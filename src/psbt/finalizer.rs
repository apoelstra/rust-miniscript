// Miniscript
// Written in 2020 by
//     Sanket Kanjalkar <sanket1729@gmail.com>
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

//! # Partially-Signed Bitcoin Transactions
//!
//! This module implements the Finalizer and Extractor roles defined in
//! BIP 174, PSBT, described at
//! `https://github.com/bitcoin/bips/blob/master/bip-0174.mediawiki`
//!

use bitcoin::util::sighash::Prevouts;
use util::{script_is_v1_tr, witness_size};

use super::{sanity_check, Psbt};
use super::{Error, InputError, PsbtInputSatisfier};
use bitcoin::blockdata::witness::Witness;
use bitcoin::secp256k1::{self, Secp256k1};
use bitcoin::util::key::XOnlyPublicKey;
use bitcoin::util::taproot::LeafVersion;
use bitcoin::{self, EcdsaSigHashType, PublicKey, Script};
use descriptor::DescriptorTrait;
use interpreter;
use Descriptor;
use Miniscript;
use Satisfier;
use {BareCtx, Legacy, Segwitv0, Tap};

// Satisfy the taproot descriptor. It is not possible to infer the complete
// descriptor from psbt because the information about all the scripts might not
// be present. Also, currently the spec does not support hidden branches, so
// inferring a descriptor is not possible
fn construct_tap_witness(
    spk: &Script,
    sat: &PsbtInputSatisfier,
    allow_mall: bool,
) -> Result<Vec<Vec<u8>>, InputError> {
    assert!(script_is_v1_tr(&spk));

    // try the script spend path first
    if let Some(sig) =
        <PsbtInputSatisfier as Satisfier<XOnlyPublicKey>>::lookup_tap_key_spend_sig(sat)
    {
        return Ok(vec![sig.to_vec()]);
    }
    // Next script spends
    let (mut min_wit, mut min_wit_len) = (None, None);
    if let Some(block_map) =
        <PsbtInputSatisfier as Satisfier<XOnlyPublicKey>>::lookup_tap_control_block_map(sat)
    {
        for (control_block, (script, ver)) in block_map {
            if *ver != LeafVersion::TapScript {
                // We don't know how to satisfy non default version scripts yet
                continue;
            }
            let ms = match Miniscript::<XOnlyPublicKey, Tap>::parse_insane(script) {
                Ok(ms) => ms,
                Err(..) => continue, // try another script
            };
            let mut wit = if allow_mall {
                match ms.satisfy_malleable(sat) {
                    Ok(ms) => ms,
                    Err(..) => continue,
                }
            } else {
                match ms.satisfy(sat) {
                    Ok(ms) => ms,
                    Err(..) => continue,
                }
            };
            wit.push(ms.encode().into_bytes());
            wit.push(control_block.serialize());
            let wit_len = Some(witness_size(&wit));
            if min_wit_len.is_some() && wit_len > min_wit_len {
                continue;
            } else {
                // store the minimum
                min_wit = Some(wit);
                min_wit_len = wit_len;
            }
        }
        min_wit.ok_or(InputError::CouldNotSatisfyTr)
    } else {
        // No control blocks found
        Err(InputError::CouldNotSatisfyTr)
    }
}

// Get the scriptpubkey for the psbt input
fn get_scriptpubkey(psbt: &Psbt, index: usize) -> Result<&Script, InputError> {
    get_utxo(psbt, index).map(|utxo| &utxo.script_pubkey)
}

// Get the spending utxo for this psbt input
fn get_utxo(psbt: &Psbt, index: usize) -> Result<&bitcoin::TxOut, InputError> {
    let inp = &psbt.inputs[index];
    let utxo = if let Some(ref witness_utxo) = inp.witness_utxo {
        &witness_utxo
    } else if let Some(ref non_witness_utxo) = inp.non_witness_utxo {
        let vout = psbt.unsigned_tx.input[index].previous_output.vout;
        &non_witness_utxo.output[vout as usize]
    } else {
        return Err(InputError::MissingUtxo);
    };
    Ok(utxo)
}

/// Get the Prevouts for the psbt
fn prevouts<'a>(psbt: &'a Psbt) -> Result<Vec<bitcoin::TxOut>, super::Error> {
    let mut utxos = vec![];
    for i in 0..psbt.inputs.len() {
        let utxo_ref = get_utxo(psbt, i).map_err(|e| Error::InputError(e, i))?;
        utxos.push(utxo_ref.clone()); // RC fix would allow references here instead of clone
    }
    Ok(utxos)
}

// Create a descriptor from unfinalized PSBT input.
// Panics on out of bound input index for psbt
// Also sanity checks that the witness script and
// redeem script are consistent with the script pubkey.
// Does *not* check signatures
// We parse the insane version while satisfying because
// we want to move the script is probably already created
// and we want to satisfy it in any way possible.
fn get_descriptor(psbt: &Psbt, index: usize) -> Result<Descriptor<PublicKey>, InputError> {
    // Figure out Scriptpubkey
    let script_pubkey = get_scriptpubkey(psbt, index)?;
    let inp = &psbt.inputs[index];
    // 1. `PK`: creates a `Pk` descriptor(does not check if partial sig is given)
    if script_pubkey.is_p2pk() {
        let script_pubkey_len = script_pubkey.len();
        let pk_bytes = &script_pubkey.to_bytes();
        match bitcoin::PublicKey::from_slice(&pk_bytes[1..script_pubkey_len - 1]) {
            Ok(pk) => Ok(Descriptor::new_pk(pk)),
            Err(e) => Err(InputError::from(e)),
        }
    } else if script_pubkey.is_p2pkh() {
        // 2. `Pkh`: creates a `PkH` descriptor if partial_sigs has the corresponding pk
        let partial_sig_contains_pk = inp
            .partial_sigs
            .iter()
            .filter(|&(&pk, _sig)| {
                // Indirect way to check the equivalence of pubkey-hashes.
                // Create a pubkey hash and check if they are the same.
                // THIS IS A BUG AND *WILL* PRODUCE WRONG SATISFACTIONS FOR UNCOMPRESSED KEYS
                // Partial sigs loses the compressed flag that is necessary
                // TODO: See https://github.com/rust-bitcoin/rust-bitcoin/pull/836
                // The type checker will fail again after we update to 0.28 and this can be removed
                let pk = bitcoin::PublicKey::new(pk);
                let addr = bitcoin::Address::p2pkh(&pk, bitcoin::Network::Bitcoin);
                *script_pubkey == addr.script_pubkey()
            })
            .next();
        match partial_sig_contains_pk {
            Some((pk, _sig)) => Ok(Descriptor::new_pkh(bitcoin::PublicKey::new(*pk))),
            None => Err(InputError::MissingPubkey),
        }
    } else if script_pubkey.is_v0_p2wpkh() {
        // 3. `Wpkh`: creates a `wpkh` descriptor if the partial sig has corresponding pk.
        let partial_sig_contains_pk = inp
            .partial_sigs
            .iter()
            .filter(|&(&pk, _sig)| {
                // Indirect way to check the equivalence of pubkey-hashes.
                // Create a pubkey hash and check if they are the same.
                let pk = bitcoin::PublicKey::new(pk);
                let addr = bitcoin::Address::p2wpkh(&pk, bitcoin::Network::Bitcoin)
                    .expect("Address corresponding to valid pubkey");
                *script_pubkey == addr.script_pubkey()
            })
            .next();
        match partial_sig_contains_pk {
            Some((pk, _sig)) => Ok(Descriptor::new_wpkh(bitcoin::PublicKey::new(*pk))?),
            None => Err(InputError::MissingPubkey),
        }
    } else if script_pubkey.is_v0_p2wsh() {
        // 4. `Wsh`: creates a `Wsh` descriptor
        if inp.redeem_script.is_some() {
            return Err(InputError::NonEmptyRedeemScript);
        }
        if let Some(ref witness_script) = inp.witness_script {
            if witness_script.to_v0_p2wsh() != *script_pubkey {
                return Err(InputError::InvalidWitnessScript {
                    witness_script: witness_script.clone(),
                    p2wsh_expected: script_pubkey.clone(),
                });
            }
            let ms = Miniscript::<bitcoin::PublicKey, Segwitv0>::parse_insane(witness_script)?;
            Ok(Descriptor::new_wsh(ms)?)
        } else {
            Err(InputError::MissingWitnessScript)
        }
    } else if script_pubkey.is_p2sh() {
        match &inp.redeem_script {
            &None => return Err(InputError::MissingRedeemScript),
            &Some(ref redeem_script) => {
                if redeem_script.to_p2sh() != *script_pubkey {
                    return Err(InputError::InvalidRedeemScript {
                        redeem: redeem_script.clone(),
                        p2sh_expected: script_pubkey.clone(),
                    });
                }
                if redeem_script.is_v0_p2wsh() {
                    // 5. `ShWsh` case
                    if let Some(ref witness_script) = inp.witness_script {
                        if witness_script.to_v0_p2wsh() != *redeem_script {
                            return Err(InputError::InvalidWitnessScript {
                                witness_script: witness_script.clone(),
                                p2wsh_expected: redeem_script.clone(),
                            });
                        }
                        let ms = Miniscript::<bitcoin::PublicKey, Segwitv0>::parse_insane(
                            witness_script,
                        )?;
                        Ok(Descriptor::new_sh_wsh(ms)?)
                    } else {
                        Err(InputError::MissingWitnessScript)
                    }
                } else if redeem_script.is_v0_p2wpkh() {
                    // 6. `ShWpkh` case
                    let partial_sig_contains_pk = inp
                        .partial_sigs
                        .iter()
                        .filter(|&(&pk, _sig)| {
                            let pk = bitcoin::PublicKey::new(pk);
                            let addr = bitcoin::Address::p2wpkh(&pk, bitcoin::Network::Bitcoin)
                                .expect("Address corresponding to valid pubkey");
                            *script_pubkey == addr.script_pubkey()
                        })
                        .next();
                    match partial_sig_contains_pk {
                        Some((pk, _sig)) => {
                            Ok(Descriptor::new_sh_wpkh(bitcoin::PublicKey::new(*pk))?)
                        }
                        None => Err(InputError::MissingPubkey),
                    }
                } else {
                    //7. regular p2sh
                    if inp.witness_script.is_some() {
                        return Err(InputError::NonEmptyWitnessScript);
                    }
                    if let Some(ref redeem_script) = inp.redeem_script {
                        let ms =
                            Miniscript::<bitcoin::PublicKey, Legacy>::parse_insane(redeem_script)?;
                        Ok(Descriptor::new_sh(ms)?)
                    } else {
                        Err(InputError::MissingWitnessScript)
                    }
                }
            }
        }
    } else {
        // 8. Bare case
        if inp.witness_script.is_some() {
            return Err(InputError::NonEmptyWitnessScript);
        }
        if inp.redeem_script.is_some() {
            return Err(InputError::NonEmptyRedeemScript);
        }
        let ms = Miniscript::<bitcoin::PublicKey, BareCtx>::parse_insane(script_pubkey)?;
        Ok(Descriptor::new_bare(ms)?)
    }
}

/// Interprets all psbt inputs and checks whether the
/// script is correctly interpreted according to the context
/// The psbt must have included final script sig and final witness.
/// In other words, this checks whether the finalized psbt interprets
/// correctly
pub fn interpreter_check<C: secp256k1::Verification>(
    psbt: &Psbt,
    secp: &Secp256k1<C>,
) -> Result<(), Error> {
    let utxos = prevouts(&psbt)?;
    let utxos = &Prevouts::All(&utxos);
    for (index, input) in psbt.inputs.iter().enumerate() {
        let spk = get_scriptpubkey(psbt, index).map_err(|e| Error::InputError(e, index))?;
        let empty_script_sig = Script::new();
        let empty_witness = Witness::default();
        let script_sig = input.final_script_sig.as_ref().unwrap_or(&empty_script_sig);
        let witness = input
            .final_script_witness
            .as_ref()
            .map(|wit_slice| Witness::from_vec(wit_slice.to_vec())) // TODO: Update rust-bitcoin psbt API to use witness
            .unwrap_or(empty_witness);

        // Now look at all the satisfied constraints. If everything is filled in
        // corrected, there should be no errors
        // Interpreter check
        {
            let cltv = psbt.unsigned_tx.lock_time;
            let csv = psbt.unsigned_tx.input[index].sequence;
            let interpreter =
                interpreter::Interpreter::from_txdata(spk, &script_sig, &witness, cltv, csv)
                    .map_err(|e| Error::InputError(InputError::Interpreter(e), index))?;
            let iter = interpreter.iter(secp, &psbt.unsigned_tx, index, &utxos);
            if let Some(error) = iter.filter_map(Result::err).next() {
                return Err(Error::InputError(InputError::Interpreter(error), index));
            };
        }
    }
    Ok(())
}

/// Finalize the psbt. This function takes in a mutable reference to psbt
/// and populates the final_witness and final_scriptsig
/// of the psbt assuming all of the inputs are miniscript as per BIP174.
/// If any of the inputs is not miniscript, this returns a parsing error
/// For satisfaction of individual inputs, use the satisfy API.
/// This function also performs a sanity interpreter check on the
/// finalized psbt which involves checking the signatures/ preimages/timelocks.
/// The functions fails it is not possible to satisfy any of the inputs non-malleably
/// See [finalize_mall] if you want to allow malleable satisfactions
pub fn finalize<C: secp256k1::Verification>(
    psbt: &mut Psbt,
    secp: &Secp256k1<C>,
) -> Result<(), super::Error> {
    finalize_helper(psbt, secp, false)
}

/// Same as [finalize], but allows for malleable satisfactions
pub fn finalize_mall<C: secp256k1::Verification>(
    psbt: &mut Psbt,
    secp: &Secp256k1<C>,
) -> Result<(), super::Error> {
    finalize_helper(psbt, secp, true)
}

pub fn finalize_helper<C: secp256k1::Verification>(
    psbt: &mut Psbt,
    secp: &Secp256k1<C>,
    allow_mall: bool,
) -> Result<(), super::Error> {
    sanity_check(psbt)?;

    // Check well-formedness of input data
    for (n, input) in psbt.inputs.iter().enumerate() {
        // TODO: fix this after https://github.com/rust-bitcoin/rust-bitcoin/issues/838
        let target_ecdsa_sighash_ty = match input.sighash_type {
            Some(psbt_hash_ty) => psbt_hash_ty
                .ecdsa_hash_ty()
                .map_err(|e| Error::InputError(InputError::NonStandardSigHashType(e), n))?,
            None => EcdsaSigHashType::All,
        };
        for (key, ecdsa_sig) in &input.partial_sigs {
            let flag = bitcoin::EcdsaSigHashType::from_u32_standard(ecdsa_sig.hash_ty as u32)
                .map_err(|_| {
                    super::Error::InputError(
                        InputError::Interpreter(interpreter::Error::NonStandardSigHash(
                            ecdsa_sig.to_vec(),
                        )),
                        n,
                    )
                })?;
            if target_ecdsa_sighash_ty != flag {
                return Err(Error::InputError(
                    InputError::WrongSigHashFlag {
                        required: target_ecdsa_sighash_ty,
                        got: flag,
                        pubkey: bitcoin::PublicKey::new(*key),
                    },
                    n,
                ));
            }
            // Signatures are well-formed in psbt partial sigs
        }
    }

    // Actually construct the witnesses
    for index in 0..psbt.inputs.len() {
        let (witness, script_sig) = {
            let spk = get_scriptpubkey(psbt, index).map_err(|e| Error::InputError(e, index))?;
            let sat = PsbtInputSatisfier::new(&psbt, index);

            if script_is_v1_tr(spk) {
                // Deal with tr case separately, unfortunately we cannot infer the full descriptor for Tr
                let wit = construct_tap_witness(spk, &sat, allow_mall)
                    .map_err(|e| Error::InputError(e, index))?;
                (wit, Script::new())
            } else {
                // Get a descriptor for this input.
                let desc = get_descriptor(&psbt, index).map_err(|e| Error::InputError(e, index))?;

                //generate the satisfaction witness and scriptsig
                if !allow_mall {
                    desc.get_satisfaction(PsbtInputSatisfier::new(&psbt, index))
                } else {
                    desc.get_satisfaction_mall(PsbtInputSatisfier::new(&psbt, index))
                }
                .map_err(|e| Error::InputError(InputError::MiniscriptError(e), index))?
            }
        };

        let input = &mut psbt.inputs[index];
        //Fill in the satisfactions
        input.final_script_sig = if script_sig.is_empty() {
            None
        } else {
            Some(script_sig)
        };
        input.final_script_witness = if witness.is_empty() {
            None
        } else {
            Some(bitcoin::Witness::from_vec(witness))
        };
        //reset everything
        input.partial_sigs.clear(); // 0x02
        input.sighash_type = None; // 0x03
        input.redeem_script = None; // 0x04
        input.witness_script = None; // 0x05
        input.bip32_derivation.clear(); // 0x05
                                        // finalized witness 0x06 and 0x07 are not clear
                                        // 0x09 Proof of reserves not yet supported
        input.ripemd160_preimages.clear(); // 0x0a
        input.sha256_preimages.clear(); // 0x0b
        input.hash160_preimages.clear(); // 0x0c
        input.hash256_preimages.clear(); // 0x0d
                                         // psbt v2 fields till 0x012 not supported
        input.tap_key_sig = None; // 0x013
        input.tap_script_sigs.clear(); // 0x014
        input.tap_scripts.clear(); // 0x015
        input.tap_key_origins.clear(); // 0x16
        input.tap_internal_key = None; // x017
        input.tap_merkle_root = None; // 0x018
    }
    // Double check everything with the interpreter
    // This only checks whether the script will be executed
    // correctly by the bitcoin interpreter under the current
    // psbt context.
    interpreter_check(&psbt, secp)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use bitcoin::consensus::encode::deserialize;
    use bitcoin::hashes::hex::FromHex;

    #[test]
    fn tests_from_bip174() {
        let mut psbt: bitcoin::util::psbt::PartiallySignedTransaction = deserialize(&Vec::<u8>::from_hex("70736274ff01009a020000000258e87a21b56daf0c23be8e7070456c336f7cbaa5c8757924f545887bb2abdd750000000000ffffffff838d0427d0ec650a68aa46bb0b098aea4422c071b2ca78352a077959d07cea1d0100000000ffffffff0270aaf00800000000160014d85c2b71d0060b09c9886aeb815e50991dda124d00e1f5050000000016001400aea9a2e5f0f876a588df5546e8742d1d87008f00000000000100bb0200000001aad73931018bd25f84ae400b68848be09db706eac2ac18298babee71ab656f8b0000000048473044022058f6fc7c6a33e1b31548d481c826c015bd30135aad42cd67790dab66d2ad243b02204a1ced2604c6735b6393e5b41691dd78b00f0c5942fb9f751856faa938157dba01feffffff0280f0fa020000000017a9140fb9463421696b82c833af241c78c17ddbde493487d0f20a270100000017a91429ca74f8a08f81999428185c97b5d852e4063f6187650000002202029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f473044022074018ad4180097b873323c0015720b3684cc8123891048e7dbcd9b55ad679c99022073d369b740e3eb53dcefa33823c8070514ca55a7dd9544f157c167913261118c01220202dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d7483045022100f61038b308dc1da865a34852746f015772934208c6d24454393cd99bdf2217770220056e675a675a6d0a02b85b14e5e29074d8a25a9b5760bea2816f661910a006ea01010304010000000104475221029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f2102dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d752ae2206029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f10d90c6a4f000000800000008000000080220602dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d710d90c6a4f0000008000000080010000800001012000c2eb0b0000000017a914b7f5faf40e3d40a5a459b1db3535f2b72fa921e887220203089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc473044022062eb7a556107a7c73f45ac4ab5a1dddf6f7075fb1275969a7f383efff784bcb202200c05dbb7470dbf2f08557dd356c7325c1ed30913e996cd3840945db12228da5f012202023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e73473044022065f45ba5998b59a27ffe1a7bed016af1f1f90d54b3aa8f7450aa5f56a25103bd02207f724703ad1edb96680b284b56d4ffcb88f7fb759eabbe08aa30f29b851383d2010103040100000001042200208c2353173743b595dfb4a07b72ba8e42e3797da74e87fe7d9d7497e3b2028903010547522103089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc21023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e7352ae2206023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e7310d90c6a4f000000800000008003000080220603089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc10d90c6a4f00000080000000800200008000220203a9a4c37f5996d3aa25dbac6b570af0650394492942460b354753ed9eeca5877110d90c6a4f000000800000008004000080002202027f6399757d2eff55a136ad02c684b1838b6556e5f1b6b34282a94b6b5005109610d90c6a4f00000080000000800500008000").unwrap()).unwrap();

        let secp = Secp256k1::verification_only();
        finalize(&mut psbt, &secp).unwrap();

        let expected: bitcoin::util::psbt::PartiallySignedTransaction = deserialize(&Vec::<u8>::from_hex("70736274ff01009a020000000258e87a21b56daf0c23be8e7070456c336f7cbaa5c8757924f545887bb2abdd750000000000ffffffff838d0427d0ec650a68aa46bb0b098aea4422c071b2ca78352a077959d07cea1d0100000000ffffffff0270aaf00800000000160014d85c2b71d0060b09c9886aeb815e50991dda124d00e1f5050000000016001400aea9a2e5f0f876a588df5546e8742d1d87008f00000000000100bb0200000001aad73931018bd25f84ae400b68848be09db706eac2ac18298babee71ab656f8b0000000048473044022058f6fc7c6a33e1b31548d481c826c015bd30135aad42cd67790dab66d2ad243b02204a1ced2604c6735b6393e5b41691dd78b00f0c5942fb9f751856faa938157dba01feffffff0280f0fa020000000017a9140fb9463421696b82c833af241c78c17ddbde493487d0f20a270100000017a91429ca74f8a08f81999428185c97b5d852e4063f6187650000000107da00473044022074018ad4180097b873323c0015720b3684cc8123891048e7dbcd9b55ad679c99022073d369b740e3eb53dcefa33823c8070514ca55a7dd9544f157c167913261118c01483045022100f61038b308dc1da865a34852746f015772934208c6d24454393cd99bdf2217770220056e675a675a6d0a02b85b14e5e29074d8a25a9b5760bea2816f661910a006ea01475221029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f2102dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d752ae0001012000c2eb0b0000000017a914b7f5faf40e3d40a5a459b1db3535f2b72fa921e8870107232200208c2353173743b595dfb4a07b72ba8e42e3797da74e87fe7d9d7497e3b20289030108da0400473044022062eb7a556107a7c73f45ac4ab5a1dddf6f7075fb1275969a7f383efff784bcb202200c05dbb7470dbf2f08557dd356c7325c1ed30913e996cd3840945db12228da5f01473044022065f45ba5998b59a27ffe1a7bed016af1f1f90d54b3aa8f7450aa5f56a25103bd02207f724703ad1edb96680b284b56d4ffcb88f7fb759eabbe08aa30f29b851383d20147522103089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc21023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e7352ae00220203a9a4c37f5996d3aa25dbac6b570af0650394492942460b354753ed9eeca5877110d90c6a4f000000800000008004000080002202027f6399757d2eff55a136ad02c684b1838b6556e5f1b6b34282a94b6b5005109610d90c6a4f00000080000000800500008000").unwrap()).unwrap();
        assert_eq!(psbt, expected);
    }
}
