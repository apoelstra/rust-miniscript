// Written in 2019 by Sanket Kanjular and Andrew Poelstra
// SPDX-License-Identifier: CC0-1.0

use bitcoin::hashes::{hash160, sha256, Hash};
use bitcoin::taproot::{ControlBlock, TAPROOT_ANNEX_PREFIX};
use bitcoin::Witness;

use super::{stack, BitcoinKey, Error, Stack};
use crate::miniscript::context::{NoChecks, ScriptContext, SigType};
use crate::prelude::*;
use crate::{BareCtx, Legacy, Miniscript, Segwitv0, Tap, ToPublicKey, Translator};

/// Attempts to parse a slice as a Bitcoin public key, checking compressedness
/// if asked to, but otherwise dropping it
fn pk_from_slice(slice: &[u8], require_compressed: bool) -> Result<bitcoin::PublicKey, Error> {
    if let Ok(pk) = bitcoin::PublicKey::from_slice(slice) {
        if require_compressed && !pk.compressed {
            Err(Error::UncompressedPubkey)
        } else {
            Ok(pk)
        }
    } else {
        Err(Error::PubkeyParseError)
    }
}

fn pk_from_stack_elem(
    elem: &stack::Element<'_>,
    require_compressed: bool,
) -> Result<bitcoin::PublicKey, Error> {
    let slice = if let stack::Element::Push(slice) = *elem {
        slice
    } else {
        return Err(Error::PubkeyParseError);
    };
    pk_from_slice(slice, require_compressed)
}

// Parse the script with appropriate context to check for context errors like
// correct usage of x-only keys or multi_a
fn script_from_stack_elem<Ctx: ScriptContext>(
    elem: &stack::Element<'_>,
) -> Result<Miniscript<Ctx::Key, Ctx>, Error> {
    match *elem {
        stack::Element::Push(sl) => {
            Miniscript::decode_consensus(bitcoin::Script::from_bytes(sl)).map_err(Error::from)
        }
        stack::Element::Satisfied => Ok(Miniscript::TRUE),
        stack::Element::Dissatisfied => Ok(Miniscript::FALSE),
    }
}

/// Helper type to indicate the origin of the bare pubkey that the interpereter uses
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum PubkeyType {
    Pk,
    Pkh,
    Wpkh,
    ShWpkh,
    Tr, // Key Spend
}

/// Helper type to indicate the origin of the bare miniscript that the interpereter uses
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum ScriptType {
    Bare,
    Sh,
    Wsh,
    ShWsh,
    Tr, // Script Spend
}

/// Structure representing a script under evaluation as a Miniscript
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub(super) enum Inner {
    /// The script being evaluated is a simple public key check (pay-to-pk,
    /// pay-to-pkhash or pay-to-witness-pkhash)
    // Technically, this allows representing a (XonlyKey, Sh) output but we make sure
    // that only appropriate outputs are created
    PublicKey(super::BitcoinKey, PubkeyType),
    /// The script being evaluated is an actual script
    Script(Miniscript<super::BitcoinKey, NoChecks>, ScriptType),
}

// The `Script` returned by this method is always generated/cloned ... when
// rust-bitcoin is updated to use a copy-on-write internal representation we
// should revisit this and return references to the actual txdata wherever
// possible
/// Parses an `Inner` and appropriate `Stack` from completed transaction data,
/// as well as the script that should be used as a scriptCode in a sighash
/// Tr outputs don't have script code and return None.
#[allow(clippy::collapsible_else_if)]
pub(super) fn from_txdata<'txin>(
    spk: &bitcoin::Script,
    script_sig: &'txin bitcoin::Script,
    witness: &'txin Witness,
) -> Result<(Inner, Stack<'txin>, Option<bitcoin::ScriptBuf>), Error> {
    let mut ssig_stack: Stack = script_sig
        .instructions_minimal()
        .map(stack::Element::from_instruction)
        .collect::<Result<Vec<stack::Element>, Error>>()?
        .into();
    let mut wit_stack: Stack = witness
        .iter()
        .map(stack::Element::from)
        .collect::<Vec<stack::Element>>()
        .into();

    // ** pay to pubkey **
    if spk.is_p2pk() {
        if !wit_stack.is_empty() {
            Err(Error::NonEmptyWitness)
        } else {
            Ok((
                Inner::PublicKey(
                    pk_from_slice(spk[1..spk.len() - 1].as_bytes(), false)?.into(),
                    PubkeyType::Pk,
                ),
                ssig_stack,
                Some(spk.to_owned()),
            ))
        }
    // ** pay to pubkeyhash **
    } else if spk.is_p2pkh() {
        if !wit_stack.is_empty() {
            Err(Error::NonEmptyWitness)
        } else {
            match ssig_stack.pop() {
                Some(elem) => {
                    let pk = pk_from_stack_elem(&elem, false)?;
                    if *spk
                        == bitcoin::ScriptBuf::new_p2pkh(&pk.to_pubkeyhash(SigType::Ecdsa).into())
                    {
                        Ok((
                            Inner::PublicKey(pk.into(), PubkeyType::Pkh),
                            ssig_stack,
                            Some(spk.to_owned()),
                        ))
                    } else {
                        Err(Error::IncorrectPubkeyHash)
                    }
                }
                None => Err(Error::UnexpectedStackEnd),
            }
        }
    // ** pay to witness pubkeyhash **
    } else if spk.is_p2wpkh() {
        if !ssig_stack.is_empty() {
            Err(Error::NonEmptyScriptSig)
        } else {
            match wit_stack.pop() {
                Some(elem) => {
                    let pk = pk_from_stack_elem(&elem, true)?;
                    let hash160 = pk.to_pubkeyhash(SigType::Ecdsa);
                    if *spk == bitcoin::ScriptBuf::new_p2wpkh(&hash160.into()) {
                        Ok((
                            Inner::PublicKey(pk.into(), PubkeyType::Wpkh),
                            wit_stack,
                            Some(bitcoin::ScriptBuf::new_p2pkh(&hash160.into())), // bip143, why..
                        ))
                    } else {
                        Err(Error::IncorrectWPubkeyHash)
                    }
                }
                None => Err(Error::UnexpectedStackEnd),
            }
        }
    // ** pay to witness scripthash **
    } else if spk.is_p2wsh() {
        if !ssig_stack.is_empty() {
            Err(Error::NonEmptyScriptSig)
        } else {
            match wit_stack.pop() {
                Some(elem) => {
                    let miniscript = script_from_stack_elem::<Segwitv0>(&elem)?;
                    let script = miniscript.encode();
                    let miniscript = miniscript.to_no_checks_ms();
                    let scripthash = sha256::Hash::hash(script.as_bytes());
                    if *spk == bitcoin::ScriptBuf::new_p2wsh(&scripthash.into()) {
                        Ok((Inner::Script(miniscript, ScriptType::Wsh), wit_stack, Some(script)))
                    } else {
                        Err(Error::IncorrectWScriptHash)
                    }
                }
                None => Err(Error::UnexpectedStackEnd),
            }
        }
    // ** pay to taproot **//
    } else if spk.is_p2tr() {
        if !ssig_stack.is_empty() {
            Err(Error::NonEmptyScriptSig)
        } else {
            let output_key = bitcoin::key::XOnlyPublicKey::from_slice(spk[2..].as_bytes())
                .map_err(|_| Error::XOnlyPublicKeyParseError)?;
            let has_annex = wit_stack
                .last()
                .and_then(|x| x.as_push().ok())
                .map(|x| !x.is_empty() && x[0] == TAPROOT_ANNEX_PREFIX)
                .unwrap_or(false);
            let has_annex = has_annex && (wit_stack.len() >= 2);
            if has_annex {
                // Annex is non-standard, bitcoin consensus rules ignore it.
                // Our sighash structure and signature verification
                // does not support annex, return error
                return Err(Error::TapAnnexUnsupported);
            }
            match wit_stack.len() {
                0 => Err(Error::UnexpectedStackEnd),
                1 => Ok((
                    Inner::PublicKey(output_key.into(), PubkeyType::Tr),
                    wit_stack,
                    None, // Tr key spend script code None
                )),
                _ => {
                    // Script spend
                    let ctrl_blk = wit_stack.pop().ok_or(Error::UnexpectedStackEnd)?;
                    let ctrl_blk = ctrl_blk.as_push()?;
                    let tap_script = wit_stack.pop().ok_or(Error::UnexpectedStackEnd)?;
                    let ctrl_blk =
                        ControlBlock::decode(ctrl_blk).map_err(Error::ControlBlockParse)?;
                    let tap_script = script_from_stack_elem::<Tap>(&tap_script)?;
                    let ms = tap_script.to_no_checks_ms();
                    // Creating new contexts is cheap
                    let secp = bitcoin::secp256k1::Secp256k1::verification_only();
                    let tap_script = tap_script.encode();
                    if ctrl_blk.verify_taproot_commitment(&secp, output_key, &tap_script) {
                        Ok((
                            Inner::Script(ms, ScriptType::Tr),
                            wit_stack,
                            // Tapscript is returned as a "scriptcode". This is a hack, but avoids adding yet
                            // another enum just for taproot, and this function is not a publicly exposed API,
                            // so it's easy enough to keep track of all uses.
                            //
                            // In particular, this return value will be put into the `script_code` member of
                            // the `Interpreter` script; the interpreter logic does the right thing with it.
                            Some(tap_script),
                        ))
                    } else {
                        Err(Error::ControlBlockVerificationError)
                    }
                }
            }
        }
    // ** pay to scripthash **
    } else if spk.is_p2sh() {
        match ssig_stack.pop() {
            Some(elem) => {
                if let stack::Element::Push(slice) = elem {
                    let scripthash = hash160::Hash::hash(slice);
                    if *spk != bitcoin::ScriptBuf::new_p2sh(&scripthash.into()) {
                        return Err(Error::IncorrectScriptHash);
                    }
                    // ** p2sh-wrapped wpkh **
                    if slice.len() == 22 && slice[0] == 0 && slice[1] == 20 {
                        return match wit_stack.pop() {
                            Some(elem) => {
                                if !ssig_stack.is_empty() {
                                    Err(Error::NonEmptyScriptSig)
                                } else {
                                    let pk = pk_from_stack_elem(&elem, true)?;
                                    let hash160 = pk.to_pubkeyhash(SigType::Ecdsa);
                                    if slice
                                        == bitcoin::ScriptBuf::new_p2wpkh(&hash160.into())
                                            .as_bytes()
                                    {
                                        Ok((
                                            Inner::PublicKey(pk.into(), PubkeyType::ShWpkh),
                                            wit_stack,
                                            Some(bitcoin::ScriptBuf::new_p2pkh(&hash160.into())), // bip143, why..
                                        ))
                                    } else {
                                        Err(Error::IncorrectWScriptHash)
                                    }
                                }
                            }
                            None => Err(Error::UnexpectedStackEnd),
                        };
                    // ** p2sh-wrapped wsh **
                    } else if slice.len() == 34 && slice[0] == 0 && slice[1] == 32 {
                        return match wit_stack.pop() {
                            Some(elem) => {
                                if !ssig_stack.is_empty() {
                                    Err(Error::NonEmptyScriptSig)
                                } else {
                                    // parse wsh with Segwitv0 context
                                    let miniscript = script_from_stack_elem::<Segwitv0>(&elem)?;
                                    let script = miniscript.encode();
                                    let miniscript = miniscript.to_no_checks_ms();
                                    let scripthash = sha256::Hash::hash(script.as_bytes());
                                    if slice
                                        == bitcoin::ScriptBuf::new_p2wsh(&scripthash.into())
                                            .as_bytes()
                                    {
                                        Ok((
                                            Inner::Script(miniscript, ScriptType::ShWsh),
                                            wit_stack,
                                            Some(script),
                                        ))
                                    } else {
                                        Err(Error::IncorrectWScriptHash)
                                    }
                                }
                            }
                            None => Err(Error::UnexpectedStackEnd),
                        };
                    }
                }
                // normal p2sh parsed in Legacy context
                let miniscript = script_from_stack_elem::<Legacy>(&elem)?;
                let script = miniscript.encode();
                let miniscript = miniscript.to_no_checks_ms();
                if wit_stack.is_empty() {
                    let scripthash = hash160::Hash::hash(script.as_bytes());
                    if *spk == bitcoin::ScriptBuf::new_p2sh(&scripthash.into()) {
                        Ok((Inner::Script(miniscript, ScriptType::Sh), ssig_stack, Some(script)))
                    } else {
                        Err(Error::IncorrectScriptHash)
                    }
                } else {
                    Err(Error::NonEmptyWitness)
                }
            }
            None => Err(Error::UnexpectedStackEnd),
        }
    // ** bare script **
    } else {
        if wit_stack.is_empty() {
            // Bare script parsed in BareCtx
            let miniscript = Miniscript::<bitcoin::PublicKey, BareCtx>::decode_consensus(spk)?;
            let miniscript = miniscript.to_no_checks_ms();
            Ok((Inner::Script(miniscript, ScriptType::Bare), ssig_stack, Some(spk.to_owned())))
        } else {
            Err(Error::NonEmptyWitness)
        }
    }
}

// Convert a miniscript from a well-defined context to a no checks context.
// We need to parse insane scripts because these scripts are obtained from already
// created transaction possibly already confirmed in a block.
// In order to avoid code duplication for various contexts related interpreter checks,
// we convert all the scripts to from a well-defined context to NoContexts.
//
// While executing Pkh(<hash>) in NoChecks, we need to pop a public key from stack
// However, NoChecks context does not know whether to parse the key as 33 bytes or 32 bytes
// While converting into NoChecks we store explicitly in TypedHash160 enum.
pub(super) trait ToNoChecks {
    fn to_no_checks_ms(&self) -> Miniscript<BitcoinKey, NoChecks>;
}

impl<Ctx: ScriptContext> ToNoChecks for Miniscript<bitcoin::PublicKey, Ctx> {
    fn to_no_checks_ms(&self) -> Miniscript<BitcoinKey, NoChecks> {
        struct TranslateFullPk;

        impl Translator<bitcoin::PublicKey> for TranslateFullPk {
            type TargetPk = BitcoinKey;
            type Error = core::convert::Infallible;

            fn pk(&mut self, pk: &bitcoin::PublicKey) -> Result<BitcoinKey, Self::Error> {
                Ok(BitcoinKey::Fullkey(*pk))
            }

            translate_hash_clone!(bitcoin::PublicKey);
        }

        self.translate_pk_ctx(&mut TranslateFullPk)
            .expect("Translation should succeed")
    }
}

impl<Ctx: ScriptContext> ToNoChecks for Miniscript<bitcoin::key::XOnlyPublicKey, Ctx> {
    fn to_no_checks_ms(&self) -> Miniscript<BitcoinKey, NoChecks> {
        struct TranslateXOnlyPk;

        impl Translator<bitcoin::key::XOnlyPublicKey> for TranslateXOnlyPk {
            type TargetPk = BitcoinKey;
            type Error = core::convert::Infallible;

            fn pk(&mut self, pk: &bitcoin::key::XOnlyPublicKey) -> Result<BitcoinKey, Self::Error> {
                Ok(BitcoinKey::XOnlyPublicKey(*pk))
            }

            translate_hash_clone!(bitcoin::key::XOnlyPublicKey);
        }
        self.translate_pk_ctx(&mut TranslateXOnlyPk)
            .expect("Translation should succeed")
    }
}

#[cfg(test)]
mod tests {

    use core::convert::TryFrom;
    use core::str::FromStr;

    use bitcoin::blockdata::script;
    use bitcoin::script::PushBytes;
    use bitcoin::ScriptBuf;
    use hex;

    use super::*;

    struct KeyTestData {
        pk_spk: bitcoin::ScriptBuf,
        pk_sig: bitcoin::ScriptBuf,
        pkh_spk: bitcoin::ScriptBuf,
        pkh_sig: bitcoin::ScriptBuf,
        pkh_sig_justkey: bitcoin::ScriptBuf,
        wpkh_spk: bitcoin::ScriptBuf,
        wpkh_stack: Witness,
        wpkh_stack_justkey: Witness,
        sh_wpkh_spk: bitcoin::ScriptBuf,
        sh_wpkh_sig: bitcoin::ScriptBuf,
        sh_wpkh_stack: Witness,
        sh_wpkh_stack_justkey: Witness,
    }

    impl KeyTestData {
        fn from_key(key: bitcoin::PublicKey) -> KeyTestData {
            // what a funny looking signature..
            let dummy_sig_vec = hex::decode_to_vec(
                "\
                302e02153b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63\
                    02153b78ce563f89a0ed9414f5aa28ad0d96d6795f9c65\
            ",
            )
            .unwrap();
            let dummy_sig = <[u8; 48]>::try_from(&dummy_sig_vec[..]).unwrap();

            let pkhash = key.to_pubkeyhash(SigType::Ecdsa).into();
            let wpkhash = key.to_pubkeyhash(SigType::Ecdsa).into();
            let wpkh_spk = bitcoin::ScriptBuf::new_p2wpkh(&wpkhash);
            let wpkh_scripthash = hash160::Hash::hash(wpkh_spk.as_bytes()).into();

            KeyTestData {
                pk_spk: bitcoin::ScriptBuf::new_p2pk(&key),
                pkh_spk: bitcoin::ScriptBuf::new_p2pkh(&pkhash),
                pk_sig: script::Builder::new().push_slice(dummy_sig).into_script(),
                pkh_sig: script::Builder::new()
                    .push_slice(dummy_sig)
                    .push_key(&key)
                    .into_script(),
                pkh_sig_justkey: script::Builder::new().push_key(&key).into_script(),
                wpkh_spk: wpkh_spk.clone(),
                wpkh_stack: Witness::from_slice(&[dummy_sig_vec.clone(), key.to_bytes()]),
                wpkh_stack_justkey: Witness::from_slice(&[key.to_bytes()]),
                sh_wpkh_spk: bitcoin::ScriptBuf::new_p2sh(&wpkh_scripthash),
                sh_wpkh_sig: script::Builder::new()
                    .push_slice(<&PushBytes>::try_from(wpkh_spk[..].as_bytes()).unwrap())
                    .into_script(),
                sh_wpkh_stack: Witness::from_slice(&[dummy_sig_vec, key.to_bytes()]),
                sh_wpkh_stack_justkey: Witness::from_slice(&[key.to_bytes()]),
            }
        }
    }

    struct FixedTestData {
        pk_comp: bitcoin::PublicKey,
        pk_uncomp: bitcoin::PublicKey,
    }

    fn fixed_test_data() -> FixedTestData {
        FixedTestData {
            pk_comp: bitcoin::PublicKey::from_str(
                "\
                025edd5cc23c51e87a497ca815d5dce0f8ab52554f849ed8995de64c5f34ce7143\
            ",
            )
            .unwrap(),
            pk_uncomp: bitcoin::PublicKey::from_str(
                "\
                045edd5cc23c51e87a497ca815d5dce0f8ab52554f849ed8995de64c5f34ce7143\
                  efae9c8dbc14130661e8cec030c89ad0c13c66c0d17a2905cdc706ab7399a868\
            ",
            )
            .unwrap(),
        }
    }

    #[test]
    fn pubkey_pk() {
        let fixed = fixed_test_data();
        let comp = KeyTestData::from_key(fixed.pk_comp);
        let uncomp = KeyTestData::from_key(fixed.pk_uncomp);
        let blank_script = bitcoin::ScriptBuf::new();
        let empty_wit = Witness::default();

        // Compressed pk, empty scriptsig
        let (inner, stack, script_code) =
            from_txdata(&comp.pk_spk, &blank_script, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp.into(), PubkeyType::Pk));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(comp.pk_spk.clone()));

        // Uncompressed pk, empty scriptsig
        let (inner, stack, script_code) =
            from_txdata(&uncomp.pk_spk, &blank_script, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_uncomp.into(), PubkeyType::Pk));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(uncomp.pk_spk.clone()));

        // Compressed pk, correct scriptsig
        let (inner, stack, script_code) =
            from_txdata(&comp.pk_spk, &comp.pk_sig, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp.into(), PubkeyType::Pk));
        assert_eq!(stack, Stack::from(vec![comp.pk_sig[1..].as_bytes().into()]));
        assert_eq!(script_code, Some(comp.pk_spk.clone()));

        // Uncompressed pk, correct scriptsig
        let (inner, stack, script_code) =
            from_txdata(&uncomp.pk_spk, &uncomp.pk_sig, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_uncomp.into(), PubkeyType::Pk));
        assert_eq!(stack, Stack::from(vec![uncomp.pk_sig[1..].as_bytes().into()]));
        assert_eq!(script_code, Some(uncomp.pk_spk));

        // Scriptpubkey has invalid key
        let mut spk = comp.pk_spk.to_bytes();
        spk[1] = 5;
        let spk = bitcoin::ScriptBuf::from(spk);
        let err = from_txdata(&spk, &bitcoin::ScriptBuf::new(), &empty_wit).unwrap_err();
        assert_eq!(err.to_string(), "could not parse pubkey");

        // Scriptpubkey has invalid script
        let mut spk = comp.pk_spk.to_bytes();
        spk[0] = 100;
        let spk = bitcoin::ScriptBuf::from(spk);
        let err = from_txdata(&spk, &bitcoin::ScriptBuf::new(), &empty_wit).unwrap_err();
        assert_eq!(&err.to_string()[0..12], "parse error:");

        // Witness is nonempty
        let wit = Witness::from_slice(&[vec![]]);
        let err = from_txdata(&comp.pk_spk, &comp.pk_sig, &wit).unwrap_err();
        assert_eq!(err.to_string(), "legacy spend had nonempty witness");
    }

    #[test]
    fn pubkey_pkh() {
        let fixed = fixed_test_data();
        let comp = KeyTestData::from_key(fixed.pk_comp);
        let uncomp = KeyTestData::from_key(fixed.pk_uncomp);
        let empty_wit = Witness::default();

        // pkh, empty scriptsig; this time it errors out
        let err = from_txdata(&comp.pkh_spk, &bitcoin::ScriptBuf::new(), &empty_wit).unwrap_err();
        assert_eq!(err.to_string(), "unexpected end of stack");

        // pkh, wrong pubkey
        let err = from_txdata(&comp.pkh_spk, &uncomp.pkh_sig_justkey, &empty_wit).unwrap_err();
        assert_eq!(err.to_string(), "public key did not match scriptpubkey");

        // pkh, right pubkey, no signature
        let (inner, stack, script_code) =
            from_txdata(&comp.pkh_spk, &comp.pkh_sig_justkey, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp.into(), PubkeyType::Pkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(comp.pkh_spk.clone()));

        let (inner, stack, script_code) =
            from_txdata(&uncomp.pkh_spk, &uncomp.pkh_sig_justkey, &empty_wit)
                .expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_uncomp.into(), PubkeyType::Pkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(uncomp.pkh_spk.clone()));

        // pkh, right pubkey, signature
        let (inner, stack, script_code) =
            from_txdata(&comp.pkh_spk, &comp.pkh_sig_justkey, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp.into(), PubkeyType::Pkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(comp.pkh_spk.clone()));

        let (inner, stack, script_code) =
            from_txdata(&uncomp.pkh_spk, &uncomp.pkh_sig_justkey, &empty_wit)
                .expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_uncomp.into(), PubkeyType::Pkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(uncomp.pkh_spk.clone()));

        // Witness is nonempty
        let wit = Witness::from_slice(&[vec![]]);
        let err = from_txdata(&comp.pkh_spk, &comp.pkh_sig, &wit).unwrap_err();
        assert_eq!(err.to_string(), "legacy spend had nonempty witness");
    }

    #[test]
    fn pubkey_wpkh() {
        let fixed = fixed_test_data();
        let comp = KeyTestData::from_key(fixed.pk_comp);
        let uncomp = KeyTestData::from_key(fixed.pk_uncomp);
        let blank_script = bitcoin::ScriptBuf::new();

        // wpkh, empty witness; this time it errors out
        let err = from_txdata(&comp.wpkh_spk, &blank_script, &Witness::default()).unwrap_err();
        assert_eq!(err.to_string(), "unexpected end of stack");

        // wpkh, uncompressed pubkey
        let err =
            from_txdata(&comp.wpkh_spk, &blank_script, &uncomp.wpkh_stack_justkey).unwrap_err();
        assert_eq!(err.to_string(), "uncompressed pubkey in non-legacy descriptor");

        // wpkh, wrong pubkey
        let err =
            from_txdata(&uncomp.wpkh_spk, &blank_script, &comp.wpkh_stack_justkey).unwrap_err();
        assert_eq!(err.to_string(), "public key did not match scriptpubkey (segwit v0)");

        // wpkh, right pubkey, no signature
        let (inner, stack, script_code) =
            from_txdata(&comp.wpkh_spk, &blank_script, &comp.wpkh_stack_justkey)
                .expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp.into(), PubkeyType::Wpkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(comp.pkh_spk.clone()));

        // wpkh, right pubkey, signature
        let (inner, stack, script_code) =
            from_txdata(&comp.wpkh_spk, &blank_script, &comp.wpkh_stack).expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp.into(), PubkeyType::Wpkh));
        assert_eq!(stack, Stack::from(vec![comp.wpkh_stack.second_to_last().unwrap().into()]));
        assert_eq!(script_code, Some(comp.pkh_spk));

        // Scriptsig is nonempty
        let err = from_txdata(&comp.wpkh_spk, &comp.pk_sig, &comp.wpkh_stack_justkey).unwrap_err();
        assert_eq!(err.to_string(), "segwit spend had nonempty scriptsig");
    }

    #[test]
    fn pubkey_sh_wpkh() {
        let fixed = fixed_test_data();
        let comp = KeyTestData::from_key(fixed.pk_comp);
        let uncomp = KeyTestData::from_key(fixed.pk_uncomp);
        let blank_script = bitcoin::ScriptBuf::new();

        // sh_wpkh, missing witness or scriptsig
        let err = from_txdata(&comp.sh_wpkh_spk, &blank_script, &Witness::default()).unwrap_err();
        assert_eq!(err.to_string(), "unexpected end of stack");
        let err =
            from_txdata(&comp.sh_wpkh_spk, &comp.sh_wpkh_sig, &Witness::default()).unwrap_err();
        assert_eq!(err.to_string(), "unexpected end of stack");
        let err = from_txdata(&comp.sh_wpkh_spk, &blank_script, &comp.sh_wpkh_stack).unwrap_err();
        assert_eq!(err.to_string(), "unexpected end of stack");

        // sh_wpkh, uncompressed pubkey
        let err =
            from_txdata(&uncomp.sh_wpkh_spk, &uncomp.sh_wpkh_sig, &uncomp.sh_wpkh_stack_justkey)
                .unwrap_err();
        assert_eq!(err.to_string(), "uncompressed pubkey in non-legacy descriptor");

        // sh_wpkh, wrong redeem script for scriptpubkey
        let err = from_txdata(&uncomp.sh_wpkh_spk, &comp.sh_wpkh_sig, &comp.sh_wpkh_stack_justkey)
            .unwrap_err();
        assert_eq!(err.to_string(), "redeem script did not match scriptpubkey",);

        // sh_wpkh, wrong redeem script for witness script
        let err =
            from_txdata(&uncomp.sh_wpkh_spk, &uncomp.sh_wpkh_sig, &comp.sh_wpkh_stack_justkey)
                .unwrap_err();
        assert_eq!(err.to_string(), "witness script did not match scriptpubkey",);

        // sh_wpkh, right pubkey, no signature
        let (inner, stack, script_code) =
            from_txdata(&comp.sh_wpkh_spk, &comp.sh_wpkh_sig, &comp.sh_wpkh_stack_justkey)
                .expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp.into(), PubkeyType::ShWpkh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(comp.pkh_spk.clone()));

        // sh_wpkh, right pubkey, signature
        let (inner, stack, script_code) =
            from_txdata(&comp.sh_wpkh_spk, &comp.sh_wpkh_sig, &comp.sh_wpkh_stack)
                .expect("parse txdata");
        assert_eq!(inner, Inner::PublicKey(fixed.pk_comp.into(), PubkeyType::ShWpkh));
        assert_eq!(stack, Stack::from(vec![comp.sh_wpkh_stack.second_to_last().unwrap().into()]));
        assert_eq!(script_code, Some(comp.pkh_spk.clone()));
    }

    fn ms_inner_script(ms: &str) -> (Miniscript<BitcoinKey, NoChecks>, bitcoin::ScriptBuf) {
        let ms = Miniscript::<bitcoin::PublicKey, Segwitv0>::from_str_insane(ms).unwrap();
        let spk = ms.encode();
        let miniscript = ms.to_no_checks_ms();
        (miniscript, spk)
    }

    #[test]
    fn script_bare() {
        let preimage = b"12345678----____12345678----____";
        let hash = hash160::Hash::hash(&preimage[..]);
        let blank_script = bitcoin::ScriptBuf::new();
        let empty_wit = Witness::default();
        let (miniscript, spk) = ms_inner_script(&format!("hash160({})", hash));

        // bare script has no validity requirements beyond being a sane script
        let (inner, stack, script_code) =
            from_txdata(&spk, &blank_script, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::Script(miniscript, ScriptType::Bare));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(spk.clone()));

        let err = from_txdata(&blank_script, &blank_script, &empty_wit).unwrap_err();
        assert_eq!(&err.to_string()[0..12], "parse error:");

        // nonempty witness
        let wit = Witness::from_slice(&[vec![]]);
        let err = from_txdata(&spk, &blank_script, &wit).unwrap_err();
        assert_eq!(&err.to_string(), "legacy spend had nonempty witness");
    }

    #[test]
    fn script_sh() {
        let preimage = b"12345678----____12345678----____";
        let hash = hash160::Hash::hash(&preimage[..]);

        let (miniscript, redeem_script) = ms_inner_script(&format!("hash160({})", hash));
        let rs_hash = hash160::Hash::hash(redeem_script.as_bytes()).into();

        let spk = ScriptBuf::new_p2sh(&rs_hash);
        let script_sig = script::Builder::new()
            .push_slice(<&PushBytes>::try_from(redeem_script.as_bytes()).unwrap())
            .into_script();
        let blank_script = bitcoin::ScriptBuf::new();
        let empty_wit = Witness::default();

        // sh without scriptsig
        let err = from_txdata(&spk, &blank_script, &Witness::default()).unwrap_err();
        assert_eq!(&err.to_string(), "unexpected end of stack");

        // with incorrect scriptsig
        let err = from_txdata(&spk, &spk, &Witness::default()).unwrap_err();
        assert_eq!(&err.to_string(), "expected push in script");

        // with correct scriptsig
        let (inner, stack, script_code) =
            from_txdata(&spk, &script_sig, &empty_wit).expect("parse txdata");
        assert_eq!(inner, Inner::Script(miniscript, ScriptType::Sh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(redeem_script));

        // nonempty witness
        let wit = Witness::from_slice(&[vec![]]);
        let err = from_txdata(&spk, &script_sig, &wit).unwrap_err();
        assert_eq!(&err.to_string(), "legacy spend had nonempty witness");
    }

    #[test]
    fn script_wsh() {
        let preimage = b"12345678----____12345678----____";
        let hash = hash160::Hash::hash(&preimage[..]);
        let (miniscript, witness_script) = ms_inner_script(&format!("hash160({})", hash));
        let wit_hash = sha256::Hash::hash(witness_script.as_bytes()).into();
        let wit_stack = Witness::from_slice(&[witness_script.to_bytes()]);

        let spk = ScriptBuf::new_p2wsh(&wit_hash);
        let blank_script = bitcoin::ScriptBuf::new();

        // wsh without witness
        let err = from_txdata(&spk, &blank_script, &Witness::default()).unwrap_err();
        assert_eq!(&err.to_string(), "unexpected end of stack");

        // with incorrect witness
        let wit = Witness::from_slice(&[spk.to_bytes()]);
        let err = from_txdata(&spk, &blank_script, &wit).unwrap_err();
        assert_eq!(&err.to_string()[0..12], "parse error:");

        // with correct witness
        let (inner, stack, script_code) =
            from_txdata(&spk, &blank_script, &wit_stack).expect("parse txdata");
        assert_eq!(inner, Inner::Script(miniscript, ScriptType::Wsh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(witness_script.clone()));

        // nonempty script_sig
        let script_sig = script::Builder::new()
            .push_slice(<&PushBytes>::try_from(witness_script.as_bytes()).unwrap())
            .into_script();
        let err = from_txdata(&spk, &script_sig, &wit_stack).unwrap_err();
        assert_eq!(&err.to_string(), "segwit spend had nonempty scriptsig");
    }

    #[test]
    fn script_sh_wsh() {
        let preimage = b"12345678----____12345678----____";
        let hash = hash160::Hash::hash(&preimage[..]);
        let (miniscript, witness_script) = ms_inner_script(&format!("hash160({})", hash));
        let wit_hash = sha256::Hash::hash(witness_script.as_bytes()).into();
        let wit_stack = Witness::from_slice(&[witness_script.to_bytes()]);

        let redeem_script = ScriptBuf::new_p2wsh(&wit_hash);
        let script_sig = script::Builder::new()
            .push_slice(<&PushBytes>::try_from(redeem_script.as_bytes()).unwrap())
            .into_script();
        let blank_script = bitcoin::ScriptBuf::new();

        let rs_hash = hash160::Hash::hash(redeem_script.as_bytes()).into();
        let spk = ScriptBuf::new_p2sh(&rs_hash);

        // shwsh without witness or scriptsig
        let err = from_txdata(&spk, &blank_script, &Witness::default()).unwrap_err();
        assert_eq!(&err.to_string(), "unexpected end of stack");
        let err = from_txdata(&spk, &script_sig, &Witness::default()).unwrap_err();
        assert_eq!(&err.to_string(), "unexpected end of stack");
        let err = from_txdata(&spk, &blank_script, &wit_stack).unwrap_err();
        assert_eq!(&err.to_string(), "unexpected end of stack");

        // with incorrect witness
        let wit = Witness::from_slice(&[spk.to_bytes()]);
        let err = from_txdata(&spk, &script_sig, &wit).unwrap_err();
        assert_eq!(&err.to_string()[0..12], "parse error:");

        // with incorrect scriptsig
        let err = from_txdata(&spk, &redeem_script, &wit_stack).unwrap_err();
        assert_eq!(&err.to_string(), "redeem script did not match scriptpubkey");

        // with correct witness
        let (inner, stack, script_code) =
            from_txdata(&spk, &script_sig, &wit_stack).expect("parse txdata");
        assert_eq!(inner, Inner::Script(miniscript, ScriptType::ShWsh));
        assert_eq!(stack, Stack::from(vec![]));
        assert_eq!(script_code, Some(witness_script));
    }
}
