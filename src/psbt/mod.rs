// Miniscript
// Written in 2019 by
//     Andrew Poelstra <apoelstra@wpsoftware.net>
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

use std::collections::BTreeMap;
use std::{error, fmt};

use bitcoin;
use bitcoin::hashes::{hash160, ripemd160, sha256, sha256d};
use bitcoin::secp256k1::{self, Secp256k1};
use bitcoin::util::psbt::PartiallySignedTransaction as Psbt;
use bitcoin::Script;

use bitcoin::util::taproot::{ControlBlock, LeafVersion, TapLeafHash};
use interpreter;
use miniscript::limits::SEQUENCE_LOCKTIME_DISABLE_FLAG;
use miniscript::satisfy::{After, Older};
use Preimage32;
use Satisfier;
use {MiniscriptKey, ToPublicKey};

mod finalizer;
pub use self::finalizer::{finalize, finalize_mall, interpreter_check};

/// Error type for Pbst Input
#[derive(Debug)]
pub enum InputError {
    /// Get the secp Errors directly
    SecpErr(bitcoin::secp256k1::Error),
    /// Key errors
    KeyErr(bitcoin::util::key::Error),
    /// Could not satisfy taproot descriptor
    /// This error is returned when both script path and key paths could not be
    /// satisfied. We cannot return a detailed error because we try all miniscripts
    /// in script spend path, we cannot know which miniscript failed.
    CouldNotSatisfyTr,
    /// Error doing an interpreter-check on a finalized psbt
    Interpreter(interpreter::Error),
    /// Redeem script does not match the p2sh hash
    InvalidRedeemScript {
        /// Redeem script
        redeem: Script,
        /// Expected p2sh Script
        p2sh_expected: Script,
    },
    /// Witness script does not match the p2wsh hash
    InvalidWitnessScript {
        /// Witness Script
        witness_script: Script,
        /// Expected p2wsh script
        p2wsh_expected: Script,
    },
    /// Invalid sig
    InvalidSignature {
        /// The bitcoin public key
        pubkey: bitcoin::PublicKey,
        /// The (incorrect) signature
        sig: Vec<u8>,
    },
    /// Pass through the underlying errors in miniscript
    MiniscriptError(super::Error),
    /// Missing redeem script for p2sh
    MissingRedeemScript,
    /// Missing witness
    MissingWitness,
    /// used for public key corresponding to pkh/wpkh
    MissingPubkey,
    /// Missing witness script for segwit descriptors
    MissingWitnessScript,
    ///Missing both the witness and non-witness utxo
    MissingUtxo,
    /// Non empty Witness script for p2sh
    NonEmptyWitnessScript,
    /// Non empty Redeem script
    NonEmptyRedeemScript,
    /// Non Standard sighash type
    NonStandardSigHashType(bitcoin::blockdata::transaction::NonStandardSigHashType),
    /// Sighash did not match
    WrongSigHashFlag {
        /// required sighash type
        required: bitcoin::EcdsaSigHashType,
        /// the sighash type we got
        got: bitcoin::EcdsaSigHashType,
        /// the corresponding publickey
        pubkey: bitcoin::PublicKey,
    },
}

/// Error type for entire Psbt
#[derive(Debug)]
pub enum Error {
    /// Input Error type
    InputError(InputError, usize),
    /// Wrong Input Count
    WrongInputCount {
        /// Input count in tx
        in_tx: usize,
        /// Input count in psbt
        in_map: usize,
    },
}

impl fmt::Display for InputError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            InputError::InvalidSignature {
                ref pubkey,
                ref sig,
            } => write!(f, "PSBT: bad signature {} for key {:?}", pubkey, sig),
            InputError::KeyErr(ref e) => write!(f, "Key Err: {}", e),
            InputError::Interpreter(ref e) => write!(f, "Interpreter: {}", e),
            InputError::SecpErr(ref e) => write!(f, "Secp Err: {}", e),
            InputError::InvalidRedeemScript {
                ref redeem,
                ref p2sh_expected,
            } => write!(
                f,
                "Redeem script {} does not match the p2sh script {}",
                redeem, p2sh_expected
            ),
            InputError::InvalidWitnessScript {
                ref witness_script,
                ref p2wsh_expected,
            } => write!(
                f,
                "Witness script {} does not match the p2wsh script {}",
                witness_script, p2wsh_expected
            ),
            InputError::MiniscriptError(ref e) => write!(f, "Miniscript Error: {}", e),
            InputError::MissingWitness => write!(f, "PSBT is missing witness"),
            InputError::MissingRedeemScript => write!(f, "PSBT is Redeem script"),
            InputError::MissingUtxo => {
                write!(f, "PSBT is missing both witness and non-witness UTXO")
            }
            InputError::MissingWitnessScript => write!(f, "PSBT is missing witness script"),
            InputError::MissingPubkey => write!(f, "Missing pubkey for a pkh/wpkh"),
            InputError::NonEmptyRedeemScript => write!(
                f,
                "PSBT has non-empty redeem script at for legacy transactions"
            ),
            InputError::NonEmptyWitnessScript => {
                write!(f, "PSBT has non-empty witness script at for legacy input")
            }
            InputError::WrongSigHashFlag {
                required,
                got,
                pubkey,
            } => write!(
                f,
                "PSBT: signature with key {:?} had \
                 sighashflag {:?} rather than required {:?}",
                pubkey, got, required
            ),
            InputError::CouldNotSatisfyTr => {
                write!(f, "Could not satisfy Tr descriptor")
            }
            InputError::NonStandardSigHashType(e) => write!(f, "Non-standard sighash type {}", e),
        }
    }
}

#[doc(hidden)]
impl From<super::Error> for InputError {
    fn from(e: super::Error) -> InputError {
        InputError::MiniscriptError(e)
    }
}

#[doc(hidden)]
impl From<bitcoin::secp256k1::Error> for InputError {
    fn from(e: bitcoin::secp256k1::Error) -> InputError {
        InputError::SecpErr(e)
    }
}

#[doc(hidden)]
impl From<bitcoin::util::key::Error> for InputError {
    fn from(e: bitcoin::util::key::Error) -> InputError {
        InputError::KeyErr(e)
    }
}

impl error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::InputError(ref inp_err, index) => write!(f, "{} at index {}", inp_err, index),
            Error::WrongInputCount { in_tx, in_map } => write!(
                f,
                "PSBT had {} inputs in transaction but {} inputs in map",
                in_tx, in_map
            ),
        }
    }
}

/// Psbt satisfier for at inputs at a particular index
/// Takes in &psbt because multiple inputs will share
/// the same psbt structure
/// All operations on this structure will panic if index
/// is more than number of inputs in pbst
pub struct PsbtInputSatisfier<'psbt> {
    /// pbst
    pub psbt: &'psbt Psbt,
    /// input index
    pub index: usize,
}

impl<'psbt> PsbtInputSatisfier<'psbt> {
    /// create a new PsbtInputsatisfier from
    /// psbt and index
    pub fn new(psbt: &'psbt Psbt, index: usize) -> Self {
        Self {
            psbt: psbt,
            index: index,
        }
    }
}

impl<'psbt, Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk> for PsbtInputSatisfier<'psbt> {
    fn lookup_tap_key_spend_sig(&self) -> Option<bitcoin::SchnorrSig> {
        self.psbt.inputs[self.index].tap_key_sig
    }

    fn lookup_tap_leaf_script_sig(&self, pk: &Pk, lh: &TapLeafHash) -> Option<bitcoin::SchnorrSig> {
        self.psbt.inputs[self.index]
            .tap_script_sigs
            .get(&(pk.to_x_only_pubkey(), *lh))
            .map(|x| *x) // replace by copied in 1.36
    }

    fn lookup_tap_control_block_map(
        &self,
    ) -> Option<&BTreeMap<ControlBlock, (bitcoin::Script, LeafVersion)>> {
        Some(&self.psbt.inputs[self.index].tap_scripts)
    }

    fn lookup_pkh_tap_leaf_script_sig(
        &self,
        pkh: &(Pk::Hash, TapLeafHash),
    ) -> Option<(bitcoin::secp256k1::XOnlyPublicKey, bitcoin::SchnorrSig)> {
        self.psbt.inputs[self.index]
            .tap_script_sigs
            .iter()
            .filter(|&((pubkey, lh), _sig)| {
                pubkey.to_pubkeyhash() == Pk::hash_to_hash160(&pkh.0) && *lh == pkh.1
            })
            .next()
            .map(|((x_only_pk, _leaf_hash), sig)| (*x_only_pk, *sig))
    }

    fn lookup_ecdsa_sig(&self, pk: &Pk) -> Option<bitcoin::EcdsaSig> {
        self.psbt.inputs[self.index]
            .partial_sigs
            .get(&pk.to_public_key().inner)
            .map(|sig| *sig)
    }

    fn lookup_pkh_ecdsa_sig(
        &self,
        pkh: &Pk::Hash,
    ) -> Option<(bitcoin::PublicKey, bitcoin::EcdsaSig)> {
        self.psbt.inputs[self.index]
            .partial_sigs
            .iter()
            .filter(|&(pubkey, _sig)| {
                bitcoin::PublicKey::new(*pubkey).to_pubkeyhash() == Pk::hash_to_hash160(pkh)
            })
            .next()
            .map(|(pk, sig)| (bitcoin::PublicKey::new(*pk), *sig))
    }

    fn check_after(&self, n: u32) -> bool {
        let locktime = self.psbt.unsigned_tx.lock_time;
        let seq = self.psbt.unsigned_tx.input[self.index].sequence;

        // https://github.com/bitcoin/bips/blob/master/bip-0065.mediawiki
        // fail if TxIn is finalized
        if seq == 0xffffffff {
            false
        } else {
            <dyn Satisfier<Pk>>::check_after(&After(locktime), n)
        }
    }

    fn check_older(&self, n: u32) -> bool {
        let seq = self.psbt.unsigned_tx.input[self.index].sequence;
        // https://github.com/bitcoin/bips/blob/master/bip-0112.mediawiki
        // Disable flag set. return true
        if n & SEQUENCE_LOCKTIME_DISABLE_FLAG != 0 {
            true
        } else if self.psbt.unsigned_tx.version < 2 || (seq & SEQUENCE_LOCKTIME_DISABLE_FLAG != 0) {
            // transaction version and sequence check
            false
        } else {
            <dyn Satisfier<Pk>>::check_older(&Older(seq), n)
        }
    }

    fn lookup_hash160(&self, h: hash160::Hash) -> Option<Preimage32> {
        self.psbt.inputs[self.index]
            .hash160_preimages
            .get(&h)
            .and_then(try_vec_as_preimage32)
    }

    fn lookup_sha256(&self, h: sha256::Hash) -> Option<Preimage32> {
        self.psbt.inputs[self.index]
            .sha256_preimages
            .get(&h)
            .and_then(try_vec_as_preimage32)
    }

    fn lookup_hash256(&self, h: sha256d::Hash) -> Option<Preimage32> {
        self.psbt.inputs[self.index]
            .hash256_preimages
            .get(&h)
            .and_then(try_vec_as_preimage32)
    }

    fn lookup_ripemd160(&self, h: ripemd160::Hash) -> Option<Preimage32> {
        self.psbt.inputs[self.index]
            .ripemd160_preimages
            .get(&h)
            .and_then(try_vec_as_preimage32)
    }
}

fn try_vec_as_preimage32(vec: &Vec<u8>) -> Option<Preimage32> {
    if vec.len() == 32 {
        let mut arr = [0u8; 32];
        arr.copy_from_slice(&vec);
        Some(arr)
    } else {
        None
    }
}

fn sanity_check(psbt: &Psbt) -> Result<(), Error> {
    if psbt.unsigned_tx.input.len() != psbt.inputs.len() {
        return Err(Error::WrongInputCount {
            in_tx: psbt.unsigned_tx.input.len(),
            in_map: psbt.inputs.len(),
        }
        .into());
    }

    Ok(())
}

/// Psbt extractor as defined in BIP174 that takes in a psbt reference
/// and outputs a extracted bitcoin::Transaction
/// Also does the interpreter sanity check
/// Will error if the final ScriptSig or final Witness are missing
/// or the interpreter check fails.
pub fn extract<C: secp256k1::Verification>(
    psbt: &Psbt,
    secp: &Secp256k1<C>,
) -> Result<bitcoin::Transaction, Error> {
    sanity_check(psbt)?;

    let mut ret = psbt.unsigned_tx.clone();
    for (n, input) in psbt.inputs.iter().enumerate() {
        if input.final_script_sig.is_none() && input.final_script_witness.is_none() {
            return Err(Error::InputError(InputError::MissingWitness, n));
        }

        if let Some(witness) = input.final_script_witness.as_ref() {
            ret.input[n].witness = witness.clone();
        }
        if let Some(script_sig) = input.final_script_sig.as_ref() {
            ret.input[n].script_sig = script_sig.clone();
        }
    }
    interpreter_check(psbt, secp)?;
    Ok(ret)
}

#[cfg(test)]
mod tests {
    use super::*;

    use bitcoin::consensus::encode::deserialize;
    use bitcoin::hashes::hex::FromHex;

    #[test]
    fn test_extract_bip174() {
        let psbt: bitcoin::util::psbt::PartiallySignedTransaction = deserialize(&Vec::<u8>::from_hex("70736274ff01009a020000000258e87a21b56daf0c23be8e7070456c336f7cbaa5c8757924f545887bb2abdd750000000000ffffffff838d0427d0ec650a68aa46bb0b098aea4422c071b2ca78352a077959d07cea1d0100000000ffffffff0270aaf00800000000160014d85c2b71d0060b09c9886aeb815e50991dda124d00e1f5050000000016001400aea9a2e5f0f876a588df5546e8742d1d87008f00000000000100bb0200000001aad73931018bd25f84ae400b68848be09db706eac2ac18298babee71ab656f8b0000000048473044022058f6fc7c6a33e1b31548d481c826c015bd30135aad42cd67790dab66d2ad243b02204a1ced2604c6735b6393e5b41691dd78b00f0c5942fb9f751856faa938157dba01feffffff0280f0fa020000000017a9140fb9463421696b82c833af241c78c17ddbde493487d0f20a270100000017a91429ca74f8a08f81999428185c97b5d852e4063f6187650000000107da00473044022074018ad4180097b873323c0015720b3684cc8123891048e7dbcd9b55ad679c99022073d369b740e3eb53dcefa33823c8070514ca55a7dd9544f157c167913261118c01483045022100f61038b308dc1da865a34852746f015772934208c6d24454393cd99bdf2217770220056e675a675a6d0a02b85b14e5e29074d8a25a9b5760bea2816f661910a006ea01475221029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f2102dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d752ae0001012000c2eb0b0000000017a914b7f5faf40e3d40a5a459b1db3535f2b72fa921e8870107232200208c2353173743b595dfb4a07b72ba8e42e3797da74e87fe7d9d7497e3b20289030108da0400473044022062eb7a556107a7c73f45ac4ab5a1dddf6f7075fb1275969a7f383efff784bcb202200c05dbb7470dbf2f08557dd356c7325c1ed30913e996cd3840945db12228da5f01473044022065f45ba5998b59a27ffe1a7bed016af1f1f90d54b3aa8f7450aa5f56a25103bd02207f724703ad1edb96680b284b56d4ffcb88f7fb759eabbe08aa30f29b851383d20147522103089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc21023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e7352ae00220203a9a4c37f5996d3aa25dbac6b570af0650394492942460b354753ed9eeca5877110d90c6a4f000000800000008004000080002202027f6399757d2eff55a136ad02c684b1838b6556e5f1b6b34282a94b6b5005109610d90c6a4f00000080000000800500008000").unwrap()).unwrap();
        let secp = Secp256k1::verification_only();
        let tx = extract(&psbt, &secp).unwrap();
        let expected: bitcoin::Transaction = deserialize(&Vec::<u8>::from_hex("0200000000010258e87a21b56daf0c23be8e7070456c336f7cbaa5c8757924f545887bb2abdd7500000000da00473044022074018ad4180097b873323c0015720b3684cc8123891048e7dbcd9b55ad679c99022073d369b740e3eb53dcefa33823c8070514ca55a7dd9544f157c167913261118c01483045022100f61038b308dc1da865a34852746f015772934208c6d24454393cd99bdf2217770220056e675a675a6d0a02b85b14e5e29074d8a25a9b5760bea2816f661910a006ea01475221029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f2102dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d752aeffffffff838d0427d0ec650a68aa46bb0b098aea4422c071b2ca78352a077959d07cea1d01000000232200208c2353173743b595dfb4a07b72ba8e42e3797da74e87fe7d9d7497e3b2028903ffffffff0270aaf00800000000160014d85c2b71d0060b09c9886aeb815e50991dda124d00e1f5050000000016001400aea9a2e5f0f876a588df5546e8742d1d87008f000400473044022062eb7a556107a7c73f45ac4ab5a1dddf6f7075fb1275969a7f383efff784bcb202200c05dbb7470dbf2f08557dd356c7325c1ed30913e996cd3840945db12228da5f01473044022065f45ba5998b59a27ffe1a7bed016af1f1f90d54b3aa8f7450aa5f56a25103bd02207f724703ad1edb96680b284b56d4ffcb88f7fb759eabbe08aa30f29b851383d20147522103089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc21023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e7352ae00000000").unwrap()).unwrap();
        assert_eq!(tx, expected);
    }
}
