// SPDX-License-Identifier: CC0-1.0

//! # Partially-Signed Bitcoin Transactions
//!
//! This module implements the Finalizer and Extractor roles defined in
//! BIP 174, PSBT, described at
//! `https://github.com/bitcoin/bips/blob/master/bip-0174.mediawiki`
//!

use core::convert::TryFrom;
use core::fmt;
#[cfg(feature = "std")]
use std::error;

use bitcoin::hashes::{hash160, sha256d, Hash};
use bitcoin::psbt::{self, Psbt};
#[cfg(not(test))] // https://github.com/rust-lang/rust/issues/121684
use bitcoin::secp256k1;
use bitcoin::secp256k1::{Secp256k1, VerifyOnly};
use bitcoin::sighash::{self, SighashCache};
use bitcoin::taproot::{self, ControlBlock, LeafVersion, TapLeafHash};
use bitcoin::{absolute, bip32, relative, transaction, Script, ScriptBuf};

use crate::miniscript::context::SigType;
use crate::prelude::*;
use crate::{
    descriptor, interpreter, DefiniteDescriptorKey, Descriptor, DescriptorPublicKey, MiniscriptKey,
    Preimage32, Satisfier, ToPublicKey, Translator,
};

mod finalizer;

#[allow(deprecated)]
pub use self::finalizer::{finalize, finalize_mall, interpreter_check};

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
    /// Psbt Input index out of bounds
    InputIdxOutofBounds {
        /// Inputs in pbst
        psbt_inp: usize,
        /// requested index
        index: usize,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::InputError(ref inp_err, index) => write!(f, "{} at index {}", inp_err, index),
            Error::WrongInputCount { in_tx, in_map } => {
                write!(f, "PSBT had {} inputs in transaction but {} inputs in map", in_tx, in_map)
            }
            Error::InputIdxOutofBounds { psbt_inp, index } => write!(
                f,
                "psbt input index {} out of bounds: psbt.inputs.len() {}",
                index, psbt_inp
            ),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        use self::Error::*;

        match self {
            InputError(e, _) => Some(e),
            WrongInputCount { .. } | InputIdxOutofBounds { .. } => None,
        }
    }
}

/// Error type for Pbst Input
#[derive(Debug)]
pub enum InputError {
    /// Get the secp Errors directly
    SecpErr(bitcoin::secp256k1::Error),
    /// Key errors
    KeyErr(bitcoin::key::FromSliceError),
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
        redeem: ScriptBuf,
        /// Expected p2sh Script
        p2sh_expected: ScriptBuf,
    },
    /// Witness script does not match the p2wsh hash
    InvalidWitnessScript {
        /// Witness Script
        witness_script: ScriptBuf,
        /// Expected p2wsh script
        p2wsh_expected: ScriptBuf,
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
    NonStandardSighashType(sighash::NonStandardSighashTypeError),
    /// Sighash did not match
    WrongSighashFlag {
        /// required sighash type
        required: sighash::EcdsaSighashType,
        /// the sighash type we got
        got: sighash::EcdsaSighashType,
        /// the corresponding publickey
        pubkey: bitcoin::PublicKey,
    },
    /// Pass through the underlying errors in miniscript.
    Validation(crate::ValidationError),
}

#[cfg(feature = "std")]
impl error::Error for InputError {
    fn cause(&self) -> Option<&dyn error::Error> {
        use self::InputError::*;

        match self {
            CouldNotSatisfyTr
            | InvalidRedeemScript { .. }
            | InvalidWitnessScript { .. }
            | InvalidSignature { .. }
            | MissingRedeemScript
            | MissingWitness
            | MissingPubkey
            | MissingWitnessScript
            | MissingUtxo
            | NonEmptyWitnessScript
            | NonEmptyRedeemScript
            | NonStandardSighashType(_)
            | WrongSighashFlag { .. } => None,
            SecpErr(e) => Some(e),
            KeyErr(e) => Some(e),
            Interpreter(e) => Some(e),
            MiniscriptError(e) => Some(e),
            Validation(e) => Some(e),
        }
    }
}

impl fmt::Display for InputError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            InputError::InvalidSignature { ref pubkey, ref sig } => {
                write!(f, "PSBT: bad signature {} for key {:?}", pubkey, sig)
            }
            InputError::KeyErr(ref e) => write!(f, "Key Err: {}", e),
            InputError::Interpreter(ref e) => write!(f, "Interpreter: {}", e),
            InputError::SecpErr(ref e) => write!(f, "Secp Err: {}", e),
            InputError::InvalidRedeemScript { ref redeem, ref p2sh_expected } => write!(
                f,
                "Redeem script {} does not match the p2sh script {}",
                redeem, p2sh_expected
            ),
            InputError::InvalidWitnessScript { ref witness_script, ref p2wsh_expected } => write!(
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
            InputError::NonEmptyRedeemScript => {
                write!(f, "PSBT has non-empty redeem script at for legacy transactions")
            }
            InputError::NonEmptyWitnessScript => {
                write!(f, "PSBT has non-empty witness script at for legacy input")
            }
            InputError::WrongSighashFlag { required, got, pubkey } => write!(
                f,
                "PSBT: signature with key {:?} had \
                 sighashflag {:?} rather than required {:?}",
                pubkey, got, required
            ),
            InputError::CouldNotSatisfyTr => write!(f, "Could not satisfy Tr descriptor"),
            InputError::NonStandardSighashType(ref e) => {
                write!(f, "Non-standard sighash type {}", e)
            }
            InputError::Validation(ref e) => e.fmt(f),
        }
    }
}

#[doc(hidden)]
impl From<super::Error> for InputError {
    fn from(e: super::Error) -> InputError { InputError::MiniscriptError(e) }
}

#[doc(hidden)]
impl From<bitcoin::secp256k1::Error> for InputError {
    fn from(e: bitcoin::secp256k1::Error) -> InputError { InputError::SecpErr(e) }
}

#[doc(hidden)]
impl From<bitcoin::key::FromSliceError> for InputError {
    fn from(e: bitcoin::key::FromSliceError) -> InputError { InputError::KeyErr(e) }
}

/// Psbt satisfier for at inputs at a particular index.
///
/// Holds a `&psbt` because multiple inputs may share
/// the same psbt structure
/// All operations on this structure will panic if index
/// is more than number of inputs in pbst
pub struct PsbtInputSatisfier<'psbt> {
    /// pbst
    psbt: &'psbt Psbt,
    /// input index
    index: usize,
}

impl<'psbt> PsbtInputSatisfier<'psbt> {
    /// create a new PsbtInputsatisfier from
    /// psbt and index
    pub fn new(psbt: &'psbt Psbt, index: usize) -> Self { Self { psbt, index } }

    /// Accessor for the PSBT this satisfier is associated with.
    pub fn psbt(&self) -> &'psbt Psbt { self.psbt }

    /// Accessor for the input this satisfier is associated with.
    pub fn psbt_input(&self) -> &psbt::Input { &self.psbt.inputs[self.index] }
}

impl<Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk> for PsbtInputSatisfier<'_> {
    fn lookup_tap_key_spend_sig(&self, pk: &Pk) -> Option<bitcoin::taproot::Signature> {
        if let Some(key) = self.psbt_input().tap_internal_key {
            if pk.to_x_only_pubkey() == key {
                return self.psbt_input().tap_key_sig;
            }
        }
        None
    }

    fn lookup_tap_leaf_script_sig(
        &self,
        pk: &Pk,
        lh: &TapLeafHash,
    ) -> Option<bitcoin::taproot::Signature> {
        self.psbt_input()
            .tap_script_sigs
            .get(&(pk.to_x_only_pubkey(), *lh))
            .copied()
    }

    fn lookup_raw_pkh_pk(&self, pkh: &hash160::Hash) -> Option<bitcoin::PublicKey> {
        self.psbt_input()
            .bip32_derivation
            .iter()
            .find(|&(pubkey, _)| pubkey.to_pubkeyhash(SigType::Ecdsa) == *pkh)
            .map(|(pubkey, _)| bitcoin::PublicKey::new(*pubkey))
    }

    fn lookup_tap_control_block_map(
        &self,
    ) -> Option<&BTreeMap<ControlBlock, (bitcoin::ScriptBuf, LeafVersion)>> {
        Some(&self.psbt_input().tap_scripts)
    }

    fn lookup_raw_pkh_tap_leaf_script_sig(
        &self,
        pkh: &(hash160::Hash, TapLeafHash),
    ) -> Option<(bitcoin::secp256k1::XOnlyPublicKey, bitcoin::taproot::Signature)> {
        self.psbt_input()
            .tap_script_sigs
            .iter()
            .find(|&((pubkey, lh), _sig)| {
                pubkey.to_pubkeyhash(SigType::Schnorr) == pkh.0 && *lh == pkh.1
            })
            .map(|((x_only_pk, _leaf_hash), sig)| (*x_only_pk, *sig))
    }

    fn lookup_ecdsa_sig(&self, pk: &Pk) -> Option<bitcoin::ecdsa::Signature> {
        self.psbt_input()
            .partial_sigs
            .get(&pk.to_public_key())
            .copied()
    }

    fn lookup_raw_pkh_ecdsa_sig(
        &self,
        pkh: &hash160::Hash,
    ) -> Option<(bitcoin::PublicKey, bitcoin::ecdsa::Signature)> {
        self.psbt_input()
            .partial_sigs
            .iter()
            .find(|&(pubkey, _sig)| pubkey.to_pubkeyhash(SigType::Ecdsa) == *pkh)
            .map(|(pk, sig)| (*pk, *sig))
    }

    fn check_after(&self, n: absolute::LockTime) -> bool {
        if !self.psbt.unsigned_tx.input[self.index].enables_lock_time() {
            return false;
        }

        let lock_time = self.psbt.unsigned_tx.lock_time;

        <dyn Satisfier<Pk>>::check_after(&lock_time, n)
    }

    fn check_older(&self, n: relative::LockTime) -> bool {
        let seq = self.psbt.unsigned_tx.input[self.index].sequence;

        if self.psbt.unsigned_tx.version < transaction::Version::TWO || !seq.is_relative_lock_time()
        {
            return false;
        }

        <dyn Satisfier<Pk>>::check_older(&seq, n)
    }

    fn lookup_hash160(&self, h: &Pk::Hash160) -> Option<Preimage32> {
        self.psbt_input()
            .hash160_preimages
            .get(&Pk::to_hash160(h))
            .and_then(|x: &Vec<u8>| <[u8; 32]>::try_from(&x[..]).ok())
    }

    fn lookup_sha256(&self, h: &Pk::Sha256) -> Option<Preimage32> {
        self.psbt_input()
            .sha256_preimages
            .get(&Pk::to_sha256(h))
            .and_then(|x: &Vec<u8>| <[u8; 32]>::try_from(&x[..]).ok())
    }

    fn lookup_hash256(&self, h: &Pk::Hash256) -> Option<Preimage32> {
        self.psbt_input()
            .hash256_preimages
            .get(&sha256d::Hash::from_byte_array(Pk::to_hash256(h).to_byte_array())) // upstream psbt operates on hash256
            .and_then(|x: &Vec<u8>| <[u8; 32]>::try_from(&x[..]).ok())
    }

    fn lookup_ripemd160(&self, h: &Pk::Ripemd160) -> Option<Preimage32> {
        self.psbt_input()
            .ripemd160_preimages
            .get(&Pk::to_ripemd160(h))
            .and_then(|x: &Vec<u8>| <[u8; 32]>::try_from(&x[..]).ok())
    }
}

// Basic sanity checks on psbts.
// rust-bitcoin TODO: (Long term)
// Brainstorm about how we can enforce these in type system while having a nice API
fn sanity_check(psbt: &Psbt) -> Result<(), Error> {
    if psbt.unsigned_tx.input.len() != psbt.inputs.len() {
        return Err(Error::WrongInputCount {
            in_tx: psbt.unsigned_tx.input.len(),
            in_map: psbt.inputs.len(),
        });
    }

    // Check well-formedness of input data
    for (index, input) in psbt.inputs.iter().enumerate() {
        // TODO: fix this after https://github.com/rust-bitcoin/rust-bitcoin/issues/838
        let target_ecdsa_sighash_ty = match input.sighash_type {
            Some(psbt_hash_ty) => psbt_hash_ty
                .ecdsa_hash_ty()
                .map_err(|e| Error::InputError(InputError::NonStandardSighashType(e), index))?,
            None => sighash::EcdsaSighashType::All,
        };
        for (key, ecdsa_sig) in &input.partial_sigs {
            let flag = sighash::EcdsaSighashType::from_standard(ecdsa_sig.sighash_type as u32)
                .map_err(|_| {
                    Error::InputError(
                        InputError::Interpreter(interpreter::Error::NonStandardSighash(
                            ecdsa_sig.to_vec(),
                        )),
                        index,
                    )
                })?;
            if target_ecdsa_sighash_ty != flag {
                return Err(Error::InputError(
                    InputError::WrongSighashFlag {
                        required: target_ecdsa_sighash_ty,
                        got: flag,
                        pubkey: *key,
                    },
                    index,
                ));
            }
            // Signatures are well-formed in psbt partial sigs
        }
    }

    Ok(())
}

/// Additional operations for miniscript descriptors for various psbt roles.
/// Note that these APIs would generally error when used on scripts that are not
/// miniscripts.
pub trait PsbtExt {
    /// Finalize the psbt. This function takes in a mutable reference to psbt
    /// and populates the final_witness and final_scriptsig
    /// for all miniscript inputs.
    ///
    /// Finalizes all inputs that it can finalize, and returns an error for each input
    /// that it cannot finalize. Also performs a sanity interpreter check on the
    /// finalized psbt which involves checking the signatures/ preimages/timelocks.
    ///
    /// Input finalization also fails if it is not possible to satisfy any of the inputs non-malleably
    /// See [finalizer::finalize_mall] if you want to allow malleable satisfactions
    ///
    /// For finalizing individual inputs, see also [`PsbtExt::finalize_inp`]
    ///
    /// # Errors:
    ///
    /// - A vector of errors, one of each of failed finalized input
    fn finalize_mut<C: secp256k1::Verification>(
        &mut self,
        secp: &secp256k1::Secp256k1<C>,
    ) -> Result<(), Vec<Error>>;

    /// Same as [`PsbtExt::finalize_mut`], but does not mutate the input psbt and
    /// returns a new psbt
    ///
    /// # Errors:
    ///
    /// - Returns a mutated psbt with all inputs `finalize_mut` could finalize
    /// - A vector of input errors, one of each of failed finalized input
    fn finalize<C: secp256k1::Verification>(
        self,
        secp: &secp256k1::Secp256k1<C>,
    ) -> Result<Psbt, (Psbt, Vec<Error>)>;

    /// Same as [PsbtExt::finalize_mut], but allows for malleable satisfactions
    fn finalize_mall_mut<C: secp256k1::Verification>(
        &mut self,
        secp: &Secp256k1<C>,
    ) -> Result<(), Vec<Error>>;

    /// Same as [PsbtExt::finalize], but allows for malleable satisfactions
    fn finalize_mall<C: secp256k1::Verification>(
        self,
        secp: &Secp256k1<C>,
    ) -> Result<Psbt, (Psbt, Vec<Error>)>;

    /// Same as [`PsbtExt::finalize_mut`], but only tries to finalize a single input leaving other
    /// inputs as is. Use this when not all of inputs that you are trying to
    /// satisfy are miniscripts
    ///
    /// # Errors:
    ///
    /// - Input error detailing why the finalization failed. The psbt is not mutated when the finalization fails
    fn finalize_inp_mut<C: secp256k1::Verification>(
        &mut self,
        secp: &secp256k1::Secp256k1<C>,
        index: usize,
    ) -> Result<(), Error>;

    /// Same as [`PsbtExt::finalize_inp_mut`], but does not mutate the psbt and returns a new one
    ///
    /// # Errors:
    ///  Returns a tuple containing
    /// - Original psbt
    /// - Input Error detailing why the input finalization failed
    #[allow(clippy::result_large_err)] // our "error type" includes the original PSBT
    fn finalize_inp<C: secp256k1::Verification>(
        self,
        secp: &secp256k1::Secp256k1<C>,
        index: usize,
    ) -> Result<Psbt, (Psbt, Error)>;

    /// Same as [`PsbtExt::finalize_inp_mut`], but allows for malleable satisfactions
    fn finalize_inp_mall_mut<C: secp256k1::Verification>(
        &mut self,
        secp: &secp256k1::Secp256k1<C>,
        index: usize,
    ) -> Result<(), Error>;

    /// Same as [`PsbtExt::finalize_inp`], but allows for malleable satisfactions
    #[allow(clippy::result_large_err)] // our "error type" includes the original PSBT
    fn finalize_inp_mall<C: secp256k1::Verification>(
        self,
        secp: &secp256k1::Secp256k1<C>,
        index: usize,
    ) -> Result<Psbt, (Psbt, Error)>;

    /// Psbt extractor as defined in BIP174 that takes in a psbt reference
    /// and outputs a extracted [`bitcoin::Transaction`].
    ///
    /// Also does the interpreter sanity check.
    ///
    /// Will error if the final ScriptSig or final Witness are missing
    /// or the interpreter check fails.
    fn extract<C: secp256k1::Verification>(
        &self,
        secp: &Secp256k1<C>,
    ) -> Result<bitcoin::Transaction, Error>;

    /// Update PSBT input with a descriptor and check consistency of `*_utxo` fields.
    ///
    /// This is the checked version of [`update_with_descriptor_unchecked`]. It checks that the
    /// `witness_utxo` and `non_witness_utxo` are sane and have a `script_pubkey` that matches the
    /// descriptor. In particular, it makes sure pre-segwit descriptors always have `non_witness_utxo`
    /// present (and the txid matches). If both `witness_utxo` and `non_witness_utxo` are present
    /// then it also checks they are consistent with each other.
    ///
    /// Hint: because of the *[segwit bug]* some PSBT signers require that `non_witness_utxo` is
    /// present on segwitv0 inputs regardless but this function doesn't enforce this so you will
    /// have to do this check its presence manually (if it is present this *will* check its
    /// validity).
    ///
    /// The `descriptor` **must not have any wildcards** in it
    /// otherwise an error will be returned however it can (and should) have extended keys in it.
    ///
    /// [`update_with_descriptor_unchecked`]: PsbtInputExt::update_with_descriptor_unchecked
    /// [segwit bug]: https://bitcoinhackers.org/@lukedashjr/104287698361196952
    fn update_input_with_descriptor(
        &mut self,
        input_index: usize,
        descriptor: &Descriptor<DefiniteDescriptorKey>,
    ) -> Result<(), UtxoUpdateError>;

    /// Update PSBT output with a descriptor and check consistency of the output's `script_pubkey`
    ///
    /// This is the checked version of [`update_with_descriptor_unchecked`]. It checks that the
    /// output's `script_pubkey` matches the descriptor.
    ///
    /// The `descriptor` **must not have any wildcards** in it
    /// otherwise an error will be returned however it can (and should) have extended keys in it.
    ///
    /// [`update_with_descriptor_unchecked`]: PsbtOutputExt::update_with_descriptor_unchecked
    fn update_output_with_descriptor(
        &mut self,
        output_index: usize,
        descriptor: &Descriptor<DefiniteDescriptorKey>,
    ) -> Result<(), OutputUpdateError>;

    /// Get the sighash message(data to sign) at input index `idx`.
    ///
    /// Based on the sighash
    /// flag specified in the [`Psbt`] sighash field. If the input sighash flag psbt field is `None`
    /// the [`sighash::TapSighashType::Default`] is chosen
    /// for for taproot spends, otherwise [`EcdsaSighashType::All`](bitcoin::sighash::EcdsaSighashType::All) is chosen.
    /// If the utxo at `idx` is a taproot output, returns a [`PsbtSighashMsg::TapSighash`] variant.
    /// If the utxo at `idx` is a pre-taproot segwit output, returns a [`PsbtSighashMsg::SegwitV0Sighash`] variant.
    /// For legacy outputs, returns a [`PsbtSighashMsg::LegacySighash`] variant.
    /// The `tapleaf_hash` parameter can be used to specify which tapleaf script hash has to be computed. If
    /// `tapleaf_hash` is [`None`], and the output is taproot output, the key spend hash is computed. This parameter must be
    /// set to [`None`] while computing sighash for pre-taproot outputs.
    /// The function also updates the sighash cache with transaction computed during sighash computation of this input
    ///
    /// # Arguments:
    ///
    /// * `idx`: The input index of psbt to sign
    /// * `cache`: The [`SighashCache`] for used to cache/read previously cached computations
    /// * `tapleaf_hash`: If the output is taproot, compute the sighash for this particular leaf.
    ///
    /// [`SighashCache`]: bitcoin::sighash::SighashCache
    fn sighash_msg<T: Borrow<bitcoin::Transaction>>(
        &self,
        idx: usize,
        cache: &mut SighashCache<T>,
        tapleaf_hash: Option<TapLeafHash>,
    ) -> Result<PsbtSighashMsg, SighashError>;
}

impl PsbtExt for Psbt {
    fn finalize_mut<C: secp256k1::Verification>(
        &mut self,
        secp: &secp256k1::Secp256k1<C>,
    ) -> Result<(), Vec<Error>> {
        // Actually construct the witnesses
        let mut errors = vec![];
        for index in 0..self.inputs.len() {
            match finalizer::finalize_input(self, index, secp, /*allow_mall*/ false) {
                Ok(..) => {}
                Err(e) => {
                    errors.push(e);
                }
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn finalize<C: secp256k1::Verification>(
        mut self,
        secp: &secp256k1::Secp256k1<C>,
    ) -> Result<Psbt, (Psbt, Vec<Error>)> {
        match self.finalize_mut(secp) {
            Ok(..) => Ok(self),
            Err(e) => Err((self, e)),
        }
    }

    fn finalize_mall_mut<C: secp256k1::Verification>(
        &mut self,
        secp: &secp256k1::Secp256k1<C>,
    ) -> Result<(), Vec<Error>> {
        let mut errors = vec![];
        for index in 0..self.inputs.len() {
            match finalizer::finalize_input(self, index, secp, /*allow_mall*/ true) {
                Ok(..) => {}
                Err(e) => {
                    errors.push(e);
                }
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn finalize_mall<C: secp256k1::Verification>(
        mut self,
        secp: &Secp256k1<C>,
    ) -> Result<Psbt, (Psbt, Vec<Error>)> {
        match self.finalize_mall_mut(secp) {
            Ok(..) => Ok(self),
            Err(e) => Err((self, e)),
        }
    }

    fn finalize_inp_mut<C: secp256k1::Verification>(
        &mut self,
        secp: &secp256k1::Secp256k1<C>,
        index: usize,
    ) -> Result<(), Error> {
        if index >= self.inputs.len() {
            return Err(Error::InputIdxOutofBounds { psbt_inp: self.inputs.len(), index });
        }
        finalizer::finalize_input(self, index, secp, /*allow_mall*/ false)
    }

    fn finalize_inp<C: secp256k1::Verification>(
        mut self,
        secp: &secp256k1::Secp256k1<C>,
        index: usize,
    ) -> Result<Psbt, (Psbt, Error)> {
        match self.finalize_inp_mut(secp, index) {
            Ok(..) => Ok(self),
            Err(e) => Err((self, e)),
        }
    }

    fn finalize_inp_mall_mut<C: secp256k1::Verification>(
        &mut self,
        secp: &secp256k1::Secp256k1<C>,
        index: usize,
    ) -> Result<(), Error> {
        if index >= self.inputs.len() {
            return Err(Error::InputIdxOutofBounds { psbt_inp: self.inputs.len(), index });
        }
        finalizer::finalize_input(self, index, secp, /*allow_mall*/ false)
    }

    fn finalize_inp_mall<C: secp256k1::Verification>(
        mut self,
        secp: &secp256k1::Secp256k1<C>,
        index: usize,
    ) -> Result<Psbt, (Psbt, Error)> {
        match self.finalize_inp_mall_mut(secp, index) {
            Ok(..) => Ok(self),
            Err(e) => Err((self, e)),
        }
    }

    fn extract<C: secp256k1::Verification>(
        &self,
        secp: &Secp256k1<C>,
    ) -> Result<bitcoin::Transaction, Error> {
        sanity_check(self)?;

        let mut ret = self.unsigned_tx.clone();
        for (n, input) in self.inputs.iter().enumerate() {
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
        interpreter_check(self, secp)?;
        Ok(ret)
    }

    fn update_input_with_descriptor(
        &mut self,
        input_index: usize,
        desc: &Descriptor<DefiniteDescriptorKey>,
    ) -> Result<(), UtxoUpdateError> {
        let n_inputs = self.inputs.len();
        let input = self
            .inputs
            .get_mut(input_index)
            .ok_or(UtxoUpdateError::IndexOutOfBounds(input_index, n_inputs))?;
        let txin = self
            .unsigned_tx
            .input
            .get(input_index)
            .ok_or(UtxoUpdateError::MissingInputUtxo)?;

        let desc_type = desc.desc_type();

        if let Some(non_witness_utxo) = &input.non_witness_utxo {
            if txin.previous_output.txid != non_witness_utxo.compute_txid() {
                return Err(UtxoUpdateError::UtxoCheck);
            }
        }

        let expected_spk = {
            match (&input.witness_utxo, &input.non_witness_utxo) {
                (Some(witness_utxo), None) => {
                    if desc_type.segwit_version().is_some() {
                        witness_utxo.script_pubkey.clone()
                    } else {
                        return Err(UtxoUpdateError::UtxoCheck);
                    }
                }
                (None, Some(non_witness_utxo)) => non_witness_utxo
                    .output
                    .get(txin.previous_output.vout as usize)
                    .ok_or(UtxoUpdateError::UtxoCheck)?
                    .script_pubkey
                    .clone(),
                (Some(witness_utxo), Some(non_witness_utxo)) => {
                    if witness_utxo
                        != non_witness_utxo
                            .output
                            .get(txin.previous_output.vout as usize)
                            .ok_or(UtxoUpdateError::UtxoCheck)?
                    {
                        return Err(UtxoUpdateError::UtxoCheck);
                    }

                    witness_utxo.script_pubkey.clone()
                }
                (None, None) => return Err(UtxoUpdateError::UtxoCheck),
            }
        };

        let (_, spk_check_passed) =
            update_item_with_descriptor_helper(input, desc, Some(&expected_spk))
                .map_err(UtxoUpdateError::DerivationError)?;

        if !spk_check_passed {
            return Err(UtxoUpdateError::MismatchedScriptPubkey);
        }

        Ok(())
    }

    fn update_output_with_descriptor(
        &mut self,
        output_index: usize,
        desc: &Descriptor<DefiniteDescriptorKey>,
    ) -> Result<(), OutputUpdateError> {
        let n_outputs = self.outputs.len();
        let output = self
            .outputs
            .get_mut(output_index)
            .ok_or(OutputUpdateError::IndexOutOfBounds(output_index, n_outputs))?;
        let txout = self
            .unsigned_tx
            .output
            .get(output_index)
            .ok_or(OutputUpdateError::MissingTxOut)?;

        let (_, spk_check_passed) =
            update_item_with_descriptor_helper(output, desc, Some(&txout.script_pubkey))
                .map_err(OutputUpdateError::DerivationError)?;

        if !spk_check_passed {
            return Err(OutputUpdateError::MismatchedScriptPubkey);
        }

        Ok(())
    }

    fn sighash_msg<T: Borrow<bitcoin::Transaction>>(
        &self,
        idx: usize,
        cache: &mut SighashCache<T>,
        tapleaf_hash: Option<TapLeafHash>,
    ) -> Result<PsbtSighashMsg, SighashError> {
        // Infer a descriptor at idx
        if idx >= self.inputs.len() {
            return Err(SighashError::IndexOutOfBounds(idx, self.inputs.len()));
        }
        let inp = &self.inputs[idx];
        let prevouts = finalizer::prevouts(self).map_err(|_e| SighashError::MissingSpendUtxos)?;
        // Note that as per Psbt spec we should have access to spent_utxos for the transaction
        // Even if the transaction does not require SighashAll, we create `Prevouts::All` for code simplicity
        let prevouts = bitcoin::sighash::Prevouts::All(&prevouts);
        let inp_spk =
            finalizer::get_scriptpubkey(self, idx).map_err(|_e| SighashError::MissingInputUtxo)?;
        if inp_spk.is_p2tr() {
            let hash_ty = inp
                .sighash_type
                .map(|sighash_type| sighash_type.taproot_hash_ty())
                .unwrap_or(Ok(sighash::TapSighashType::Default))
                .map_err(|_e| SighashError::InvalidSighashType)?;
            match tapleaf_hash {
                Some(leaf_hash) => {
                    let tap_sighash_msg = cache
                        .taproot_script_spend_signature_hash(idx, &prevouts, leaf_hash, hash_ty)?;
                    Ok(PsbtSighashMsg::TapSighash(tap_sighash_msg))
                }
                None => {
                    let tap_sighash_msg =
                        cache.taproot_key_spend_signature_hash(idx, &prevouts, hash_ty)?;
                    Ok(PsbtSighashMsg::TapSighash(tap_sighash_msg))
                }
            }
        } else {
            let hash_ty = inp
                .sighash_type
                .map(|sighash_type| sighash_type.ecdsa_hash_ty())
                .unwrap_or(Ok(sighash::EcdsaSighashType::All))
                .map_err(|_e| SighashError::InvalidSighashType)?;
            let amt = finalizer::get_utxo(self, idx)
                .map_err(|_e| SighashError::MissingInputUtxo)?
                .value;
            let is_nested_wpkh = inp_spk.is_p2sh()
                && inp
                    .redeem_script
                    .as_ref()
                    .map(|x| x.is_p2wpkh())
                    .unwrap_or(false);
            let is_nested_wsh = inp_spk.is_p2sh()
                && inp
                    .redeem_script
                    .as_ref()
                    .map(|x| x.is_p2wsh())
                    .unwrap_or(false);
            if inp_spk.is_p2wpkh() || inp_spk.is_p2wsh() || is_nested_wpkh || is_nested_wsh {
                let msg = if inp_spk.is_p2wpkh() {
                    cache.p2wpkh_signature_hash(idx, &inp_spk, amt, hash_ty)?
                } else if is_nested_wpkh {
                    let script_code = inp
                        .redeem_script
                        .as_ref()
                        .expect("redeem script non-empty checked earlier");
                    cache.p2wpkh_signature_hash(idx, script_code, amt, hash_ty)?
                } else {
                    let witness_script = inp
                        .witness_script
                        .as_ref()
                        .ok_or(SighashError::MissingWitnessScript)?;
                    cache.p2wsh_signature_hash(idx, witness_script, amt, hash_ty)?
                };
                Ok(PsbtSighashMsg::SegwitV0Sighash(msg))
            } else {
                // legacy sighash case
                let script_code = if inp_spk.is_p2sh() {
                    inp.redeem_script
                        .as_ref()
                        .ok_or(SighashError::MissingRedeemScript)?
                } else {
                    &inp_spk
                };
                let msg = cache.legacy_signature_hash(idx, script_code, hash_ty.to_u32())?;
                Ok(PsbtSighashMsg::LegacySighash(msg))
            }
        }
    }
}

/// Extension trait for PSBT inputs
pub trait PsbtInputExt {
    /// Given the descriptor for a utxo being spent populate the PSBT input's fields so it can be signed.
    ///
    /// If the descriptor contains wildcards or otherwise cannot be transformed into a concrete
    /// descriptor an error will be returned. The descriptor *can* (and should) have extended keys in
    /// it so PSBT fields like `bip32_derivation` and `tap_key_origins` can be populated.
    ///
    /// Note that his method doesn't check that the `witness_utxo` or `non_witness_utxo` is
    /// consistent with the descriptor. To do that see [`update_input_with_descriptor`].
    ///
    /// ## Return value
    ///
    /// For convenience, this returns the concrete descriptor that is computed internally to fill
    /// out the PSBT input fields. This can be used to manually check that the `script_pubkey` in
    /// `witness_utxo` and/or `non_witness_utxo` is consistent with the descriptor.
    ///
    /// [`update_input_with_descriptor`]: PsbtExt::update_input_with_descriptor
    fn update_with_descriptor_unchecked(
        &mut self,
        descriptor: &Descriptor<DefiniteDescriptorKey>,
    ) -> Result<Descriptor<bitcoin::PublicKey>, descriptor::NonDefiniteKeyError>;
}

impl PsbtInputExt for psbt::Input {
    fn update_with_descriptor_unchecked(
        &mut self,
        descriptor: &Descriptor<DefiniteDescriptorKey>,
    ) -> Result<Descriptor<bitcoin::PublicKey>, descriptor::NonDefiniteKeyError> {
        let (derived, _) = update_item_with_descriptor_helper(self, descriptor, None)?;
        Ok(derived)
    }
}

/// Extension trait for PSBT outputs
pub trait PsbtOutputExt {
    /// Given the descriptor of a PSBT output populate the relevant metadata
    ///
    /// If the descriptor contains wildcards or otherwise cannot be transformed into a concrete
    /// descriptor an error will be returned. The descriptor *can* (and should) have extended keys in
    /// it so PSBT fields like `bip32_derivation` and `tap_key_origins` can be populated.
    ///
    /// Note that this method doesn't check that the `script_pubkey` of the output being
    /// updated matches the descriptor. To do that see [`update_output_with_descriptor`].
    ///
    /// ## Return value
    ///
    /// For convenience, this returns the concrete descriptor that is computed internally to fill
    /// out the PSBT output fields. This can be used to manually check that the `script_pubkey` is
    /// consistent with the descriptor.
    ///
    /// [`update_output_with_descriptor`]: PsbtExt::update_output_with_descriptor
    fn update_with_descriptor_unchecked(
        &mut self,
        descriptor: &Descriptor<DefiniteDescriptorKey>,
    ) -> Result<Descriptor<bitcoin::PublicKey>, descriptor::NonDefiniteKeyError>;
}

impl PsbtOutputExt for psbt::Output {
    fn update_with_descriptor_unchecked(
        &mut self,
        descriptor: &Descriptor<DefiniteDescriptorKey>,
    ) -> Result<Descriptor<bitcoin::PublicKey>, descriptor::NonDefiniteKeyError> {
        let (derived, _) = update_item_with_descriptor_helper(self, descriptor, None)?;
        Ok(derived)
    }
}

// Traverse the pkh lookup while maintaining a reverse map for storing the map
// hash160 -> (XonlyPublicKey)/PublicKey
struct KeySourceLookUp(
    pub BTreeMap<secp256k1::PublicKey, bip32::KeySource>,
    pub secp256k1::Secp256k1<VerifyOnly>,
);

impl Translator<DefiniteDescriptorKey> for KeySourceLookUp {
    type TargetPk = bitcoin::PublicKey;
    type Error = core::convert::Infallible;

    fn pk(&mut self, xpk: &DefiniteDescriptorKey) -> Result<Self::TargetPk, Self::Error> {
        let derived = xpk.derive_public_key(&self.1);
        self.0.insert(
            derived.to_public_key().inner,
            (
                xpk.master_fingerprint(),
                xpk.full_derivation_path()
                    .expect("definite keys cannot be multikeys"),
            ),
        );
        Ok(derived)
    }

    translate_hash_clone!(DescriptorPublicKey);
}

// Provides generalized access to PSBT fields common to inputs and outputs
trait PsbtFields {
    // Common fields are returned as a mutable ref of the same type
    fn redeem_script(&mut self) -> &mut Option<ScriptBuf>;
    fn witness_script(&mut self) -> &mut Option<ScriptBuf>;
    fn bip32_derivation(&mut self) -> &mut BTreeMap<secp256k1::PublicKey, bip32::KeySource>;
    fn tap_internal_key(&mut self) -> &mut Option<bitcoin::key::XOnlyPublicKey>;
    fn tap_key_origins(
        &mut self,
    ) -> &mut BTreeMap<bitcoin::key::XOnlyPublicKey, (Vec<TapLeafHash>, bip32::KeySource)>;
    #[allow(dead_code)]
    fn proprietary(&mut self) -> &mut BTreeMap<psbt::raw::ProprietaryKey, Vec<u8>>;
    #[allow(dead_code)]
    fn unknown(&mut self) -> &mut BTreeMap<psbt::raw::Key, Vec<u8>>;

    // `tap_tree` only appears in psbt::Output, so it's returned as an option of a mutable ref
    fn tap_tree(&mut self) -> Option<&mut Option<taproot::TapTree>> { None }

    // `tap_scripts` and `tap_merkle_root` only appear in psbt::Input
    fn tap_scripts(&mut self) -> Option<&mut BTreeMap<ControlBlock, (ScriptBuf, LeafVersion)>> {
        None
    }
    fn tap_merkle_root(&mut self) -> Option<&mut Option<taproot::TapNodeHash>> { None }
}

impl PsbtFields for psbt::Input {
    fn redeem_script(&mut self) -> &mut Option<ScriptBuf> { &mut self.redeem_script }
    fn witness_script(&mut self) -> &mut Option<ScriptBuf> { &mut self.witness_script }
    fn bip32_derivation(&mut self) -> &mut BTreeMap<secp256k1::PublicKey, bip32::KeySource> {
        &mut self.bip32_derivation
    }
    fn tap_internal_key(&mut self) -> &mut Option<bitcoin::key::XOnlyPublicKey> {
        &mut self.tap_internal_key
    }
    fn tap_key_origins(
        &mut self,
    ) -> &mut BTreeMap<bitcoin::key::XOnlyPublicKey, (Vec<TapLeafHash>, bip32::KeySource)> {
        &mut self.tap_key_origins
    }
    #[allow(dead_code)]
    fn proprietary(&mut self) -> &mut BTreeMap<psbt::raw::ProprietaryKey, Vec<u8>> {
        &mut self.proprietary
    }
    #[allow(dead_code)]
    fn unknown(&mut self) -> &mut BTreeMap<psbt::raw::Key, Vec<u8>> { &mut self.unknown }

    fn tap_scripts(&mut self) -> Option<&mut BTreeMap<ControlBlock, (ScriptBuf, LeafVersion)>> {
        Some(&mut self.tap_scripts)
    }
    fn tap_merkle_root(&mut self) -> Option<&mut Option<taproot::TapNodeHash>> {
        Some(&mut self.tap_merkle_root)
    }
}

impl PsbtFields for psbt::Output {
    fn redeem_script(&mut self) -> &mut Option<ScriptBuf> { &mut self.redeem_script }
    fn witness_script(&mut self) -> &mut Option<ScriptBuf> { &mut self.witness_script }
    fn bip32_derivation(&mut self) -> &mut BTreeMap<secp256k1::PublicKey, bip32::KeySource> {
        &mut self.bip32_derivation
    }
    fn tap_internal_key(&mut self) -> &mut Option<bitcoin::key::XOnlyPublicKey> {
        &mut self.tap_internal_key
    }
    fn tap_key_origins(
        &mut self,
    ) -> &mut BTreeMap<bitcoin::key::XOnlyPublicKey, (Vec<TapLeafHash>, bip32::KeySource)> {
        &mut self.tap_key_origins
    }
    #[allow(dead_code)]
    fn proprietary(&mut self) -> &mut BTreeMap<psbt::raw::ProprietaryKey, Vec<u8>> {
        &mut self.proprietary
    }
    #[allow(dead_code)]
    fn unknown(&mut self) -> &mut BTreeMap<psbt::raw::Key, Vec<u8>> { &mut self.unknown }

    fn tap_tree(&mut self) -> Option<&mut Option<taproot::TapTree>> { Some(&mut self.tap_tree) }
}

fn update_item_with_descriptor_helper<F: PsbtFields>(
    item: &mut F,
    descriptor: &Descriptor<DefiniteDescriptorKey>,
    check_script: Option<&Script>,
    // We return an extra boolean here to indicate an error with `check_script`. We do this
    // because the error is "morally" a UtxoUpdateError::MismatchedScriptPubkey, but some
    // callers expect a `descriptor::NonDefiniteKeyError`, which cannot be produced from a
    // `UtxoUpdateError`, and those callers can't get this error anyway because they pass
    // `None` for `check_script`.
) -> Result<(Descriptor<bitcoin::PublicKey>, bool), descriptor::NonDefiniteKeyError> {
    let secp = Secp256k1::verification_only();

    // 1. Derive the descriptor, recording each key derivation in a map from xpubs
    //    the keysource used to derive the key.
    let mut bip32_derivation = KeySourceLookUp(BTreeMap::new(), secp);
    let derived = descriptor
        .translate_pk(&mut bip32_derivation)
        .map_err(crate::TranslateErr::into_outer_err)
        .expect("No Context errors while translating");

    // 2. If we have a specific scriptpubkey we are targeting, bail out.
    if let Some(check_script) = check_script {
        if check_script != &derived.script_pubkey() {
            return Ok((derived, false));
        }
    }

    // 3. Update the PSBT fields using the derived key map.
    if let Descriptor::Tr(ref tr_derived) = &derived {
        let spend_info = tr_derived.spend_info();
        let KeySourceLookUp(xpub_map, _) = bip32_derivation;

        *item.tap_internal_key() = Some(spend_info.internal_key());
        for (derived_key, key_source) in xpub_map {
            item.tap_key_origins()
                .insert(derived_key.to_x_only_pubkey(), (vec![], key_source));
        }
        if let Some(merkle_root) = item.tap_merkle_root() {
            *merkle_root = spend_info.merkle_root();
        }

        for leaf_derived in spend_info.leaves() {
            let leaf_script = (ScriptBuf::from(leaf_derived.script()), leaf_derived.leaf_version());
            let tapleaf_hash = leaf_derived.leaf_hash();
            if let Some(tap_scripts) = item.tap_scripts() {
                let control_block = leaf_derived.control_block().clone();
                tap_scripts.insert(control_block, leaf_script);
            }

            for leaf_pk in leaf_derived.miniscript().iter_pk() {
                let tapleaf_hashes = &mut item
                    .tap_key_origins()
                    .get_mut(&leaf_pk.to_x_only_pubkey())
                    .expect("inserted all keys above")
                    .0;
                if tapleaf_hashes.last() != Some(&tapleaf_hash) {
                    tapleaf_hashes.push(tapleaf_hash);
                }
            }
        }

        // Ensure there are no duplicated leaf hashes. This can happen if some of them were
        // already present in the map when this function is called, since this only appends new
        // data to the psbt without checking what's already present.
        for (tapleaf_hashes, _) in item.tap_key_origins().values_mut() {
            tapleaf_hashes.sort();
            tapleaf_hashes.dedup();
        }

        // Only set the tap_tree if the item supports it (it's an output) and the descriptor actually
        // contains one, otherwise it'll just be empty
        if let Some(tap_tree) = item.tap_tree() {
            *tap_tree = spend_info.to_tap_tree();
        }
    } else {
        item.bip32_derivation().append(&mut bip32_derivation.0);

        match &derived {
            Descriptor::Bare(_) | Descriptor::Pkh(_) | Descriptor::Wpkh(_) => {}
            Descriptor::Sh(sh) => match sh.as_inner() {
                descriptor::ShInner::Wsh(wsh) => {
                    *item.witness_script() = Some(wsh.inner_script());
                    *item.redeem_script() = Some(wsh.inner_script().to_p2wsh());
                }
                descriptor::ShInner::Wpkh(..) => *item.redeem_script() = Some(sh.inner_script()),
                descriptor::ShInner::SortedMulti(_) | descriptor::ShInner::Ms(_) => {
                    *item.redeem_script() = Some(sh.inner_script())
                }
            },
            Descriptor::Wsh(wsh) => *item.witness_script() = Some(wsh.inner_script()),
            Descriptor::Tr(_) => unreachable!("Tr is dealt with separately"),
        }
    };

    Ok((derived, true))
}

/// Return error type for [`PsbtExt::update_input_with_descriptor`]
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UtxoUpdateError {
    /// Index out of bounds
    IndexOutOfBounds(usize, usize),
    /// The unsigned transaction didn't have an input at that index
    MissingInputUtxo,
    /// Derivation error
    DerivationError(descriptor::NonDefiniteKeyError),
    /// The PSBT's `witness_utxo` and/or `non_witness_utxo` were invalid or missing
    UtxoCheck,
    /// The PSBT's `witness_utxo` and/or `non_witness_utxo` had a script_pubkey that did not match
    /// the descriptor
    MismatchedScriptPubkey,
}

impl fmt::Display for UtxoUpdateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UtxoUpdateError::IndexOutOfBounds(ind, len) => {
                write!(f, "index {}, psbt input len: {}", ind, len)
            }
            UtxoUpdateError::MissingInputUtxo => {
                write!(f, "Missing input in unsigned transaction")
            }
            UtxoUpdateError::DerivationError(e) => write!(f, "Key derivation error {}", e),
            UtxoUpdateError::UtxoCheck => write!(
                f,
                "The input's witness_utxo and/or non_witness_utxo were invalid or missing"
            ),
            UtxoUpdateError::MismatchedScriptPubkey => {
                write!(f, "The input's witness_utxo and/or non_witness_utxo had a script pubkey that didn't match the descriptor")
            }
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for UtxoUpdateError {
    fn cause(&self) -> Option<&dyn error::Error> {
        use self::UtxoUpdateError::*;

        match self {
            IndexOutOfBounds(_, _) | MissingInputUtxo | UtxoCheck | MismatchedScriptPubkey => None,
            DerivationError(e) => Some(e),
        }
    }
}

/// Return error type for [`PsbtExt::update_output_with_descriptor`]
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OutputUpdateError {
    /// Index out of bounds
    IndexOutOfBounds(usize, usize),
    /// The raw unsigned transaction didn't have an output at that index
    MissingTxOut,
    /// Derivation error
    DerivationError(descriptor::NonDefiniteKeyError),
    /// The output's script_pubkey did not match the descriptor
    MismatchedScriptPubkey,
}

impl fmt::Display for OutputUpdateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OutputUpdateError::IndexOutOfBounds(ind, len) => {
                write!(f, "index {}, psbt output len: {}", ind, len)
            }
            OutputUpdateError::MissingTxOut => {
                write!(f, "Missing txout in the unsigned transaction")
            }
            OutputUpdateError::DerivationError(e) => write!(f, "Key derivation error {}", e),
            OutputUpdateError::MismatchedScriptPubkey => {
                write!(f, "The output's script pubkey didn't match the descriptor")
            }
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for OutputUpdateError {
    fn cause(&self) -> Option<&dyn error::Error> {
        use self::OutputUpdateError::*;

        match self {
            IndexOutOfBounds(_, _) | MissingTxOut | MismatchedScriptPubkey => None,
            DerivationError(e) => Some(e),
        }
    }
}

/// Return error type for [`PsbtExt::sighash_msg`]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SighashError {
    /// Index out of bounds
    IndexOutOfBounds(usize, usize),
    /// Missing input utxo
    MissingInputUtxo,
    /// Missing Prevouts
    MissingSpendUtxos,
    /// Invalid Sighash type
    InvalidSighashType,
    /// Computation error for taproot sighash.
    SighashTaproot(sighash::TaprootError),
    /// Computation error for P2WPKH sighash.
    SighashP2wpkh(sighash::P2wpkhError),
    /// Computation error for P2WSH sighash.
    TransactionInputsIndex(transaction::InputsIndexError),
    /// Missing Witness script
    MissingWitnessScript,
    /// Missing Redeem script,
    MissingRedeemScript,
}

impl fmt::Display for SighashError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SighashError::IndexOutOfBounds(ind, len) => {
                write!(f, "index {}, psbt input len: {}", ind, len)
            }
            SighashError::MissingInputUtxo => write!(f, "Missing input utxo in pbst"),
            SighashError::MissingSpendUtxos => write!(f, "Missing Psbt spend utxos"),
            SighashError::InvalidSighashType => write!(f, "Invalid Sighash type"),
            SighashError::MissingWitnessScript => write!(f, "Missing Witness Script"),
            SighashError::MissingRedeemScript => write!(f, "Missing Redeem Script"),
            SighashError::SighashTaproot(ref e) => write!(f, "sighash taproot: {}", e),
            SighashError::SighashP2wpkh(ref e) => write!(f, "sighash p2wpkh: {}", e),
            SighashError::TransactionInputsIndex(ref e) => write!(f, "tx inputs index: {}", e),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for SighashError {
    fn cause(&self) -> Option<&dyn error::Error> {
        use self::SighashError::*;

        match self {
            IndexOutOfBounds(_, _)
            | MissingInputUtxo
            | MissingSpendUtxos
            | InvalidSighashType
            | MissingWitnessScript
            | MissingRedeemScript => None,
            SighashTaproot(ref e) => Some(e),
            SighashP2wpkh(ref e) => Some(e),
            TransactionInputsIndex(ref e) => Some(e),
        }
    }
}

impl From<sighash::TaprootError> for SighashError {
    fn from(e: sighash::TaprootError) -> Self { SighashError::SighashTaproot(e) }
}

impl From<sighash::P2wpkhError> for SighashError {
    fn from(e: sighash::P2wpkhError) -> Self { SighashError::SighashP2wpkh(e) }
}

impl From<transaction::InputsIndexError> for SighashError {
    fn from(e: transaction::InputsIndexError) -> Self { SighashError::TransactionInputsIndex(e) }
}

/// Sighash message(signing data) for a given psbt transaction input.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum PsbtSighashMsg {
    /// Taproot Signature hash
    TapSighash(sighash::TapSighash),
    /// Legacy ECDSA sighash message.
    LegacySighash(sighash::LegacySighash),
    /// Segwit v0 ECDSA sighash message.
    SegwitV0Sighash(sighash::SegwitV0Sighash),
}

impl PsbtSighashMsg {
    /// Convert the message to a [`secp256k1::Message`].
    pub fn to_secp_msg(&self) -> secp256k1::Message {
        match *self {
            PsbtSighashMsg::TapSighash(msg) => secp256k1::Message::from_digest(msg.to_byte_array()),
            PsbtSighashMsg::LegacySighash(msg) => {
                secp256k1::Message::from_digest(msg.to_byte_array())
            }
            PsbtSighashMsg::SegwitV0Sighash(msg) => {
                secp256k1::Message::from_digest(msg.to_byte_array())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use bitcoin::bip32::{DerivationPath, Xpub};
    use bitcoin::consensus::encode::deserialize;
    use bitcoin::key::XOnlyPublicKey;
    use bitcoin::secp256k1::PublicKey;
    use bitcoin::{Amount, OutPoint, TxIn, TxOut};
    use hex;

    use super::*;
    use crate::Miniscript;

    #[test]
    fn test_extract_bip174() {
        let psbt = bitcoin::Psbt::deserialize(&hex::decode_to_vec("70736274ff01009a020000000258e87a21b56daf0c23be8e7070456c336f7cbaa5c8757924f545887bb2abdd750000000000ffffffff838d0427d0ec650a68aa46bb0b098aea4422c071b2ca78352a077959d07cea1d0100000000ffffffff0270aaf00800000000160014d85c2b71d0060b09c9886aeb815e50991dda124d00e1f5050000000016001400aea9a2e5f0f876a588df5546e8742d1d87008f00000000000100bb0200000001aad73931018bd25f84ae400b68848be09db706eac2ac18298babee71ab656f8b0000000048473044022058f6fc7c6a33e1b31548d481c826c015bd30135aad42cd67790dab66d2ad243b02204a1ced2604c6735b6393e5b41691dd78b00f0c5942fb9f751856faa938157dba01feffffff0280f0fa020000000017a9140fb9463421696b82c833af241c78c17ddbde493487d0f20a270100000017a91429ca74f8a08f81999428185c97b5d852e4063f6187650000000107da00473044022074018ad4180097b873323c0015720b3684cc8123891048e7dbcd9b55ad679c99022073d369b740e3eb53dcefa33823c8070514ca55a7dd9544f157c167913261118c01483045022100f61038b308dc1da865a34852746f015772934208c6d24454393cd99bdf2217770220056e675a675a6d0a02b85b14e5e29074d8a25a9b5760bea2816f661910a006ea01475221029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f2102dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d752ae0001012000c2eb0b0000000017a914b7f5faf40e3d40a5a459b1db3535f2b72fa921e8870107232200208c2353173743b595dfb4a07b72ba8e42e3797da74e87fe7d9d7497e3b20289030108da0400473044022062eb7a556107a7c73f45ac4ab5a1dddf6f7075fb1275969a7f383efff784bcb202200c05dbb7470dbf2f08557dd356c7325c1ed30913e996cd3840945db12228da5f01473044022065f45ba5998b59a27ffe1a7bed016af1f1f90d54b3aa8f7450aa5f56a25103bd02207f724703ad1edb96680b284b56d4ffcb88f7fb759eabbe08aa30f29b851383d20147522103089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc21023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e7352ae00220203a9a4c37f5996d3aa25dbac6b570af0650394492942460b354753ed9eeca5877110d90c6a4f000000800000008004000080002202027f6399757d2eff55a136ad02c684b1838b6556e5f1b6b34282a94b6b5005109610d90c6a4f00000080000000800500008000").unwrap()).unwrap();
        let secp = Secp256k1::verification_only();
        let tx = psbt.extract(&secp).unwrap();
        let expected: bitcoin::Transaction = deserialize(&hex::decode_to_vec("0200000000010258e87a21b56daf0c23be8e7070456c336f7cbaa5c8757924f545887bb2abdd7500000000da00473044022074018ad4180097b873323c0015720b3684cc8123891048e7dbcd9b55ad679c99022073d369b740e3eb53dcefa33823c8070514ca55a7dd9544f157c167913261118c01483045022100f61038b308dc1da865a34852746f015772934208c6d24454393cd99bdf2217770220056e675a675a6d0a02b85b14e5e29074d8a25a9b5760bea2816f661910a006ea01475221029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f2102dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d752aeffffffff838d0427d0ec650a68aa46bb0b098aea4422c071b2ca78352a077959d07cea1d01000000232200208c2353173743b595dfb4a07b72ba8e42e3797da74e87fe7d9d7497e3b2028903ffffffff0270aaf00800000000160014d85c2b71d0060b09c9886aeb815e50991dda124d00e1f5050000000016001400aea9a2e5f0f876a588df5546e8742d1d87008f000400473044022062eb7a556107a7c73f45ac4ab5a1dddf6f7075fb1275969a7f383efff784bcb202200c05dbb7470dbf2f08557dd356c7325c1ed30913e996cd3840945db12228da5f01473044022065f45ba5998b59a27ffe1a7bed016af1f1f90d54b3aa8f7450aa5f56a25103bd02207f724703ad1edb96680b284b56d4ffcb88f7fb759eabbe08aa30f29b851383d20147522103089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc21023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e7352ae00000000").unwrap()).unwrap();
        assert_eq!(tx, expected);
    }

    #[test]
    fn test_update_item_tr_no_script() {
        // keys taken from: https://github.com/bitcoin/bips/blob/master/bip-0086.mediawiki#Specifications
        let root_xpub = Xpub::from_str("xpub661MyMwAqRbcFkPHucMnrGNzDwb6teAX1RbKQmqtEF8kK3Z7LZ59qafCjB9eCRLiTVG3uxBxgKvRgbubRhqSKXnGGb1aoaqLrpMBDrVxga8").unwrap();
        let fingerprint = root_xpub.fingerprint();
        let desc = format!("tr([{}/86'/0'/0']xpub6BgBgsespWvERF3LHQu6CnqdvfEvtMcQjYrcRzx53QJjSxarj2afYWcLteoGVky7D3UKDP9QyrLprQ3VCECoY49yfdDEHGCtMMj92pReUsQ/0/0)", fingerprint);
        let desc = Descriptor::from_str(&desc).unwrap();
        let mut psbt_input = psbt::Input::default();
        psbt_input.update_with_descriptor_unchecked(&desc).unwrap();
        let mut psbt_output = psbt::Output::default();
        psbt_output.update_with_descriptor_unchecked(&desc).unwrap();
        let internal_key = XOnlyPublicKey::from_str(
            "cc8a4bc64d897bddc5fbc2f670f7a8ba0b386779106cf1223c6fc5d7cd6fc115",
        )
        .unwrap();
        assert_eq!(psbt_input.tap_internal_key, Some(internal_key));
        assert_eq!(
            psbt_input.tap_key_origins.get(&internal_key),
            Some(&(vec![], (fingerprint, DerivationPath::from_str("m/86'/0'/0'/0/0").unwrap())))
        );
        assert_eq!(psbt_input.tap_key_origins.len(), 1);
        assert_eq!(psbt_input.tap_scripts.len(), 0);
        assert_eq!(psbt_input.tap_merkle_root, None);

        assert_eq!(psbt_output.tap_internal_key, psbt_input.tap_internal_key);
        assert_eq!(psbt_output.tap_key_origins, psbt_input.tap_key_origins);
        assert_eq!(psbt_output.tap_tree, None);
    }

    #[test]
    fn test_update_item_tr_with_tapscript() {
        use crate::Tap;
        // keys taken from: https://github.com/bitcoin/bips/blob/master/bip-0086.mediawiki#Specifications
        let root_xpub = Xpub::from_str("xpub661MyMwAqRbcFkPHucMnrGNzDwb6teAX1RbKQmqtEF8kK3Z7LZ59qafCjB9eCRLiTVG3uxBxgKvRgbubRhqSKXnGGb1aoaqLrpMBDrVxga8").unwrap();
        let fingerprint = root_xpub.fingerprint();
        let xpub = format!("[{}/86'/0'/0']xpub6BgBgsespWvERF3LHQu6CnqdvfEvtMcQjYrcRzx53QJjSxarj2afYWcLteoGVky7D3UKDP9QyrLprQ3VCECoY49yfdDEHGCtMMj92pReUsQ", fingerprint);
        let desc =
            format!("tr({}/0/0,{{pkh({}/0/1),multi_a(2,{}/0/1,{}/1/0)}})", xpub, xpub, xpub, xpub);

        let desc = Descriptor::from_str(&desc).unwrap();
        let internal_key = XOnlyPublicKey::from_str(
            "cc8a4bc64d897bddc5fbc2f670f7a8ba0b386779106cf1223c6fc5d7cd6fc115",
        )
        .unwrap();
        let mut psbt_input = psbt::Input::default();
        psbt_input.update_with_descriptor_unchecked(&desc).unwrap();
        let mut psbt_output = psbt::Output::default();
        psbt_output.update_with_descriptor_unchecked(&desc).unwrap();
        assert_eq!(psbt_input.tap_internal_key, Some(internal_key));
        assert_eq!(
            psbt_input.tap_key_origins.get(&internal_key),
            Some(&(vec![], (fingerprint, DerivationPath::from_str("m/86'/0'/0'/0/0").unwrap())))
        );
        assert_eq!(psbt_input.tap_key_origins.len(), 3);
        assert_eq!(psbt_input.tap_scripts.len(), 2);
        assert!(psbt_input.tap_merkle_root.is_some());

        assert_eq!(psbt_output.tap_internal_key, psbt_input.tap_internal_key);
        assert_eq!(psbt_output.tap_key_origins, psbt_input.tap_key_origins);
        assert!(psbt_output.tap_tree.is_some());

        let key_0_1 = XOnlyPublicKey::from_str(
            "83dfe85a3151d2517290da461fe2815591ef69f2b18a2ce63f01697a8b313145",
        )
        .unwrap();
        let first_leaf_hash = {
            let ms =
                Miniscript::<XOnlyPublicKey, Tap>::from_str(&format!("pkh({})", &key_0_1)).unwrap();
            let first_script = ms.encode();
            assert!(psbt_input
                .tap_scripts
                .values()
                .any(|value| *value == (first_script.clone(), LeafVersion::TapScript)));
            TapLeafHash::from_script(&first_script, LeafVersion::TapScript)
        };

        {
            // check 0/1
            let (leaf_hashes, (key_fingerprint, deriv_path)) =
                psbt_input.tap_key_origins.get(&key_0_1).unwrap();
            assert_eq!(key_fingerprint, &fingerprint);
            assert_eq!(&deriv_path.to_string(), "86'/0'/0'/0/1");
            assert_eq!(leaf_hashes.len(), 2);
            assert!(leaf_hashes.contains(&first_leaf_hash));
        }

        {
            // check 1/0
            let key_1_0 = XOnlyPublicKey::from_str(
                "399f1b2f4393f29a18c937859c5dd8a77350103157eb880f02e8c08214277cef",
            )
            .unwrap();
            let (leaf_hashes, (key_fingerprint, deriv_path)) =
                psbt_input.tap_key_origins.get(&key_1_0).unwrap();
            assert_eq!(key_fingerprint, &fingerprint);
            assert_eq!(&deriv_path.to_string(), "86'/0'/0'/1/0");
            assert_eq!(leaf_hashes.len(), 1);
            assert!(!leaf_hashes.contains(&first_leaf_hash));
        }
    }

    #[test]
    fn test_update_item_non_tr_multi() {
        // values taken from https://github.com/bitcoin/bips/blob/master/bip-0084.mediawiki (after removing zpub thingy)
        let root_xpub = Xpub::from_str("xpub661MyMwAqRbcFkPHucMnrGNzDwb6teAX1RbKQmqtEF8kK3Z7LZ59qafCjB9eCRLiTVG3uxBxgKvRgbubRhqSKXnGGb1aoaqLrpMBDrVxga8").unwrap();
        let fingerprint = root_xpub.fingerprint();
        let xpub = format!("[{}/84'/0'/0']xpub6CatWdiZiodmUeTDp8LT5or8nmbKNcuyvz7WyksVFkKB4RHwCD3XyuvPEbvqAQY3rAPshWcMLoP2fMFMKHPJ4ZeZXYVUhLv1VMrjPC7PW6V", fingerprint);
        let pubkeys = [
            "0330d54fd0dd420a6e5f8d3624f5f3482cae350f79d5f0753bf5beef9c2d91af3c",
            "03e775fd51f0dfb8cd865d9ff1cca2a158cf651fe997fdc9fee9c1d3b5e995ea77",
            "03025324888e429ab8e3dbaf1f7802648b9cd01e9b418485c5fa4c1b9b5700e1a6",
        ];

        let expected_bip32 = pubkeys
            .iter()
            .zip(["0/0", "0/1", "1/0"].iter())
            .map(|(pubkey, path)| {
                (
                    PublicKey::from_str(pubkey).unwrap(),
                    (
                        fingerprint,
                        DerivationPath::from_str(&format!("m/84'/0'/0'/{}", path)).unwrap(),
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();

        {
            // test segwit
            let desc = format!("wsh(multi(2,{}/0/0,{}/0/1,{}/1/0))", xpub, xpub, xpub);
            let desc = Descriptor::from_str(&desc).unwrap();
            let derived = format!("wsh(multi(2,{}))", pubkeys.join(","));
            let derived = Descriptor::<bitcoin::PublicKey>::from_str(&derived).unwrap();

            let mut psbt_input = psbt::Input::default();
            psbt_input.update_with_descriptor_unchecked(&desc).unwrap();

            let mut psbt_output = psbt::Output::default();
            psbt_output.update_with_descriptor_unchecked(&desc).unwrap();

            assert_eq!(expected_bip32, psbt_input.bip32_derivation);
            assert_eq!(psbt_input.witness_script, Some(derived.explicit_script().unwrap()));

            assert_eq!(psbt_output.bip32_derivation, psbt_input.bip32_derivation);
            assert_eq!(psbt_output.witness_script, psbt_input.witness_script);
        }

        {
            // test non-segwit
            let desc = format!("sh(multi(2,{}/0/0,{}/0/1,{}/1/0))", xpub, xpub, xpub);
            let desc = Descriptor::from_str(&desc).unwrap();
            let derived = format!("sh(multi(2,{}))", pubkeys.join(","));
            let derived = Descriptor::<bitcoin::PublicKey>::from_str(&derived).unwrap();

            let mut psbt_input = psbt::Input::default();
            psbt_input.update_with_descriptor_unchecked(&desc).unwrap();

            let mut psbt_output = psbt::Output::default();
            psbt_output.update_with_descriptor_unchecked(&desc).unwrap();

            assert_eq!(psbt_input.bip32_derivation, expected_bip32);
            assert_eq!(psbt_input.witness_script, None);
            assert_eq!(psbt_input.redeem_script, Some(derived.explicit_script().unwrap()));

            assert_eq!(psbt_output.bip32_derivation, psbt_input.bip32_derivation);
            assert_eq!(psbt_output.witness_script, psbt_input.witness_script);
            assert_eq!(psbt_output.redeem_script, psbt_input.redeem_script);
        }
    }

    #[test]
    fn test_update_input_checks() {
        let desc = "tr([73c5da0a/86'/0'/0']xpub6BgBgsespWvERF3LHQu6CnqdvfEvtMcQjYrcRzx53QJjSxarj2afYWcLteoGVky7D3UKDP9QyrLprQ3VCECoY49yfdDEHGCtMMj92pReUsQ/0/0)";
        let desc = Descriptor::<DefiniteDescriptorKey>::from_str(desc).unwrap();

        let mut non_witness_utxo = bitcoin::Transaction {
            version: transaction::Version::ONE,
            lock_time: absolute::LockTime::ZERO,
            input: vec![],
            output: vec![TxOut {
                value: Amount::from_sat(1_000),
                script_pubkey: ScriptBuf::from_hex(
                    "5120a60869f0dbcf1dc659c9cecbaf8050135ea9e8cdc487053f1dc6880949dc684c",
                )
                .unwrap(),
            }],
        };

        let tx = bitcoin::Transaction {
            version: transaction::Version::ONE,
            lock_time: absolute::LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint { txid: non_witness_utxo.compute_txid(), vout: 0 },
                ..Default::default()
            }],
            output: vec![],
        };

        let mut psbt = Psbt::from_unsigned_tx(tx).unwrap();
        assert_eq!(
            psbt.update_input_with_descriptor(0, &desc),
            Err(UtxoUpdateError::UtxoCheck),
            "neither *_utxo are not set"
        );
        psbt.inputs[0].witness_utxo = Some(non_witness_utxo.output[0].clone());
        assert_eq!(
            psbt.update_input_with_descriptor(0, &desc),
            Ok(()),
            "witness_utxo is set which is ok"
        );
        psbt.inputs[0].non_witness_utxo = Some(non_witness_utxo.clone());
        assert_eq!(
            psbt.update_input_with_descriptor(0, &desc),
            Ok(()),
            "matching non_witness_utxo"
        );
        non_witness_utxo.version = transaction::Version::non_standard(0);
        psbt.inputs[0].non_witness_utxo = Some(non_witness_utxo);
        assert_eq!(
            psbt.update_input_with_descriptor(0, &desc),
            Err(UtxoUpdateError::UtxoCheck),
            "non_witness_utxo no longer matches"
        );
        psbt.inputs[0].non_witness_utxo = None;
        psbt.inputs[0].witness_utxo.as_mut().unwrap().script_pubkey = ScriptBuf::default();
        assert_eq!(
            psbt.update_input_with_descriptor(0, &desc),
            Err(UtxoUpdateError::MismatchedScriptPubkey),
            "non_witness_utxo no longer matches"
        );
    }

    #[test]
    fn test_update_output_checks() {
        let desc = "tr([73c5da0a/86'/0'/0']xpub6BgBgsespWvERF3LHQu6CnqdvfEvtMcQjYrcRzx53QJjSxarj2afYWcLteoGVky7D3UKDP9QyrLprQ3VCECoY49yfdDEHGCtMMj92pReUsQ/0/0)";
        let desc = Descriptor::<DefiniteDescriptorKey>::from_str(desc).unwrap();

        let tx = bitcoin::Transaction {
            version: transaction::Version::ONE,
            lock_time: absolute::LockTime::ZERO,
            input: vec![],
            output: vec![TxOut {
                value: Amount::from_sat(1_000),
                script_pubkey: ScriptBuf::from_hex(
                    "5120a60869f0dbcf1dc659c9cecbaf8050135ea9e8cdc487053f1dc6880949dc684c",
                )
                .unwrap(),
            }],
        };

        let mut psbt = Psbt::from_unsigned_tx(tx).unwrap();
        assert_eq!(
            psbt.update_output_with_descriptor(1, &desc),
            Err(OutputUpdateError::IndexOutOfBounds(1, 1)),
            "output index doesn't exist"
        );
        assert_eq!(
            psbt.update_output_with_descriptor(0, &desc),
            Ok(()),
            "script_pubkey should match"
        );
        psbt.unsigned_tx.output[0].script_pubkey = ScriptBuf::default();
        assert_eq!(
            psbt.update_output_with_descriptor(0, &desc),
            Err(OutputUpdateError::MismatchedScriptPubkey),
            "output script_pubkey no longer matches"
        );
    }
}
