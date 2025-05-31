// Written in 2019 by Sanket Kanjular and Andrew Poelstra
// SPDX-License-Identifier: CC0-1.0

use core::fmt;
#[cfg(feature = "std")]
use std::error;

use bitcoin::hashes::hash160;
use bitcoin::hex::DisplayHex;
#[cfg(not(test))] // https://github.com/rust-lang/rust/issues/121684
use bitcoin::secp256k1;
use bitcoin::{absolute, relative, taproot};

use super::BitcoinKey;
use crate::prelude::*;

/// Detailed Error type for Interpreter
#[derive(Debug)]
pub enum Error {
    /// Could not satisfy, absolute locktime not met
    AbsoluteLockTimeNotMet(absolute::LockTime),
    /// Could not satisfy, lock time values are different units
    AbsoluteLockTimeComparisonInvalid(absolute::LockTime, absolute::LockTime),
    /// Cannot Infer a taproot descriptor
    /// Key spends cannot infer the internal key of the descriptor
    /// Inferring script spends is possible, but is hidden nodes are currently
    /// not supported in descriptor spec
    CannotInferTrDescriptors,
    /// Error parsing taproot control block
    ControlBlockParse(taproot::TaprootError),
    /// Tap control block(merkle proofs + tweak) verification error
    ControlBlockVerificationError,
    /// General Interpreter error.
    CouldNotEvaluate,
    /// Error decoding Miniscript from script.
    Decode(crate::miniscript::decode::Error),
    /// ECDSA Signature related error
    EcdsaSig(bitcoin::ecdsa::Error),
    /// We expected a push (including a `OP_1` but no other numeric pushes)
    ExpectedPush,
    /// The preimage to the hash function must be exactly 32 bytes.
    HashPreimageLengthMismatch,
    /// Incorrect scriptPubKey (pay-to-pubkeyhash) for the provided public key
    IncorrectPubkeyHash,
    /// Incorrect scriptPubKey for the provided redeem script
    IncorrectScriptHash,
    /// Incorrect scriptPubKey (pay-to-witness-pubkeyhash) for the provided public key
    IncorrectWPubkeyHash,
    /// Incorrect scriptPubKey for the provided witness script
    IncorrectWScriptHash,
    /// MultiSig missing at least `1` witness elements out of `k + 1` required
    InsufficientSignaturesMultiSig,
    /// Invalid Sighash type
    InvalidSchnorrSighashType(Vec<u8>),
    /// ecdsa Signature failed to verify
    InvalidEcdsaSignature(bitcoin::PublicKey),
    /// Signature failed to verify
    InvalidSchnorrSignature(bitcoin::key::XOnlyPublicKey),
    /// Last byte of this signature isn't a standard sighash type
    NonStandardSighash(Vec<u8>),
    /// MultiSig requires 1 extra zero element apart from the `k` signatures
    MissingExtraZeroMultiSig,
    /// Script abortion because of incorrect dissatisfaction for multisig.
    /// Any input witness apart from sat(0 sig ...) or nsat(0 0 ..) leads to
    /// this error. This is network standardness assumption and miniscript only
    /// supports standard scripts
    MultiSigEvaluationError,
    ///Witness must be empty for pre-segwit transactions
    NonEmptyWitness,
    ///ScriptSig must be empty for pure segwit transactions
    NonEmptyScriptSig,
    /// Script abortion because of incorrect dissatisfaction for Checksig.
    /// Any input witness apart from sat(sig) or nsat(0) leads to
    /// this error. This is network standardness assumption and miniscript only
    /// supports standard scripts
    // note that BitcoinKey is not exported, create a data structure to convey the same
    // information in error
    PkEvaluationError(PkEvalErrInner),
    /// The Public Key hash check for the given pubkey. This occurs in `PkH`
    /// node when the given key does not match to Hash in script.
    PkHashVerifyFail(hash160::Hash),
    /// Parse Error while parsing a `stack::Element::Push` as a Pubkey. Both
    /// 33 byte and 65 bytes are supported.
    PubkeyParseError,
    /// Parse Error while parsing a `stack::Element::Push` as a XOnlyPublicKey (32 bytes)
    XOnlyPublicKeyParseError,
    /// Could not satisfy, relative locktime not met
    RelativeLockTimeNotMet(relative::LockTime),
    /// Could not satisfy, the sequence number on the tx input had the disable flag set.
    RelativeLockTimeDisabled(relative::LockTime),
    /// Forward-secp related errors
    Secp(secp256k1::Error),
    /// Miniscript requires the entire top level script to be satisfied.
    ScriptSatisfactionError,
    /// Schnorr Signature error
    SchnorrSig(bitcoin::taproot::SigFromSliceError),
    /// Errors in signature hash calculations
    SighashError(bitcoin::sighash::InvalidSighashTypeError),
    /// Taproot Annex Unsupported
    TapAnnexUnsupported,
    /// An uncompressed public key was encountered in a context where it is
    /// disallowed (e.g. in a Segwit script or p2wpkh output)
    UncompressedPubkey,
    /// Got `stack::Element::Satisfied` or `stack::Element::Dissatisfied` when the
    /// interpreter was expecting `stack::Element::Push`
    UnexpectedStackBoolean,
    /// Unexpected Stack End, caused by popping extra elements from stack
    UnexpectedStackEnd,
    /// Unexpected Stack Push `stack::Element::Push` element when the interpreter
    /// was expecting a stack boolean `stack::Element::Satisfied` or
    /// `stack::Element::Dissatisfied`
    UnexpectedStackElementPush,
    /// Verify expects stack top element exactly to be `stack::Element::Satisfied`.
    /// This error is raised even if the stack top is `stack::Element::Push`.
    VerifyFailed,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::AbsoluteLockTimeNotMet(n) => {
                write!(f, "required absolute locktime CLTV of {} blocks, not met", n)
            }
            Self::AbsoluteLockTimeComparisonInvalid(n, lock_time) => write!(
                f,
                "could not satisfy, lock time values are different units n: {} lock_time: {}",
                n, lock_time
            ),
            Self::CannotInferTrDescriptors => write!(f, "Cannot infer taproot descriptors"),
            Self::ControlBlockParse(ref e) => write!(f, "Control block parse error {}", e),
            Self::ControlBlockVerificationError => f.write_str("Control block verification failed"),
            Self::EcdsaSig(ref s) => write!(f, "Ecdsa sig error: {}", s),
            Self::ExpectedPush => f.write_str("expected push in script"),
            Self::CouldNotEvaluate => f.write_str("Interpreter Self: Could not evaluate"),
            Self::Decode(ref e) => e.fmt(f),
            Self::HashPreimageLengthMismatch => f.write_str("Hash preimage should be 32 bytes"),
            Self::IncorrectPubkeyHash => f.write_str("public key did not match scriptpubkey"),
            Self::IncorrectScriptHash => f.write_str("redeem script did not match scriptpubkey"),
            Self::IncorrectWPubkeyHash => {
                f.write_str("public key did not match scriptpubkey (segwit v0)")
            }
            Self::IncorrectWScriptHash => f.write_str("witness script did not match scriptpubkey"),
            Self::InsufficientSignaturesMultiSig => f.write_str("Insufficient signatures for CMS"),
            Self::InvalidSchnorrSighashType(ref sig) => {
                write!(f, "Invalid sighash type for schnorr signature '{:x}'", sig.as_hex())
            }
            Self::InvalidEcdsaSignature(pk) => write!(f, "bad ecdsa signature with pk {}", pk),
            Self::InvalidSchnorrSignature(pk) => write!(f, "bad schnorr signature with pk {}", pk),
            Self::NonStandardSighash(ref sig) => {
                write!(f, "Non standard sighash type for signature '{:x}'", sig.as_hex())
            }
            Self::NonEmptyWitness => f.write_str("legacy spend had nonempty witness"),
            Self::NonEmptyScriptSig => f.write_str("segwit spend had nonempty scriptsig"),
            Self::MissingExtraZeroMultiSig => f.write_str("CMS missing extra zero"),
            Self::MultiSigEvaluationError => {
                f.write_str("CMS script aborted, incorrect satisfaction/dissatisfaction")
            }
            Self::PkEvaluationError(ref key) => write!(f, "Incorrect Signature for pk {}", key),
            Self::PkHashVerifyFail(ref hash) => write!(f, "Pubkey Hash check failed {}", hash),
            Self::PubkeyParseError => f.write_str("could not parse pubkey"),
            Self::XOnlyPublicKeyParseError => f.write_str("could not parse x-only pubkey"),
            Self::RelativeLockTimeNotMet(n) => {
                write!(f, "required relative locktime CSV of {} blocks, not met", n)
            }
            Self::RelativeLockTimeDisabled(n) => {
                write!(f, "required relative locktime CSV of {} blocks, but tx sequence number has disable-flag set", n)
            }
            Self::ScriptSatisfactionError => f.write_str("Top level script must be satisfied"),
            Self::Secp(ref e) => fmt::Display::fmt(e, f),
            Self::SchnorrSig(ref s) => write!(f, "Schnorr sig error: {}", s),
            Self::SighashError(ref e) => fmt::Display::fmt(e, f),
            Self::TapAnnexUnsupported => f.write_str("Encountered annex element"),
            Self::UncompressedPubkey => f.write_str("uncompressed pubkey in non-legacy descriptor"),
            Self::UnexpectedStackBoolean => {
                f.write_str("Expected Stack Push operation, found stack bool")
            }
            Self::UnexpectedStackElementPush => write!(f, "Got {}, expected Stack Boolean", 1),
            Self::UnexpectedStackEnd => f.write_str("unexpected end of stack"),
            Self::VerifyFailed => f.write_str("Expected Satisfied Boolean at stack top for VERIFY"),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        match self {
            Self::AbsoluteLockTimeNotMet(_)
            | Self::AbsoluteLockTimeComparisonInvalid(_, _)
            | Self::CannotInferTrDescriptors
            | Self::ControlBlockVerificationError
            | Self::CouldNotEvaluate
            | Self::ExpectedPush
            | Self::HashPreimageLengthMismatch
            | Self::IncorrectPubkeyHash
            | Self::IncorrectScriptHash
            | Self::IncorrectWPubkeyHash
            | Self::IncorrectWScriptHash
            | Self::InsufficientSignaturesMultiSig
            | Self::InvalidEcdsaSignature(_)
            | Self::InvalidSchnorrSignature(_)
            | Self::InvalidSchnorrSighashType(_)
            | Self::NonStandardSighash(_)
            | Self::MissingExtraZeroMultiSig
            | Self::MultiSigEvaluationError
            | Self::NonEmptyWitness
            | Self::NonEmptyScriptSig
            | Self::PubkeyParseError
            | Self::XOnlyPublicKeyParseError
            | Self::PkEvaluationError(_)
            | Self::PkHashVerifyFail(_)
            | Self::RelativeLockTimeNotMet(_)
            | Self::RelativeLockTimeDisabled(_)
            | Self::ScriptSatisfactionError
            | Self::TapAnnexUnsupported
            | Self::UncompressedPubkey
            | Self::UnexpectedStackBoolean
            | Self::UnexpectedStackEnd
            | Self::UnexpectedStackElementPush
            | Self::VerifyFailed => None,
            Self::ControlBlockParse(e) => Some(e),
            Self::Decode(e) => Some(e),
            Self::EcdsaSig(e) => Some(e),
            Self::Secp(e) => Some(e),
            Self::SchnorrSig(e) => Some(e),
            Self::SighashError(e) => Some(e),
        }
    }
}

#[doc(hidden)]
impl From<secp256k1::Error> for Error {
    fn from(e: secp256k1::Error) -> Self { Self::Secp(e) }
}

#[doc(hidden)]
impl From<bitcoin::sighash::InvalidSighashTypeError> for Error {
    fn from(e: bitcoin::sighash::InvalidSighashTypeError) -> Self { Self::SighashError(e) }
}

#[doc(hidden)]
impl From<bitcoin::ecdsa::Error> for Error {
    fn from(e: bitcoin::ecdsa::Error) -> Self { Self::EcdsaSig(e) }
}

#[doc(hidden)]
impl From<bitcoin::taproot::SigFromSliceError> for Error {
    fn from(e: bitcoin::taproot::SigFromSliceError) -> Self { Self::SchnorrSig(e) }
}

/// A type of representing which keys errored during interpreter checksig evaluation
// Note that we can't use BitcoinKey because it is not public
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PkEvalErrInner {
    /// Full Key
    FullKey(bitcoin::PublicKey),
    /// XOnly Key
    XOnlyKey(bitcoin::key::XOnlyPublicKey),
}

impl From<BitcoinKey> for PkEvalErrInner {
    fn from(pk: BitcoinKey) -> Self {
        match pk {
            BitcoinKey::Fullkey(pk) => Self::FullKey(pk),
            BitcoinKey::XOnlyPublicKey(xpk) => Self::XOnlyKey(xpk),
        }
    }
}

impl fmt::Display for PkEvalErrInner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FullKey(pk) => pk.fmt(f),
            Self::XOnlyKey(xpk) => xpk.fmt(f),
        }
    }
}
