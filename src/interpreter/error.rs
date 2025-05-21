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
            Error::AbsoluteLockTimeNotMet(n) => {
                write!(f, "required absolute locktime CLTV of {} blocks, not met", n)
            }
            Error::AbsoluteLockTimeComparisonInvalid(n, lock_time) => write!(
                f,
                "could not satisfy, lock time values are different units n: {} lock_time: {}",
                n, lock_time
            ),
            Error::CannotInferTrDescriptors => write!(f, "Cannot infer taproot descriptors"),
            Error::ControlBlockParse(ref e) => write!(f, "Control block parse error {}", e),
            Error::ControlBlockVerificationError => {
                f.write_str("Control block verification failed")
            }
            Error::EcdsaSig(ref s) => write!(f, "Ecdsa sig error: {}", s),
            Error::ExpectedPush => f.write_str("expected push in script"),
            Error::CouldNotEvaluate => f.write_str("Interpreter Error: Could not evaluate"),
            Error::Decode(ref e) => e.fmt(f),
            Error::HashPreimageLengthMismatch => f.write_str("Hash preimage should be 32 bytes"),
            Error::IncorrectPubkeyHash => f.write_str("public key did not match scriptpubkey"),
            Error::IncorrectScriptHash => f.write_str("redeem script did not match scriptpubkey"),
            Error::IncorrectWPubkeyHash => {
                f.write_str("public key did not match scriptpubkey (segwit v0)")
            }
            Error::IncorrectWScriptHash => f.write_str("witness script did not match scriptpubkey"),
            Error::InsufficientSignaturesMultiSig => f.write_str("Insufficient signatures for CMS"),
            Error::InvalidSchnorrSighashType(ref sig) => {
                write!(f, "Invalid sighash type for schnorr signature '{:x}'", sig.as_hex())
            }
            Error::InvalidEcdsaSignature(pk) => write!(f, "bad ecdsa signature with pk {}", pk),
            Error::InvalidSchnorrSignature(pk) => write!(f, "bad schnorr signature with pk {}", pk),
            Error::NonStandardSighash(ref sig) => {
                write!(f, "Non standard sighash type for signature '{:x}'", sig.as_hex())
            }
            Error::NonEmptyWitness => f.write_str("legacy spend had nonempty witness"),
            Error::NonEmptyScriptSig => f.write_str("segwit spend had nonempty scriptsig"),
            Error::MissingExtraZeroMultiSig => f.write_str("CMS missing extra zero"),
            Error::MultiSigEvaluationError => {
                f.write_str("CMS script aborted, incorrect satisfaction/dissatisfaction")
            }
            Error::PkEvaluationError(ref key) => write!(f, "Incorrect Signature for pk {}", key),
            Error::PkHashVerifyFail(ref hash) => write!(f, "Pubkey Hash check failed {}", hash),
            Error::PubkeyParseError => f.write_str("could not parse pubkey"),
            Error::XOnlyPublicKeyParseError => f.write_str("could not parse x-only pubkey"),
            Error::RelativeLockTimeNotMet(n) => {
                write!(f, "required relative locktime CSV of {} blocks, not met", n)
            }
            Error::RelativeLockTimeDisabled(n) => {
                write!(f, "required relative locktime CSV of {} blocks, but tx sequence number has disable-flag set", n)
            }
            Error::ScriptSatisfactionError => f.write_str("Top level script must be satisfied"),
            Error::Secp(ref e) => fmt::Display::fmt(e, f),
            Error::SchnorrSig(ref s) => write!(f, "Schnorr sig error: {}", s),
            Error::SighashError(ref e) => fmt::Display::fmt(e, f),
            Error::TapAnnexUnsupported => f.write_str("Encountered annex element"),
            Error::UncompressedPubkey => {
                f.write_str("uncompressed pubkey in non-legacy descriptor")
            }
            Error::UnexpectedStackBoolean => {
                f.write_str("Expected Stack Push operation, found stack bool")
            }
            Error::UnexpectedStackElementPush => write!(f, "Got {}, expected Stack Boolean", 1),
            Error::UnexpectedStackEnd => f.write_str("unexpected end of stack"),
            Error::VerifyFailed => {
                f.write_str("Expected Satisfied Boolean at stack top for VERIFY")
            }
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        use self::Error::*;

        match self {
            AbsoluteLockTimeNotMet(_)
            | AbsoluteLockTimeComparisonInvalid(_, _)
            | CannotInferTrDescriptors
            | ControlBlockVerificationError
            | CouldNotEvaluate
            | ExpectedPush
            | HashPreimageLengthMismatch
            | IncorrectPubkeyHash
            | IncorrectScriptHash
            | IncorrectWPubkeyHash
            | IncorrectWScriptHash
            | InsufficientSignaturesMultiSig
            | InvalidEcdsaSignature(_)
            | InvalidSchnorrSignature(_)
            | InvalidSchnorrSighashType(_)
            | NonStandardSighash(_)
            | MissingExtraZeroMultiSig
            | MultiSigEvaluationError
            | NonEmptyWitness
            | NonEmptyScriptSig
            | PubkeyParseError
            | XOnlyPublicKeyParseError
            | PkEvaluationError(_)
            | PkHashVerifyFail(_)
            | RelativeLockTimeNotMet(_)
            | RelativeLockTimeDisabled(_)
            | ScriptSatisfactionError
            | TapAnnexUnsupported
            | UncompressedPubkey
            | UnexpectedStackBoolean
            | UnexpectedStackEnd
            | UnexpectedStackElementPush
            | VerifyFailed => None,
            ControlBlockParse(e) => Some(e),
            Decode(e) => Some(e),
            EcdsaSig(e) => Some(e),
            Secp(e) => Some(e),
            SchnorrSig(e) => Some(e),
            SighashError(e) => Some(e),
        }
    }
}

#[doc(hidden)]
impl From<secp256k1::Error> for Error {
    fn from(e: secp256k1::Error) -> Error { Error::Secp(e) }
}

#[doc(hidden)]
impl From<bitcoin::sighash::InvalidSighashTypeError> for Error {
    fn from(e: bitcoin::sighash::InvalidSighashTypeError) -> Error { Error::SighashError(e) }
}

#[doc(hidden)]
impl From<bitcoin::ecdsa::Error> for Error {
    fn from(e: bitcoin::ecdsa::Error) -> Error { Error::EcdsaSig(e) }
}

#[doc(hidden)]
impl From<bitcoin::taproot::SigFromSliceError> for Error {
    fn from(e: bitcoin::taproot::SigFromSliceError) -> Error { Error::SchnorrSig(e) }
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
            BitcoinKey::Fullkey(pk) => PkEvalErrInner::FullKey(pk),
            BitcoinKey::XOnlyPublicKey(xpk) => PkEvalErrInner::XOnlyKey(xpk),
        }
    }
}

impl fmt::Display for PkEvalErrInner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PkEvalErrInner::FullKey(pk) => pk.fmt(f),
            PkEvalErrInner::XOnlyKey(xpk) => xpk.fmt(f),
        }
    }
}
