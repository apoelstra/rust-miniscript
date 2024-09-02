// Written in 2019 by Andrew Poelstra <apoelstra@wpsoftware.net>
// SPDX-License-Identifier: CC0-1.0

//! Miniscript and Output Descriptors
//!
//! ## Bitcoin Script
//!
//! In Bitcoin, spending policies are defined and enforced by means of a
//! stack-based programming language known as Bitcoin Script. While this
//! language appears to be designed with tractable analysis in mind (e.g.
//! there are no looping or jumping constructions), in practice this is
//! extremely difficult. As a result, typical wallet software supports only
//! a small set of script templates, cannot interoperate with other similar
//! software, and each wallet contains independently written ad-hoc manually
//! verified code to handle these templates. Users who require more complex
//! spending policies, or who want to combine signing infrastructure which
//! was not explicitly designed to work together, are simply out of luck.
//!
//! ## Miniscript
//!
//! Miniscript is an alternative to Bitcoin Script which eliminates these
//! problems. It can be efficiently and simply encoded as Script to ensure
//! that it works on the Bitcoin blockchain, but its design is very different.
//! Essentially, a Miniscript is a monotone function (tree of ANDs, ORs and
//! thresholds) of signature requirements, hash preimage requirements, and
//! timelocks.
//!
//! A [full description of Miniscript is available here](https://bitcoin.sipa.be/miniscript).
//!
//! Miniscript also admits a more human-readable encoding.
//!
//! ## Output Descriptors
//!
//! While spending policies in Bitcoin are entirely defined by Script; there
//! are multiple ways of embedding these Scripts in transaction outputs; for
//! example, P2SH or Segwit v0. These different embeddings are expressed by
//! *Output Descriptors*, [which are described here](https://github.com/bitcoin/bitcoin/blob/master/doc/descriptors.md).
//!
//! # Examples
//!
//! ## Deriving an address from a descriptor
//!
//! ```rust
//! use std::str::FromStr;
//!
//! let desc = miniscript::Descriptor::<bitcoin::PublicKey>::from_str("\
//!     sh(wsh(or_d(\
//!     c:pk_k(020e0338c96a8870479f2396c373cc7696ba124e8635d41b0ea581112b67817261),\
//!     c:pk_k(0250863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352)\
//!     )))\
//!     ").unwrap();
//!
//! // Derive the P2SH address.
//! assert_eq!(
//!     desc.address(bitcoin::Network::Bitcoin).unwrap().to_string(),
//!     "3CJxbQBfWAe1ZkKiGQNEYrioV73ZwvBWns"
//! );
//!
//! // Check whether the descriptor is safe. This checks whether all spend paths are accessible in
//! // the Bitcoin network. It may be possible that some of the spend paths require more than 100
//! // elements in Wsh scripts or they contain a combination of timelock and heightlock.
//! assert!(desc.sanity_check().is_ok());
//!
//! // Estimate the satisfaction cost.
//! // scriptSig: OP_PUSH34 <OP_0 OP_32 <32-byte-hash>>
//! // = (1 + 1 + 1 + 32) * 4 = 140 WU
//! // redeemScript: varint <OP_33 <pk1> OP_CHECKSIG OP_IFDUP OP_NOTIF OP_33 <pk2> OP_CHECKSIG OP_ENDIF>
//! // = 1 + (1 + 33 + 1 + 1 + 1 + 1 + 33 + 1 + 1) = 74 WU
//! // stackItem[Sig]: varint <sig+sighash>
//! // = 1 + 73 = 74 WU
//! // Expected satisfaction weight: 140 + 74 + 74 = 288
//! assert_eq!(desc.max_weight_to_satisfy().unwrap().to_wu(), 288);
//! ```
//!

#![cfg_attr(all(not(feature = "std"), not(test)), no_std)]
// Experimental features we need.
#![cfg_attr(bench, feature(test))]
// Coding conventions
#![warn(missing_docs)]
#![deny(unsafe_code)]
// Clippy lints that we have disabled
#![allow(clippy::iter_kv_map)] // https://github.com/rust-lang/rust-clippy/issues/11752
#![allow(clippy::manual_range_contains)] // I hate this lint -asp
#![allow(unexpected_cfgs)] // This one is just batshit.

#[cfg(target_pointer_width = "16")]
compile_error!(
    "rust-miniscript currently only supports architectures with pointers wider than 16 bits"
);

pub use bitcoin;

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

#[cfg(any(feature = "std", test))]
extern crate core;

#[cfg(feature = "serde")]
pub use serde;

#[cfg(bench)]
extern crate test;

#[macro_use]
mod macros;

#[macro_use]
mod pub_macros;

#[cfg(bench)]
mod benchmarks;
mod blanket_traits;
pub mod descriptor;
mod error;
pub mod expression;
pub mod interpreter;
pub mod iter;
pub mod miniscript;
pub mod plan;
pub mod policy;
mod primitives;
pub mod psbt;

#[cfg(test)]
mod test_utils;
mod util;

use core::{fmt, hash, str};

use bitcoin::hashes::{hash160, ripemd160, sha256, Hash};
use bitcoin::hex::DisplayHex;
use bitcoin::{script, Opcode};

pub use crate::blanket_traits::FromStrKey;
pub use crate::descriptor::{DefiniteDescriptorKey, Descriptor, DescriptorPublicKey};
pub use crate::error::ParseError;
pub use crate::expression::{ParseNumError, ParseThresholdError, ParseTreeError};
pub use crate::interpreter::Interpreter;
pub use crate::miniscript::analyzable::{AnalysisError, ExtParams};
pub use crate::miniscript::context::{BareCtx, Legacy, ScriptContext, Segwitv0, SigType, Tap};
pub use crate::miniscript::decode::Terminal;
pub use crate::miniscript::satisfy::{Preimage32, Satisfier};
pub use crate::miniscript::{hash256, Miniscript};
use crate::prelude::*;
pub use crate::primitives::absolute_locktime::{AbsLockTime, AbsLockTimeError};
pub use crate::primitives::relative_locktime::{RelLockTime, RelLockTimeError};
pub use crate::primitives::threshold::{Threshold, ThresholdError};

/// Public key trait which can be converted to Hash type
pub trait MiniscriptKey: Clone + Eq + Ord + fmt::Debug + fmt::Display + hash::Hash {
    /// Returns true if the pubkey is uncompressed. Defaults to `false`.
    fn is_uncompressed(&self) -> bool { false }

    /// Returns true if the pubkey is an x-only pubkey. Defaults to `false`.
    // This is required to know what in DescriptorPublicKey to know whether the inner
    // key in allowed in descriptor context
    fn is_x_only_key(&self) -> bool { false }

    /// Returns the number of different derivation paths in this key. Only >1 for keys
    /// in BIP389 multipath descriptors.
    fn num_der_paths(&self) -> usize { 0 }

    /// The associated [`bitcoin::hashes::sha256::Hash`] for this [`MiniscriptKey`], used in the
    /// sha256 fragment.
    type Sha256: Clone + Eq + Ord + fmt::Display + fmt::Debug + hash::Hash;

    /// The associated [`miniscript::hash256::Hash`] for this [`MiniscriptKey`], used in the
    /// hash256 fragment.
    type Hash256: Clone + Eq + Ord + fmt::Display + fmt::Debug + hash::Hash;

    /// The associated [`bitcoin::hashes::ripemd160::Hash`] for this [`MiniscriptKey`] type, used
    /// in the ripemd160 fragment.
    type Ripemd160: Clone + Eq + Ord + fmt::Display + fmt::Debug + hash::Hash;

    /// The associated [`bitcoin::hashes::hash160::Hash`] for this [`MiniscriptKey`] type, used in
    /// the hash160 fragment.
    type Hash160: Clone + Eq + Ord + fmt::Display + fmt::Debug + hash::Hash;
}

impl MiniscriptKey for bitcoin::secp256k1::PublicKey {
    type Sha256 = sha256::Hash;
    type Hash256 = hash256::Hash;
    type Ripemd160 = ripemd160::Hash;
    type Hash160 = hash160::Hash;
}

impl MiniscriptKey for bitcoin::PublicKey {
    /// Returns the compressed-ness of the underlying secp256k1 key.
    fn is_uncompressed(&self) -> bool { !self.compressed }

    type Sha256 = sha256::Hash;
    type Hash256 = hash256::Hash;
    type Ripemd160 = ripemd160::Hash;
    type Hash160 = hash160::Hash;
}

impl MiniscriptKey for bitcoin::secp256k1::XOnlyPublicKey {
    type Sha256 = sha256::Hash;
    type Hash256 = hash256::Hash;
    type Ripemd160 = ripemd160::Hash;
    type Hash160 = hash160::Hash;

    fn is_x_only_key(&self) -> bool { true }
}

impl MiniscriptKey for String {
    type Sha256 = String; // specify hashes as string
    type Hash256 = String;
    type Ripemd160 = String;
    type Hash160 = String;
}

/// Trait describing public key types which can be converted to bitcoin pubkeys
pub trait ToPublicKey: MiniscriptKey {
    /// Converts an object to a public key
    fn to_public_key(&self) -> bitcoin::PublicKey;

    /// Convert an object to x-only pubkey
    fn to_x_only_pubkey(&self) -> bitcoin::secp256k1::XOnlyPublicKey {
        let pk = self.to_public_key();
        bitcoin::secp256k1::XOnlyPublicKey::from(pk.inner)
    }

    /// Obtain the public key hash for this MiniscriptKey
    /// Expects an argument to specify the signature type.
    /// This would determine whether to serialize the key as 32 byte x-only pubkey
    /// or regular public key when computing the hash160
    fn to_pubkeyhash(&self, sig_type: SigType) -> hash160::Hash {
        match sig_type {
            SigType::Ecdsa => hash160::Hash::hash(&self.to_public_key().to_bytes()),
            SigType::Schnorr => hash160::Hash::hash(&self.to_x_only_pubkey().serialize()),
        }
    }

    /// Converts the generic associated [`MiniscriptKey::Sha256`] to [`sha256::Hash`]
    fn to_sha256(hash: &<Self as MiniscriptKey>::Sha256) -> sha256::Hash;

    /// Converts the generic associated [`MiniscriptKey::Hash256`] to [`hash256::Hash`]
    fn to_hash256(hash: &<Self as MiniscriptKey>::Hash256) -> hash256::Hash;

    /// Converts the generic associated [`MiniscriptKey::Ripemd160`] to [`ripemd160::Hash`]
    fn to_ripemd160(hash: &<Self as MiniscriptKey>::Ripemd160) -> ripemd160::Hash;

    /// Converts the generic associated [`MiniscriptKey::Hash160`] to [`hash160::Hash`]
    fn to_hash160(hash: &<Self as MiniscriptKey>::Hash160) -> hash160::Hash;
}

impl ToPublicKey for bitcoin::PublicKey {
    fn to_public_key(&self) -> bitcoin::PublicKey { *self }

    fn to_sha256(hash: &sha256::Hash) -> sha256::Hash { *hash }

    fn to_hash256(hash: &hash256::Hash) -> hash256::Hash { *hash }

    fn to_ripemd160(hash: &ripemd160::Hash) -> ripemd160::Hash { *hash }

    fn to_hash160(hash: &hash160::Hash) -> hash160::Hash { *hash }
}

impl ToPublicKey for bitcoin::secp256k1::PublicKey {
    fn to_public_key(&self) -> bitcoin::PublicKey { bitcoin::PublicKey::new(*self) }

    fn to_sha256(hash: &sha256::Hash) -> sha256::Hash { *hash }

    fn to_hash256(hash: &hash256::Hash) -> hash256::Hash { *hash }

    fn to_ripemd160(hash: &ripemd160::Hash) -> ripemd160::Hash { *hash }

    fn to_hash160(hash: &hash160::Hash) -> hash160::Hash { *hash }
}

impl ToPublicKey for bitcoin::secp256k1::XOnlyPublicKey {
    fn to_public_key(&self) -> bitcoin::PublicKey {
        // This code should never be used.
        // But is implemented for completeness
        let mut data: Vec<u8> = vec![0x02];
        data.extend(self.serialize().iter());
        bitcoin::PublicKey::from_slice(&data)
            .expect("Failed to construct 33 Publickey from 0x02 appended x-only key")
    }

    fn to_x_only_pubkey(&self) -> bitcoin::secp256k1::XOnlyPublicKey { *self }

    fn to_sha256(hash: &sha256::Hash) -> sha256::Hash { *hash }

    fn to_hash256(hash: &hash256::Hash) -> hash256::Hash { *hash }

    fn to_ripemd160(hash: &ripemd160::Hash) -> ripemd160::Hash { *hash }

    fn to_hash160(hash: &hash160::Hash) -> hash160::Hash { *hash }
}

/// Describes an object that can translate various keys and hashes from one key to the type
/// associated with the other key. Used by the [`TranslatePk`] trait to do the actual translations.
pub trait Translator<P: MiniscriptKey> {
    /// The public key (and associated hash types that this translator converts to.
    type TargetPk: MiniscriptKey;
    /// An error that may occur during transalation.
    type Error;

    /// Translates keys.
    fn pk(&mut self, pk: &P) -> Result<Self::TargetPk, Self::Error>;

    /// Translates SHA256 hashes.
    fn sha256(
        &mut self,
        sha256: &P::Sha256,
    ) -> Result<<Self::TargetPk as MiniscriptKey>::Sha256, Self::Error>;

    /// Translates HASH256 hashes.
    fn hash256(
        &mut self,
        hash256: &P::Hash256,
    ) -> Result<<Self::TargetPk as MiniscriptKey>::Hash256, Self::Error>;

    /// Translates RIPEMD160 hashes.
    fn ripemd160(
        &mut self,
        ripemd160: &P::Ripemd160,
    ) -> Result<<Self::TargetPk as MiniscriptKey>::Ripemd160, Self::Error>;

    /// Translates HASH160 hashes.
    fn hash160(
        &mut self,
        hash160: &P::Hash160,
    ) -> Result<<Self::TargetPk as MiniscriptKey>::Hash160, Self::Error>;
}

/// An enum for representing translation errors
pub enum TranslateErr<E> {
    /// Error inside in the underlying key translation
    TranslatorErr(E),
    /// Error in the final translated structure. In some cases, the translated
    /// structure might not be valid under the given context. For example, translating
    /// from string keys to x-only keys in wsh descriptors.
    OuterError(Error),
}

impl<E> TranslateErr<E> {
    /// Enum used to capture errors from the [`Translator`] trait as well as
    /// context errors from the translated structure.
    /// The errors occurred in translation are captured in the [`TranslateErr::TranslatorErr`]
    /// while the errors in the translated structure are captured in the [`TranslateErr::OuterError`]
    ///
    /// As of taproot upgrade: The following rules apply to the translation of descriptors:
    /// - Legacy/Bare does not allow x_only keys
    /// - SegwitV0 does not allow uncompressed keys and x_only keys
    /// - Tapscript does not allow uncompressed keys
    /// - Translating into multi-path descriptors should have same number of path
    ///   for all the keys in the descriptor
    ///
    /// # Panics
    ///
    /// This function will panic if the Error is OutError.
    pub fn expect_translator_err(self, msg: &str) -> E {
        if let Self::TranslatorErr(v) = self {
            v
        } else {
            panic!("{}", msg)
        }
    }
}

impl<E> From<E> for TranslateErr<E> {
    fn from(v: E) -> Self { Self::TranslatorErr(v) }
}

// Required for unwrap
impl<E: fmt::Debug> fmt::Debug for TranslateErr<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::TranslatorErr(e) => write!(f, "TranslatorErr({:?})", e),
            Self::OuterError(e) => write!(f, "OuterError({:?})", e),
        }
    }
}

/// Converts a descriptor using abstract keys to one using specific keys. Uses translator `t` to do
/// the actual translation function calls.
#[deprecated(since = "TBD", note = "This trait no longer needs to be imported.")]
pub trait TranslatePk<P, Q>
where
    P: MiniscriptKey,
    Q: MiniscriptKey,
{
}

/// Trait describing the ability to iterate over every key
pub trait ForEachKey<Pk: MiniscriptKey> {
    /// Run a predicate on every key in the descriptor, returning whether
    /// the predicate returned true for every key
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, pred: F) -> bool
    where
        Pk: 'a;

    /// Run a predicate on every key in the descriptor, returning whether
    /// the predicate returned true for any key
    fn for_any_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, mut pred: F) -> bool
    where
        Pk: 'a,
    {
        !self.for_each_key(|key| !pred(key))
    }
}

/// Miniscript

#[derive(Debug)]
pub enum Error {
    /// Opcode appeared which is not part of the script subset
    InvalidOpcode(Opcode),
    /// Some opcode occurred followed by `OP_VERIFY` when it had
    /// a `VERIFY` version that should have been used instead
    NonMinimalVerify(String),
    /// Push was illegal in some context
    InvalidPush(Vec<u8>),
    /// rust-bitcoin script error
    Script(script::Error),
    /// rust-bitcoin address error
    AddrError(bitcoin::address::ParseError),
    /// rust-bitcoin p2sh address error
    AddrP2shError(bitcoin::address::P2shError),
    /// While parsing backward, hit beginning of script
    UnexpectedStart,
    /// Got something we were not expecting
    Unexpected(String),
    /// Encountered a wrapping character that we don't recognize
    UnknownWrapper(char),
    /// Parsed a miniscript and the result was not of type T
    NonTopLevel(String),
    /// Parsed a miniscript but there were more script opcodes after it
    Trailing(String),
    /// Could not satisfy a script (fragment) because of a missing signature
    MissingSig(bitcoin::PublicKey),
    /// General failure to satisfy
    CouldNotSatisfy,
    /// Typechecking failed
    TypeCheck(String),
    /// Forward-secp related errors
    Secp(bitcoin::secp256k1::Error),
    #[cfg(feature = "compiler")]
    /// Compiler related errors
    CompilerError(crate::policy::compiler::CompilerError),
    /// Errors related to policy
    ConcretePolicy(policy::concrete::PolicyError),
    /// Errors related to lifting
    LiftError(policy::LiftError),
    /// Forward script context related errors
    ContextError(miniscript::context::ScriptContextError),
    /// Recursion depth exceeded when parsing policy/miniscript from string
    MaxRecursiveDepthExceeded,
    /// Anything but c:pk(key) (P2PK), c:pk_h(key) (P2PKH), and thresh_m(k,...)
    /// up to n=3 is invalid by standardness (bare)
    NonStandardBareScript,
    /// Analysis Error
    AnalysisError(miniscript::analyzable::AnalysisError),
    /// Miniscript is equivalent to false. No possible satisfaction
    ImpossibleSatisfaction,
    /// Bare descriptors don't have any addresses
    BareDescriptorAddr,
    /// PubKey invalid under current context
    PubKeyCtxError(miniscript::decode::KeyParseError, &'static str),
    /// No script code for Tr descriptors
    TrNoScriptCode,
    /// At least two BIP389 key expressions in the descriptor contain tuples of
    /// derivation indexes of different lengths.
    MultipathDescLenMismatch,
    /// Invalid absolute locktime
    AbsoluteLockTime(AbsLockTimeError),
    /// Invalid absolute locktime
    RelativeLockTime(RelLockTimeError),
    /// Invalid threshold.
    Threshold(ThresholdError),
    /// Invalid threshold.
    ParseThreshold(ParseThresholdError),
    /// Invalid expression tree.
    Parse(ParseError),
}

#[doc(hidden)] // will be removed when we remove Error
impl From<ParseThresholdError> for Error {
    fn from(e: ParseThresholdError) -> Self { Self::ParseThreshold(e) }
}

// https://github.com/sipa/miniscript/pull/5 for discussion on this number
const MAX_RECURSION_DEPTH: u32 = 402;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::InvalidOpcode(op) => write!(f, "invalid opcode {}", op),
            Error::NonMinimalVerify(ref tok) => write!(f, "{} VERIFY", tok),
            Error::InvalidPush(ref push) => {
                write!(f, "invalid push {:x}", push.as_hex())
            },
            Error::Script(ref e) => fmt::Display::fmt(e, f),
            Error::AddrError(ref e) => fmt::Display::fmt(e, f),
            Error::AddrP2shError(ref e) => fmt::Display::fmt(e, f),
            Error::UnexpectedStart => f.write_str("unexpected start of script"),
            Error::Unexpected(ref s) => write!(f, "unexpected «{}»", s),
            Error::UnknownWrapper(ch) => write!(f, "unknown wrapper «{}:»", ch),
            Error::NonTopLevel(ref s) => write!(f, "non-T miniscript: {}", s),
            Error::Trailing(ref s) => write!(f, "trailing tokens: {}", s),
            Error::MissingSig(ref pk) => write!(f, "missing signature for key {:?}", pk),
            Error::CouldNotSatisfy => f.write_str("could not satisfy"),
            Error::TypeCheck(ref e) => write!(f, "typecheck: {}", e),
            Error::Secp(ref e) => fmt::Display::fmt(e, f),
            Error::ContextError(ref e) => fmt::Display::fmt(e, f),
            #[cfg(feature = "compiler")]
            Error::CompilerError(ref e) => fmt::Display::fmt(e, f),
            Error::ConcretePolicy(ref e) => fmt::Display::fmt(e, f),
            Error::LiftError(ref e) => fmt::Display::fmt(e, f),
            Error::MaxRecursiveDepthExceeded => write!(
                f,
                "Recursive depth over {} not permitted",
                MAX_RECURSION_DEPTH
            ),
            Error::NonStandardBareScript => write!(
                f,
                "Anything but c:pk(key) (P2PK), c:pk_h(key) (P2PKH), and thresh_m(k,...) \
                up to n=3 is invalid by standardness (bare).
                "
            ),
            Error::AnalysisError(ref e) => e.fmt(f),
            Error::ImpossibleSatisfaction => write!(f, "Impossible to satisfy Miniscript"),
            Error::BareDescriptorAddr => write!(f, "Bare descriptors don't have address"),
            Error::PubKeyCtxError(ref pk, ref ctx) => {
                write!(f, "Pubkey error: {} under {} scriptcontext", pk, ctx)
            }
            Error::TrNoScriptCode => write!(f, "No script code for Tr descriptors"),
            Error::MultipathDescLenMismatch => write!(f, "At least two BIP389 key expressions in the descriptor contain tuples of derivation indexes of different lengths"),
            Error::AbsoluteLockTime(ref e) => e.fmt(f),
            Error::RelativeLockTime(ref e) => e.fmt(f),
            Error::Threshold(ref e) => e.fmt(f),
            Error::ParseThreshold(ref e) => e.fmt(f),
            Error::Parse(ref e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn cause(&self) -> Option<&dyn std::error::Error> {
        use self::Error::*;

        match self {
            InvalidOpcode(_)
            | NonMinimalVerify(_)
            | InvalidPush(_)
            | UnexpectedStart
            | Unexpected(_)
            | UnknownWrapper(_)
            | NonTopLevel(_)
            | Trailing(_)
            | MissingSig(_)
            | CouldNotSatisfy
            | TypeCheck(_)
            | MaxRecursiveDepthExceeded
            | NonStandardBareScript
            | ImpossibleSatisfaction
            | BareDescriptorAddr
            | TrNoScriptCode
            | MultipathDescLenMismatch => None,
            Script(e) => Some(e),
            AddrError(e) => Some(e),
            AddrP2shError(e) => Some(e),
            Secp(e) => Some(e),
            #[cfg(feature = "compiler")]
            CompilerError(e) => Some(e),
            ConcretePolicy(e) => Some(e),
            LiftError(e) => Some(e),
            ContextError(e) => Some(e),
            AnalysisError(e) => Some(e),
            PubKeyCtxError(e, _) => Some(e),
            AbsoluteLockTime(e) => Some(e),
            RelativeLockTime(e) => Some(e),
            Threshold(e) => Some(e),
            ParseThreshold(e) => Some(e),
            Parse(e) => Some(e),
        }
    }
}

#[doc(hidden)]
impl From<miniscript::types::Error> for Error {
    fn from(e: miniscript::types::Error) -> Error { Error::TypeCheck(e.to_string()) }
}

#[doc(hidden)]
impl From<policy::LiftError> for Error {
    fn from(e: policy::LiftError) -> Error { Error::LiftError(e) }
}

#[doc(hidden)]
impl From<miniscript::context::ScriptContextError> for Error {
    fn from(e: miniscript::context::ScriptContextError) -> Error { Error::ContextError(e) }
}

#[doc(hidden)]
impl From<miniscript::analyzable::AnalysisError> for Error {
    fn from(e: miniscript::analyzable::AnalysisError) -> Error { Error::AnalysisError(e) }
}

#[doc(hidden)]
impl From<bitcoin::secp256k1::Error> for Error {
    fn from(e: bitcoin::secp256k1::Error) -> Error { Error::Secp(e) }
}

#[doc(hidden)]
impl From<bitcoin::address::ParseError> for Error {
    fn from(e: bitcoin::address::ParseError) -> Error { Error::AddrError(e) }
}

#[doc(hidden)]
impl From<bitcoin::address::P2shError> for Error {
    fn from(e: bitcoin::address::P2shError) -> Error { Error::AddrP2shError(e) }
}

#[doc(hidden)]
#[cfg(feature = "compiler")]
impl From<crate::policy::compiler::CompilerError> for Error {
    fn from(e: crate::policy::compiler::CompilerError) -> Error { Error::CompilerError(e) }
}

/// The size of an encoding of a number in Script
pub fn script_num_size(n: usize) -> usize {
    match n {
        n if n <= 0x10 => 1,      // OP_n
        n if n < 0x80 => 2,       // OP_PUSH1 <n>
        n if n < 0x8000 => 3,     // OP_PUSH2 <n>
        n if n < 0x800000 => 4,   // OP_PUSH3 <n>
        n if n < 0x80000000 => 5, // OP_PUSH4 <n>
        _ => 6,                   // OP_PUSH5 <n>
    }
}

/// Returns the size of the smallest push opcode used to push a given number of bytes onto the stack
///
/// For sizes ≤ 75, there are dedicated single-byte opcodes, so the push size is one. Otherwise,
/// if the size can fit into 1, 2 or 4 bytes, we use the `PUSHDATA{1,2,4}` opcode respectively,
/// followed by the actual size encoded in that many bytes.
fn push_opcode_size(script_size: usize) -> usize {
    if script_size < 76 {
        1
    } else if script_size < 0x100 {
        2
    } else if script_size < 0x10000 {
        3
    } else {
        5
    }
}

/// Helper function used by tests
#[cfg(test)]
fn hex_script(s: &str) -> bitcoin::ScriptBuf {
    let v: Vec<u8> = bitcoin::hashes::hex::FromHex::from_hex(s).unwrap();
    bitcoin::ScriptBuf::from(v)
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::*;

    #[test]
    fn regression_bitcoin_key_hash() {
        use bitcoin::PublicKey;

        // Uncompressed key.
        let pk = PublicKey::from_str(
            "042e58afe51f9ed8ad3cc7897f634d881fdbe49a81564629ded8156bebd2ffd1af191923a2964c177f5b5923ae500fca49e99492d534aa3759d6b25a8bc971b133"
        ).unwrap();

        let want = hash160::Hash::from_str("ac2e7daf42d2c97418fd9f78af2de552bb9c6a7a").unwrap();
        let got = pk.to_pubkeyhash(SigType::Ecdsa);
        assert_eq!(got, want)
    }

    #[test]
    fn regression_secp256k1_key_hash() {
        use bitcoin::secp256k1::PublicKey;

        // Compressed key.
        let pk = PublicKey::from_str(
            "032e58afe51f9ed8ad3cc7897f634d881fdbe49a81564629ded8156bebd2ffd1af",
        )
        .unwrap();

        let want = hash160::Hash::from_str("9511aa27ef39bbfa4e4f3dd15f4d66ea57f475b4").unwrap();
        let got = pk.to_pubkeyhash(SigType::Ecdsa);
        assert_eq!(got, want)
    }

    #[test]
    fn regression_xonly_key_hash() {
        use bitcoin::secp256k1::XOnlyPublicKey;

        let pk = XOnlyPublicKey::from_str(
            "cc8a4bc64d897bddc5fbc2f670f7a8ba0b386779106cf1223c6fc5d7cd6fc115",
        )
        .unwrap();

        let want = hash160::Hash::from_str("eb8ac65f971ae688a94aeabf223506865e7e08f2").unwrap();
        let got = pk.to_pubkeyhash(SigType::Schnorr);
        assert_eq!(got, want)
    }
}

#[allow(unused_imports)] // this is an internal prelude module; not all imports are used with every feature combination
mod prelude {
    // Mutex implementation from LDK
    // https://github.com/lightningdevkit/rust-lightning/blob/9bdce47f0e0516e37c89c09f1975dfc06b5870b1/lightning-invoice/src/sync.rs
    #[cfg(all(not(feature = "std"), not(test)))]
    mod mutex {
        use core::cell::{RefCell, RefMut};
        use core::ops::{Deref, DerefMut};

        pub type LockResult<Guard> = Result<Guard, ()>;

        /// `Mutex` is not a real mutex as it cannot be used in a multi-threaded
        /// context. `Mutex` is a dummy implementation of [`std::sync::Mutex`]
        /// for `no_std` environments.
        pub struct Mutex<T: ?Sized> {
            inner: RefCell<T>,
        }

        #[must_use = "if unused the Mutex will immediately unlock"]
        pub struct MutexGuard<'a, T: ?Sized + 'a> {
            lock: RefMut<'a, T>,
        }

        impl<T: ?Sized> Deref for MutexGuard<'_, T> {
            type Target = T;

            fn deref(&self) -> &T { self.lock.deref() }
        }

        impl<T: ?Sized> DerefMut for MutexGuard<'_, T> {
            fn deref_mut(&mut self) -> &mut T { self.lock.deref_mut() }
        }

        impl<T> Mutex<T> {
            pub fn new(inner: T) -> Mutex<T> { Mutex { inner: RefCell::new(inner) } }

            pub fn lock(&self) -> LockResult<MutexGuard<'_, T>> {
                Ok(MutexGuard { lock: self.inner.borrow_mut() })
            }
        }
    }

    #[cfg(all(not(feature = "std"), not(test)))]
    pub use alloc::{
        borrow::{Borrow, Cow, ToOwned},
        boxed::Box,
        collections::{vec_deque::VecDeque, BTreeMap, BTreeSet, BinaryHeap},
        rc, slice,
        string::{String, ToString},
        sync,
        vec::Vec,
    };
    #[cfg(any(feature = "std", test))]
    pub use std::{
        borrow::{Borrow, Cow, ToOwned},
        boxed::Box,
        collections::{vec_deque::VecDeque, BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet},
        rc, slice,
        string::{String, ToString},
        sync,
        sync::Mutex,
        vec::Vec,
    };

    #[cfg(all(not(feature = "std"), not(test)))]
    pub use self::mutex::Mutex;
}
