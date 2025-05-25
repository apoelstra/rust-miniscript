// SPDX-License-Identifier: CC0-1.0

//! Validation Parameters
//!
//! Settings for determining what a "valid" Miniscript is.

use core::fmt;
#[cfg(feature = "std")]
use std::error;

use crate::prelude::{String, ToString as _};

/// Validation Parameters
#[non_exhaustive]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValidationParams {
    /// Allow compressed 33-byte keys.
    pub allow_compressed_keys: bool,
    /// Allow duplicate public keys in the script.
    pub allow_duplicate_keys: bool,
    /// Allow the `d:` fragment. (Disallowed pre-segwit because minimality is not enforced.)
    pub allow_dup_if: bool,
    /// Allow scripts with 3rd-party malleability vectors.
    pub allow_malleability: bool,
    /// Allow the `multi` fragment. (This allowed only pre-Taproot.)
    pub allow_multi: bool,
    /// Allow the `multi_a` fragment. (This allowed only post-Taproot.)
    pub allow_multi_a: bool,
    /// Allow mixing of height-based and time-based timelocks in a given script.
    pub allow_mixed_time_locks: bool,
    /// Allow the `or_i` fragment. (Disallowed pre-segwit because minimality is not enforced.)
    pub allow_or_i: bool,
    /// Allow the `expr_raw_pkh` fragment.
    pub allow_raw_pkh: bool,
    /// Allow branches without any signatures (this property is referred to as `hassig`
    /// in the Miniscript specification, and in very old documentation as "safety").
    pub allow_sigless_branch: bool,
    /// Allow scripts that don't have the "B" type, i.e. which are not valid scripts
    /// on their own.
    pub allow_non_b: bool,
    /// Allow 65-byte uncompressed and hybrid keys.
    pub allow_uncompressed_keys: bool,
    /// Allow unsatisfiable programs.
    pub allow_unsatisfiable: bool,
    /// Allow 32-byte x-only keys.
    pub allow_x_only_keys: bool,
    /// Allow multipath keys with inconsistent lengths.
    pub allow_inconsistent_multipath_keys: bool,
    /// Maximum number of non-push opcodes executed in any branch.
    pub max_opcode_count: usize,
    /// Maximum size of the encoded script.
    ///
    /// Depending on context, a Miniscript may be embedded in a Taproot leaf, a segwit
    /// witness script, a P2SH redeem script, a bare `scriptPubKey`, or possibly some
    /// future thing. This limit describes how many bytes it may be encoded as, *not*
    /// including any length prefix bytes.
    pub max_script_size: usize,
    /// Maximum number of witness stack items.
    pub max_witness_items: usize,
    /// Maximum number of stack elements during script execution.
    pub max_exec_stack_size: usize,
    /// Maximum recursive depth allowed in the Miniscript tree.
    ///
    /// This value is a limitation of the library; it is not related to the maximum depth
    /// of Taproot trees (which is enforced elsewhere) or anything else. We hope to relax
    /// it in the future once we have eliminated all recursive structures from the library.
    ///
    /// See <https://github.com/sipa/miniscript/pull/5> for some history of this limit.
    pub max_recursive_depth: usize,
}

impl ValidationParams {
    /// A set of parameters representing "anything goes".
    pub const MAX: Self = Self {
        allow_compressed_keys: true,
        allow_duplicate_keys: true,
        allow_dup_if: true,
        allow_malleability: true,
        allow_mixed_time_locks: true,
        allow_multi: true,
        allow_multi_a: true,
        allow_or_i: true,
        allow_raw_pkh: true,
        allow_sigless_branch: true,
        allow_non_b: true,
        allow_uncompressed_keys: true,
        allow_unsatisfiable: true,
        allow_x_only_keys: true,
        allow_inconsistent_multipath_keys: true,
        max_opcode_count: usize::MAX,
        max_script_size: usize::MAX,
        max_witness_items: usize::MAX,
        max_exec_stack_size: usize::MAX,
        max_recursive_depth: 402, // https://github.com/sipa/miniscript/pull/5
    };

    /// Enforce a basic set of sanity checks.
    ///
    /// These limitations are those that apply to _all_ contexts. So, for example, `multi_a`
    /// is allowed by this constant, and no size/opcode limits are enforced. You likely want
    /// to use a context-specific constant such as [`SEGWIT_V0`] or [`TAPROOT`] rather than
    /// this constant.
    pub const SANE: Self = Self {
        allow_compressed_keys: true,
        allow_duplicate_keys: false,
        allow_dup_if: true,
        allow_malleability: false,
        allow_mixed_time_locks: false,
        allow_multi: true,
        allow_multi_a: true,
        allow_or_i: true,
        allow_raw_pkh: false,
        allow_sigless_branch: false,
        allow_non_b: false,
        allow_uncompressed_keys: true,
        // FIXME should make allow_unsatisfiable false, but for compatibility
        // with existing code we leave it as true even for "sane" scripts.
        allow_unsatisfiable: true,
        allow_x_only_keys: true,
        allow_inconsistent_multipath_keys: false,
        max_opcode_count: usize::MAX,
        max_script_size: usize::MAX,
        max_witness_items: usize::MAX,
        max_exec_stack_size: usize::MAX,
        max_recursive_depth: Self::MAX.max_recursive_depth,
    };

    /// Enforce a bare minimum set of sanity checks.
    ///
    /// This includes any consensus limits that Miniscript understands, and
    /// forbids unsatisfiable programs. If you really want to parse anything
    /// that can be parsed, use [`Self::MAX`] instead.
    pub const CONSENSUS: Self = Self {
        allow_compressed_keys: true,
        allow_duplicate_keys: true,
        allow_dup_if: true,
        allow_malleability: true,
        allow_mixed_time_locks: true,
        allow_multi: true,
        allow_multi_a: true,
        allow_or_i: true,
        allow_raw_pkh: false,
        allow_sigless_branch: true,
        allow_non_b: false,
        allow_uncompressed_keys: true,
        // FIXME see above; we should forbid unsatisfiable programs
        allow_unsatisfiable: true,
        allow_x_only_keys: true,
        allow_inconsistent_multipath_keys: true,
        max_opcode_count: usize::MAX,
        max_script_size: usize::MAX,
        max_witness_items: usize::MAX,
        max_exec_stack_size: usize::MAX,
        max_recursive_depth: Self::MAX.max_recursive_depth,
    };

    /// Whether this set of parameters is equal to another.
    ///
    /// Defined as an explicit method to get `const`.
    pub const fn eq(&self, other: &Self) -> bool {
        self.allow_compressed_keys == other.allow_compressed_keys
            && self.allow_duplicate_keys == other.allow_duplicate_keys
            && self.allow_dup_if == other.allow_dup_if
            && self.allow_malleability == other.allow_malleability
            && self.allow_mixed_time_locks == other.allow_mixed_time_locks
            && self.allow_multi == other.allow_multi
            && self.allow_multi_a == other.allow_multi_a
            && self.allow_or_i == other.allow_or_i
            && self.allow_raw_pkh == other.allow_raw_pkh
            && self.allow_sigless_branch == other.allow_sigless_branch
            && self.allow_non_b == other.allow_non_b
            && self.allow_uncompressed_keys == other.allow_uncompressed_keys
            && self.allow_unsatisfiable == other.allow_unsatisfiable
            && self.allow_x_only_keys == other.allow_x_only_keys
            && self.allow_inconsistent_multipath_keys == other.allow_inconsistent_multipath_keys
            && self.max_opcode_count == other.max_opcode_count
            && self.max_script_size == other.max_script_size
            && self.max_witness_items == other.max_witness_items
            && self.max_exec_stack_size == other.max_exec_stack_size
            && self.max_recursive_depth == other.max_recursive_depth
    }

    /// Whether a script satisfying this set of parameters must also satisfy the
    /// other set of parameters.
    pub const fn entails(&self, other: &Self) -> bool { self.intersect(other).eq(self) }

    /// Computes the intersection of two sets of validation parameters.
    ///
    /// The "intersection" is as restrictive as both of them. Alternately, it is the
    /// least restrictive set of parameters which nonetheless entails both.
    pub const fn intersect(&self, other: &Self) -> Self {
        ValidationParams {
            allow_compressed_keys: self.allow_compressed_keys && other.allow_compressed_keys,
            allow_duplicate_keys: self.allow_duplicate_keys && other.allow_duplicate_keys,
            allow_dup_if: self.allow_dup_if && other.allow_dup_if,
            allow_malleability: self.allow_malleability && other.allow_malleability,
            allow_mixed_time_locks: self.allow_mixed_time_locks && other.allow_mixed_time_locks,
            allow_multi: self.allow_multi && other.allow_multi,
            allow_multi_a: self.allow_multi_a && other.allow_multi_a,
            allow_or_i: self.allow_or_i && other.allow_or_i,
            allow_raw_pkh: self.allow_raw_pkh && other.allow_raw_pkh,
            allow_sigless_branch: self.allow_sigless_branch && other.allow_sigless_branch,
            allow_non_b: self.allow_non_b && other.allow_non_b,
            allow_uncompressed_keys: self.allow_uncompressed_keys && other.allow_uncompressed_keys,
            allow_unsatisfiable: self.allow_unsatisfiable && other.allow_unsatisfiable,
            allow_x_only_keys: self.allow_x_only_keys && other.allow_x_only_keys,
            allow_inconsistent_multipath_keys: self.allow_inconsistent_multipath_keys
                && other.allow_inconsistent_multipath_keys,
            // cannot use cmp::min in const ctx
            max_opcode_count: if self.max_opcode_count < other.max_opcode_count {
                self.max_opcode_count
            } else {
                other.max_opcode_count
            },
            max_script_size: if self.max_script_size < other.max_script_size {
                self.max_script_size
            } else {
                other.max_script_size
            },
            max_witness_items: if self.max_witness_items < other.max_witness_items {
                self.max_witness_items
            } else {
                other.max_witness_items
            },
            max_exec_stack_size: if self.max_exec_stack_size < other.max_exec_stack_size {
                self.max_exec_stack_size
            } else {
                other.max_exec_stack_size
            },
            max_recursive_depth: if self.max_recursive_depth < other.max_recursive_depth {
                self.max_recursive_depth
            } else {
                other.max_recursive_depth
            },
        }
    }

    /// Computes the union of two sets of validation parameters.
    ///
    /// The "union" is as non-restrictive as both of them. Alternately, it is the
    /// most restrictive set of parameters which nonetheless is entailed by both.
    pub const fn union(&self, other: &Self) -> Self {
        ValidationParams {
            allow_compressed_keys: self.allow_compressed_keys || other.allow_compressed_keys,
            allow_duplicate_keys: self.allow_duplicate_keys || other.allow_duplicate_keys,
            allow_dup_if: self.allow_dup_if || other.allow_dup_if,
            allow_malleability: self.allow_malleability || other.allow_malleability,
            allow_mixed_time_locks: self.allow_mixed_time_locks || other.allow_mixed_time_locks,
            allow_multi: self.allow_multi || other.allow_multi,
            allow_multi_a: self.allow_multi_a || other.allow_multi_a,
            allow_or_i: self.allow_or_i || other.allow_or_i,
            allow_raw_pkh: self.allow_raw_pkh || other.allow_raw_pkh,
            allow_sigless_branch: self.allow_sigless_branch || other.allow_sigless_branch,
            allow_non_b: self.allow_non_b || other.allow_non_b,
            allow_uncompressed_keys: self.allow_uncompressed_keys || other.allow_uncompressed_keys,
            allow_unsatisfiable: self.allow_unsatisfiable || other.allow_unsatisfiable,
            allow_x_only_keys: self.allow_x_only_keys || other.allow_x_only_keys,
            allow_inconsistent_multipath_keys: self.allow_inconsistent_multipath_keys
                || other.allow_inconsistent_multipath_keys,
            // cannot use cmp::max in const ctx
            max_opcode_count: if self.max_opcode_count > other.max_opcode_count {
                self.max_opcode_count
            } else {
                other.max_opcode_count
            },
            max_script_size: if self.max_script_size > other.max_script_size {
                self.max_script_size
            } else {
                other.max_script_size
            },
            max_witness_items: if self.max_witness_items > other.max_witness_items {
                self.max_witness_items
            } else {
                other.max_witness_items
            },
            max_exec_stack_size: if self.max_exec_stack_size > other.max_exec_stack_size {
                self.max_exec_stack_size
            } else {
                other.max_exec_stack_size
            },
            max_recursive_depth: if self.max_recursive_depth > other.max_recursive_depth {
                self.max_recursive_depth
            } else {
                other.max_recursive_depth
            },
        }
    }

    /// Validates a single key against the validation parameters.
    pub fn validate_pk<Pk>(&self, key: &Pk) -> Result<(), KeyError>
    where
        Pk: crate::MiniscriptKey,
    {
        // Compressed keys are allowed if -either- compressed keys or x-only keys are allowed:
        // for purposes of validating a constructed Miniscript, we treat compressed keys as
        // x-only ones, and when encoding them we will just drop their parity. (When decoding
        // a Miniscript from Script, we are strict and do not allow compressed keys in place
        // of x-only ones. But there we have explicit logic, rather than using this function
        // for rejection.)
        if !self.allow_compressed_keys
            && !self.allow_x_only_keys
            && !key.is_uncompressed()
            && !key.is_x_only_key()
        {
            return Err(KeyError::IllegalCompressedKey(key.to_string()));
        }
        if !self.allow_uncompressed_keys && key.is_uncompressed() {
            return Err(KeyError::IllegalUncompressedKey(key.to_string()));
        }
        if !self.allow_x_only_keys && key.is_x_only_key() {
            return Err(KeyError::IllegalXOnlyKey(key.to_string()));
        }
        Ok(())
    }
}

/// A validation error
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Error {
    /// Script had duplicate public keys.
    DuplicateKeys,
    /// Script had a `d:` fragment in a context it was not allowed.
    IllegalDupIf,
    /// Taproot script had a `multi` fragment
    IllegalMulti,
    /// Non-Taproot script had a `multi_a` fragment
    IllegalMultiA,
    /// Script had a `or_i` fragment in a context it was not allowed.
    IllegalOrI,
    /// Script contains an `expr_raw_pkh` fragment.
    IllegalRawPkh,
    /// Malleable script
    Malleable,
    /// At least one satisfaction path executes more than the allowable number of
    /// non-push opcodes.
    #[allow(missing_docs)]
    MaxOpCountExceeded { actual: usize, limit: usize },
    /// The script exceeds the maximum allowable script size.
    #[allow(missing_docs)]
    MaxScriptSizeExceeded { actual: usize, limit: usize },
    /// At least one satisfaction path has more than the allowable number of initial
    /// witness stack elements.
    #[allow(missing_docs)]
    MaxWitnessItemsExceeded { actual: usize, limit: usize },
    /// At least one satisfaction path requires more than the allowable number of elements
    /// to be on the stack.
    #[allow(missing_docs)]
    MaxExecStackSizeExceeded { actual: usize, limit: usize },
    /// A script exceeded the maximum allowable recursive depth for a Miniscript tree.
    ///
    /// This error triggers as soon as the limit is exceeded, so we do not know the actual
    /// depth of the script, only that it is in excess of the limit.
    #[allow(missing_docs)]
    MaxRecursiveDepthExceeded { limit: usize },
    /// Script had a branch which required a height-based and time-based timelock simultaneously.
    MixedTimeLocks,
    /// Two multipath keys were present, which had a different number of lengths.
    #[allow(missing_docs)]
    MultipathKeyLenMismatch { len1: usize, len2: usize },
    /// Top-level script did not have the "B" type, i.e. it is not valid as a standalone script.
    NonBase(crate::miniscript::types::Base),
    /// Script contains some branch that does not require any signatures.
    ///
    /// This is both directly dangerous (it likely indicates an "anyone-can-spend" output)
    /// and presents a malleability vector, since it allows 3rd parties to modify parts of
    /// the transaction such as locktimes or sequence numbers.
    SiglessBranch,
    /// Illegal key type (e.g. x-only key outside of Taproot).
    Key(KeyError),
    /// The Miniscript cannot be satisfied.
    Unsatisfiable,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::DuplicateKeys => f.write_str("duplicate public keys"),
            Error::IllegalDupIf => f.write_str("legacy script with a `dup_if` fragment"),
            Error::IllegalMulti => f.write_str("non-Taproot script with a `multi_a` fragment"),
            Error::IllegalMultiA => f.write_str("non-Taproot script with a `multi_a` fragment"),
            Error::IllegalOrI => f.write_str("legacy script with a `or_i` fragment"),
            Error::IllegalRawPkh => f.write_str("script with a `expr_raw_pkh` fragment"),
            Error::Malleable => f.write_str("script has a 3rd-party malleability vector"),
            Error::MaxOpCountExceeded { actual, limit } => write!(
                f,
                "a satisfaction path executes at least {} non-push opcodes (limit: {}).",
                actual, limit
            ),
            Error::MaxScriptSizeExceeded { actual, limit } => write!(
                f,
                "script has size at least {} (limit: {}).",
                actual, limit
            ),
            Error::MaxWitnessItemsExceeded { actual, limit } => write!(
                f,
                "a satisfaction path requires at least {} witness items (limit: {}).",
                actual, limit
            ),
            Error::MaxExecStackSizeExceeded { actual, limit } => write!(
                f,
                "a satisfaction path requires at least {} items on the stack at once (limit: {}).",
                actual, limit
            ),
            Error::MaxRecursiveDepthExceeded { limit } => write!(
                f,
                "script exceeded the maximum recursive depth limit of {}; if you have a use case for deeper scripts, please file an issue against rust-miniscript",
                limit
            ),
            Error::MixedTimeLocks => f.write_str("mixed a height-based and time-based timelock"),
            Error::MultipathKeyLenMismatch { len1, len2 } => write!(f, "found multipath keys with lengths {} and {}; lengths must match", len1, len2),
            Error::NonBase(base) => write!(f, "script has type {:?}, which is not allowed for a top-level Miniscript", base),
            Error::SiglessBranch => f.write_str("all spending paths must require a signature"),
            Error::Key(ref e) => e.fmt(f),
            Error::Unsatisfiable => f.write_str("no satisfaction exists for script"),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            Self::Key(ref e) => Some(e),
            _ => None,
        }
    }
}

impl From<KeyError> for Error {
    fn from(k: KeyError) -> Self { Self::Key(k) }
}

/// A validation error
#[allow(clippy::enum_variant_names)] // clippy doesn't like the Illegal* prefix
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum KeyError {
    /// A compressed key appeared in a context it was not allowed.
    IllegalCompressedKey(String),
    /// An uncompressed key appeared in a context it was not allowed.
    IllegalUncompressedKey(String),
    /// An x-only key appeared in a context it was not allowed.
    IllegalXOnlyKey(String),
}

impl fmt::Display for KeyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::IllegalCompressedKey(ref s) => write!(f, "compressed key `{}` not allowed", s),
            Self::IllegalUncompressedKey(ref s) => write!(f, "compressed key `{}` not allowed", s),
            Self::IllegalXOnlyKey(ref s) => write!(f, "compressed key `{}` not allowed", s),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for KeyError {
    fn cause(&self) -> Option<&dyn error::Error> { None }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entailment() {
        assert!(ValidationParams::SANE.entails(&ValidationParams::CONSENSUS));
        assert!(!ValidationParams::CONSENSUS.entails(&ValidationParams::SANE));
    }
}
