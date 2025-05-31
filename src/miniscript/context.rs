// Written in 2019 by Sanket Kanjalkar and Andrew Poelstra
// SPDX-License-Identifier: CC0-1.0

use core::{fmt, hash};

use crate::miniscript::limits::{
    MAX_OPS_PER_SCRIPT, MAX_SCRIPT_ELEMENT_SIZE, MAX_SCRIPT_SIZE, MAX_STACK_SIZE,
    MAX_STANDARD_P2WSH_SCRIPT_SIZE, MAX_STANDARD_P2WSH_STACK_ITEMS,
};
use crate::{Miniscript, MiniscriptKey, ValidationParams};

/// The ScriptContext for Miniscript.
///
/// Additional type information associated with
/// miniscript that is used for carrying out checks that dependent on the
/// context under which the script is used.
/// For example, disallowing uncompressed keys in Segwit context
pub trait ScriptContext:
    fmt::Debug + Clone + Ord + PartialOrd + Eq + PartialEq + hash::Hash + private::Sealed + 'static
{
    /// The validation parameters enforcing consensus limits in this context, and
    /// nothing further.
    const CONSENSUS: ValidationParams;

    /// Sensible validation parameters for this context. Unless you have a good reason
    /// to choose otherwise, these are the validation parameters you want.
    ///
    /// They are also the validation parameters used throughout this library when no
    /// explicit choice of parameters is made.
    const SANE: ValidationParams;

    /// Depending on script context, the size of a satifaction witness may slightly differ.
    fn max_satisfaction_size<Pk: MiniscriptKey>(ms: &Miniscript<Pk, Self>) -> Option<usize>;

    /// The type of signature required for satisfaction
    // We need to context decide whether the serialize pk to 33 byte or 32 bytes.
    // And to decide which type of signatures to look for during satisfaction
    fn sig_type() -> SigType;

    /// Get the len of public key when serialized based on context
    /// Note that this includes the serialization prefix. Returns
    /// 34/66 for Bare/Legacy based on key compressedness
    /// 34 for Segwitv0, 33 for Tap
    fn pk_len<Pk: MiniscriptKey>(pk: &Pk) -> usize;

    /// Local helper function to display error messages with context
    fn name_str() -> &'static str;
}

/// Signature algorithm type
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum SigType {
    /// Ecdsa signature
    Ecdsa,
    /// Schnorr Signature
    Schnorr,
}

/// Legacy ScriptContext
/// To be used as P2SH scripts
/// For creation of Bare scriptpubkeys, construct the Miniscript
/// under `Bare` ScriptContext
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Legacy {}

impl ScriptContext for Legacy {
    const CONSENSUS: ValidationParams = ValidationParams {
        allow_compressed_keys: true,
        allow_dup_if: false,
        allow_uncompressed_keys: true,
        allow_multi_a: false,
        allow_or_i: false,
        allow_x_only_keys: false,
        max_opcode_count: MAX_OPS_PER_SCRIPT,
        max_script_size: MAX_SCRIPT_ELEMENT_SIZE,
        ..ValidationParams::CONSENSUS
    };
    const SANE: ValidationParams = Self::CONSENSUS.intersect(&ValidationParams::SANE);

    fn max_satisfaction_size<Pk: MiniscriptKey>(ms: &Miniscript<Pk, Self>) -> Option<usize> {
        ms.ext.sat_data.map(|data| data.max_script_sig_size)
    }

    fn pk_len<Pk: MiniscriptKey>(pk: &Pk) -> usize {
        if pk.is_uncompressed() {
            66
        } else {
            34
        }
    }

    fn name_str() -> &'static str { "Legacy/p2sh" }

    fn sig_type() -> SigType { SigType::Ecdsa }
}

/// Segwitv0 ScriptContext
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Segwitv0 {}

impl ScriptContext for Segwitv0 {
    const CONSENSUS: ValidationParams = ValidationParams {
        allow_compressed_keys: true,
        allow_uncompressed_keys: false,
        allow_multi_a: false,
        allow_x_only_keys: false,
        max_opcode_count: MAX_OPS_PER_SCRIPT,
        max_exec_stack_size: MAX_STACK_SIZE,
        ..ValidationParams::CONSENSUS
    };
    const SANE: ValidationParams = ValidationParams {
        max_script_size: MAX_STANDARD_P2WSH_SCRIPT_SIZE,
        max_witness_items: MAX_STANDARD_P2WSH_STACK_ITEMS,
        ..Self::CONSENSUS.intersect(&ValidationParams::SANE)
    };

    fn max_satisfaction_size<Pk: MiniscriptKey>(ms: &Miniscript<Pk, Self>) -> Option<usize> {
        ms.ext.sat_data.map(|data| data.max_witness_stack_size)
    }

    fn pk_len<Pk: MiniscriptKey>(_pk: &Pk) -> usize { 34 }

    fn name_str() -> &'static str { "Segwitv0" }

    fn sig_type() -> SigType { SigType::Ecdsa }
}

/// Tap ScriptContext
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Tap {}

impl ScriptContext for Tap {
    const CONSENSUS: ValidationParams = ValidationParams {
        allow_compressed_keys: false,
        allow_uncompressed_keys: false,
        allow_multi: false,
        allow_x_only_keys: true,
        ..ValidationParams::CONSENSUS
    };
    const SANE: ValidationParams = ValidationParams {
        max_script_size: MAX_STANDARD_P2WSH_SCRIPT_SIZE,
        max_witness_items: MAX_STANDARD_P2WSH_STACK_ITEMS,
        ..Self::CONSENSUS.intersect(&ValidationParams::SANE)
    };

    fn max_satisfaction_size<Pk: MiniscriptKey>(ms: &Miniscript<Pk, Self>) -> Option<usize> {
        ms.ext.sat_data.map(|data| data.max_witness_stack_size)
    }

    fn sig_type() -> SigType { SigType::Schnorr }

    fn pk_len<Pk: MiniscriptKey>(_pk: &Pk) -> usize { 33 }

    fn name_str() -> &'static str { "TapscriptCtx" }
}

/// Bare ScriptContext
/// To be used as raw script pubkeys
/// In general, it is not recommended to use Bare descriptors
/// as they as strongly limited by standardness policies.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum BareCtx {}

impl ScriptContext for BareCtx {
    const CONSENSUS: ValidationParams = ValidationParams {
        allow_compressed_keys: true,
        allow_dup_if: false,
        allow_uncompressed_keys: true,
        allow_multi_a: false,
        allow_or_i: false,
        allow_x_only_keys: false,
        max_opcode_count: MAX_OPS_PER_SCRIPT,
        max_script_size: MAX_SCRIPT_SIZE,
        ..ValidationParams::CONSENSUS
    };
    const SANE: ValidationParams = Self::CONSENSUS.intersect(&ValidationParams::SANE);

    fn max_satisfaction_size<Pk: MiniscriptKey>(ms: &Miniscript<Pk, Self>) -> Option<usize> {
        // For bare outputs the script appears in the scriptpubkey; its cost
        // is the same as for a legacy scriptsig.
        ms.ext.sat_data.map(|data| data.max_script_sig_size)
    }

    fn pk_len<Pk: MiniscriptKey>(pk: &Pk) -> usize {
        if pk.is_uncompressed() {
            66
        } else {
            34
        }
    }

    fn name_str() -> &'static str { "BareCtx" }

    fn sig_type() -> SigType { SigType::Ecdsa }
}

/// "No Checks Ecdsa" Context
///
/// Used by the "satisified constraints" iterator, which is intended to read
/// scripts off of the blockchain without doing any sanity checks on them.
/// This context should *NOT* be used unless you know what you are doing.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum NoChecks {}
impl ScriptContext for NoChecks {
    // todo: When adding support for interpreter, we need a enum with all supported keys here
    const CONSENSUS: ValidationParams = ValidationParams::MAX;
    const SANE: ValidationParams = ValidationParams::MAX;

    fn max_satisfaction_size<Pk: MiniscriptKey>(_ms: &Miniscript<Pk, Self>) -> Option<usize> {
        panic!("Tried to compute a satisfaction size bound on a no-checks ecdsa miniscript")
    }

    fn pk_len<Pk: MiniscriptKey>(_pk: &Pk) -> usize {
        panic!("Tried to compute a pk len bound on a no-checks ecdsa miniscript")
    }

    fn name_str() -> &'static str {
        // Internally used code
        "NochecksEcdsa"
    }

    fn sig_type() -> SigType { SigType::Ecdsa }
}

/// Private Mod to prevent downstream from implementing this public trait
mod private {
    use super::{BareCtx, Legacy, NoChecks, Segwitv0, Tap};

    pub trait Sealed {}

    // Implement for those same types, but no others.
    impl Sealed for BareCtx {}
    impl Sealed for Legacy {}
    impl Sealed for Segwitv0 {}
    impl Sealed for Tap {}
    impl Sealed for NoChecks {}
}
