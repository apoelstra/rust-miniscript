// SPDX-License-Identifier: CC0-1.0

//!  Miniscript Analysis
//!
//! Tools for determining whether the guarantees offered by the library
//! actually hold.

use core::fmt;
#[cfg(feature = "std")]
use std::error;

use crate::prelude::*;
use crate::{Miniscript, MiniscriptKey, ScriptContext, Terminal};

/// Params for parsing miniscripts that either non-sane or non-specified(experimental) in the spec.
/// Used as a parameter [`Miniscript::from_str_ext`] and [`Miniscript::decode_with_ext`].
///
/// This allows parsing miniscripts if
/// 1. It is unsafe(does not require a digital signature to spend it)
/// 2. It contains a unspendable path because of either
///     1. Resource limitations
///     2. Timelock Mixing
/// 3. The script is malleable and thereby some of satisfaction weight
///    guarantees are not satisfied.
/// 4. It has repeated public keys
/// 5. raw pkh fragments without the pk. This could be obtained when parsing miniscript from script
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Hash)]
pub struct ExtParams {
    /// Allow parsing of non-safe miniscripts
    pub top_unsafe: bool,
    /// Allow parsing of miniscripts with unspendable paths
    pub resource_limitations: bool,
    /// Allow parsing of miniscripts with timelock mixing
    pub timelock_mixing: bool,
    /// Allow parsing of malleable miniscripts
    pub malleability: bool,
    /// Allow parsing of miniscripts with repeated public keys
    pub repeated_pk: bool,
    /// Allow parsing of miniscripts with raw pkh fragments without the pk.
    /// This could be obtained when parsing miniscript from script
    pub raw_pkh: bool,
}

impl ExtParams {
    /// Create a new ExtParams that with all the sanity rules
    pub fn new() -> ExtParams {
        ExtParams {
            top_unsafe: false,
            resource_limitations: false,
            timelock_mixing: false,
            malleability: false,
            repeated_pk: false,
            raw_pkh: false,
        }
    }

    /// Create a new ExtParams that allows all the sanity rules
    pub fn sane() -> ExtParams { ExtParams::new() }

    /// Create a new ExtParams that insanity rules
    /// This enables parsing well specified but "insane" miniscripts.
    /// Refer to the [`ExtParams`] documentation for more details on "insane" miniscripts.
    pub fn insane() -> ExtParams {
        ExtParams {
            top_unsafe: true,
            resource_limitations: true,
            timelock_mixing: true,
            malleability: true,
            repeated_pk: true,
            raw_pkh: false,
        }
    }

    /// Enable all non-sane rules and experimental rules
    pub fn allow_all() -> ExtParams {
        ExtParams {
            top_unsafe: true,
            resource_limitations: true,
            timelock_mixing: true,
            malleability: true,
            repeated_pk: true,
            raw_pkh: true,
        }
    }

    /// Builder that allows non-safe miniscripts.
    pub fn top_unsafe(mut self) -> ExtParams {
        self.top_unsafe = true;
        self
    }

    /// Builder that allows miniscripts with exceed resource limitations.
    pub fn exceed_resource_limitations(mut self) -> ExtParams {
        self.resource_limitations = true;
        self
    }

    /// Builder that allows miniscripts with timelock mixing.
    pub fn timelock_mixing(mut self) -> ExtParams {
        self.timelock_mixing = true;
        self
    }

    /// Builder that allows malleable miniscripts.
    pub fn malleability(mut self) -> ExtParams {
        self.malleability = true;
        self
    }

    /// Builder that allows miniscripts with repeated public keys.
    pub fn repeated_pk(mut self) -> ExtParams {
        self.repeated_pk = true;
        self
    }

    /// Builder that allows miniscripts with raw pkh fragments.
    pub fn raw_pkh(mut self) -> ExtParams {
        self.raw_pkh = true;
        self
    }
}

/// Possible reasons Miniscript guarantees can fail
/// We currently mark Miniscript as Non-Analyzable if
/// 1. It is unsafe(does not require a digital signature to spend it)
/// 2. It contains a unspendable path because of either
///     1. Resource limitations
///     2. Timelock Mixing
/// 3. The script is malleable and thereby some of satisfaction weight
///    guarantees are not satisfied.
/// 4. It has repeated publickeys
#[derive(Debug, PartialEq)]
pub enum AnalysisError {
    /// Top level is not safe.
    SiglessBranch,
    /// Repeated Pubkeys
    RepeatedPubkeys,
    /// Miniscript contains at least one path that exceeds resource limits
    BranchExceedResouceLimits,
    /// Contains a combination of heightlock and timelock
    HeightTimelockCombination,
    /// Malleable script
    Malleable,
    /// Contains partial descriptor raw pkh
    ContainsRawPkh,
}

impl fmt::Display for AnalysisError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AnalysisError::SiglessBranch => {
                f.write_str("All spend paths must require a signature")
            }
            AnalysisError::RepeatedPubkeys => {
                f.write_str("Miniscript contains repeated pubkeys or pubkeyhashes")
            }
            AnalysisError::BranchExceedResouceLimits => {
                f.write_str("At least one spend path exceeds the resource limits(stack depth/satisfaction size..)")
            }
            AnalysisError::HeightTimelockCombination => {
                f.write_str("Contains a combination of heightlock and timelock")
            }
            AnalysisError::Malleable => f.write_str("Miniscript is malleable"),
            AnalysisError::ContainsRawPkh => f.write_str("Miniscript contains raw pkh"),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for AnalysisError {
    fn cause(&self) -> Option<&dyn error::Error> {
        use self::AnalysisError::*;

        match self {
            SiglessBranch
            | RepeatedPubkeys
            | BranchExceedResouceLimits
            | HeightTimelockCombination
            | Malleable
            | ContainsRawPkh => None,
        }
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Miniscript<Pk, Ctx> {
    /// Whether all spend paths of miniscript require a signature
    pub fn requires_sig(&self) -> bool { self.ty.mall.safe }

    /// Whether the miniscript is malleable
    pub fn is_non_malleable(&self) -> bool { self.ty.mall.non_malleable }

    /// Whether the miniscript can exceed the resource limits(Opcodes, Stack limit etc)
    // It maybe possible to return a detail error type containing why the miniscript
    // failed. But doing so may require returning a collection of errors
    pub fn within_resource_limits(&self) -> bool { Ctx::check_local_validity(self).is_ok() }

    /// Whether the miniscript contains a combination of timelocks
    pub fn has_mixed_timelocks(&self) -> bool { self.ext.timelock_info.contains_unspendable_path() }

    /// Whether the miniscript has repeated Pk or Pkh
    pub fn has_repeated_keys(&self) -> bool {
        // Simple way to check whether all of these are correct is
        // to have an iterator
        let all_pkhs_len = self.iter_pk().count();

        let unique_pkhs_len = self.iter_pk().collect::<BTreeSet<_>>().len();

        unique_pkhs_len != all_pkhs_len
    }

    /// Whether the given miniscript contains a raw pkh fragment
    pub fn contains_raw_pkh(&self) -> bool {
        self.iter().any(|ms| matches!(ms.node, Terminal::RawPkH(_)))
    }

    /// Check whether the miniscript follows the given Extra policy [`ExtParams`]
    pub fn ext_check(&self, ext: &ExtParams) -> Result<(), AnalysisError> {
        if !ext.top_unsafe && !self.requires_sig() {
            Err(AnalysisError::SiglessBranch)
        } else if !ext.malleability && !self.is_non_malleable() {
            Err(AnalysisError::Malleable)
        } else if !ext.resource_limitations && !self.within_resource_limits() {
            Err(AnalysisError::BranchExceedResouceLimits)
        } else if !ext.repeated_pk && self.has_repeated_keys() {
            Err(AnalysisError::RepeatedPubkeys)
        } else if !ext.timelock_mixing && self.has_mixed_timelocks() {
            Err(AnalysisError::HeightTimelockCombination)
        } else if !ext.raw_pkh && self.contains_raw_pkh() {
            Err(AnalysisError::ContainsRawPkh)
        } else {
            Ok(())
        }
    }
}
