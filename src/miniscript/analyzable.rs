// SPDX-License-Identifier: CC0-1.0

//!  Miniscript Analysis
//!
//! Tools for determining whether the guarantees offered by the library
//! actually hold.

use crate::prelude::*;
use crate::{Miniscript, MiniscriptKey, ScriptContext, Terminal};

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Miniscript<Pk, Ctx> {
    /// Whether all spend paths of miniscript require a signature
    pub fn requires_sig(&self) -> bool { self.ty.mall.safe }

    /// Whether the miniscript is malleable
    pub fn is_non_malleable(&self) -> bool { self.ty.mall.non_malleable }

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
}
