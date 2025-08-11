// SPDX-License-Identifier: CC0-1.0

//! Satisfactions and dissatisfactions for individual Miniscript fragments.

use bitcoin::TapLeafHash;

use super::{Placeholder, Satisfaction, Witness};
use crate::plan::AssetProvider;
use crate::{MiniscriptKey, ScriptContext, ToPublicKey};

impl<Pk: MiniscriptKey + ToPublicKey> Satisfaction<Placeholder<Pk>> {
    /// The (dissatisfaction, satisfaction) pair for a `pk_k` fragment.
    pub(super) fn pk_k<S, Ctx>(stfr: &S, pk: &Pk, leaf_hash: &TapLeafHash) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
        Ctx: ScriptContext,
    {
        (
            Self {
                stack: Witness::push_0(),
                has_sig: false,
                relative_timelock: None,
                absolute_timelock: None,
            },
            Self {
                stack: Witness::signature::<_, Ctx>(stfr, pk, leaf_hash),
                has_sig: true,
                relative_timelock: None,
                absolute_timelock: None,
            },
        )
    }
}
