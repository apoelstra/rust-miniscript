// SPDX-License-Identifier: CC0-1.0

//! Satisfactions and dissatisfactions for individual Miniscript fragments.

use bitcoin::hashes::hash160;
use bitcoin::TapLeafHash;

use super::{Placeholder, Satisfaction, Witness};
use crate::plan::AssetProvider;
use crate::{AbsLockTime, MiniscriptKey, RelLockTime, ScriptContext, ToPublicKey};

impl<Pk: MiniscriptKey + ToPublicKey> Satisfaction<Placeholder<Pk>> {
    pub(super) const IMPOSSIBLE: Self = Self {
        stack: Witness::Impossible,
        has_sig: false,
        relative_timelock: None,
        absolute_timelock: None,
    };

    pub(super) const TRIVIAL: Self = Self {
        stack: Witness::empty(),
        has_sig: false,
        relative_timelock: None,
        absolute_timelock: None,
    };

    /// Constant that can't be `const` due to Rust limitations
    fn push_0() -> Self { Self { stack: Witness::push_0(), ..Self::TRIVIAL } }

    /// The (dissatisfaction, satisfaction) pair for a `pk_k` fragment.
    pub(super) fn pk_k<S, Ctx>(stfr: &S, pk: &Pk, leaf_hash: &TapLeafHash) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
        Ctx: ScriptContext,
    {
        (
            Self::push_0(),
            Self {
                stack: Witness::signature::<_, Ctx>(stfr, pk, leaf_hash),
                has_sig: true,
                ..Self::TRIVIAL
            },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for a `pk_h` fragment.
    pub(super) fn pk_h<S, Ctx>(stfr: &S, pk: &Pk, leaf_hash: &TapLeafHash) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
        Ctx: ScriptContext,
    {
        let wit = Witness::signature::<_, Ctx>(stfr, pk, leaf_hash);
        (
            Self {
                stack: Witness::combine(
                    Witness::push_0(),
                    Witness::Stack(vec![Placeholder::Pubkey(pk.clone(), Ctx::pk_len(pk))]),
                ),
                ..Self::TRIVIAL
            },
            Self {
                stack: Witness::combine(
                    wit,
                    Witness::Stack(vec![Placeholder::Pubkey(pk.clone(), Ctx::pk_len(pk))]),
                ),
                has_sig: true,
                ..Self::TRIVIAL
            },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for a `pk_h` fragment.
    pub(super) fn raw_pk_h<S, Ctx>(
        stfr: &S,
        pkh: &hash160::Hash,
        leaf_hash: &TapLeafHash,
    ) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
        Ctx: ScriptContext,
    {
        (
            Self {
                stack: Witness::combine(
                    Witness::push_0(),
                    Witness::pkh_public_key::<_, Ctx>(stfr, pkh),
                ),
                ..Self::TRIVIAL
            },
            Self {
                stack: Witness::pkh_signature::<_, Ctx>(stfr, pkh, leaf_hash),
                has_sig: true,
                ..Self::TRIVIAL
            },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for an `after` fragment.
    pub(super) fn after<S>(stfr: &S, t: AbsLockTime, root_has_sig: bool) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        let (stack, absolute_timelock) = if stfr.check_after(t.into()) {
            (Witness::empty(), Some(t))
        } else if root_has_sig {
            // If the root terminal has signature, the
            // signature covers the nLockTime and nSequence
            // values. The sender of the transaction should
            // take care that it signs the value such that the
            // timelock is not met
            (Witness::Impossible, None)
        } else {
            (Witness::Unavailable, None)
        };
        (
            Self::IMPOSSIBLE,
            Self { stack, has_sig: false, relative_timelock: None, absolute_timelock },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for an `older` fragment.
    pub(super) fn older<S>(stfr: &S, t: RelLockTime, root_has_sig: bool) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        let (stack, relative_timelock) = if stfr.check_older(t.into()) {
            (Witness::empty(), Some(t))
        } else if root_has_sig {
            // If the root terminal has signature, the
            // signature covers the nLockTime and nSequence
            // values. The sender of the transaction should
            // take care that it signs the value such that the
            // timelock is not met
            (Witness::Impossible, None)
        } else {
            (Witness::Unavailable, None)
        };
        (
            Self::IMPOSSIBLE,
            Self { stack, has_sig: false, relative_timelock, absolute_timelock: None },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for a `ripemd160` fragment.
    pub(super) fn ripemd160<S>(stfr: &S, h: &Pk::Ripemd160) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        (
            Self { stack: Witness::hash_dissatisfaction(), ..Self::TRIVIAL },
            Self { stack: Witness::ripemd160_preimage(stfr, h), ..Self::TRIVIAL },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for a `hash160` fragment.
    pub(super) fn hash160<S>(stfr: &S, h: &Pk::Hash160) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        (
            Self { stack: Witness::hash_dissatisfaction(), ..Self::TRIVIAL },
            Self { stack: Witness::hash160_preimage(stfr, h), ..Self::TRIVIAL },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for a `ripemd256` fragment.
    pub(super) fn sha256<S>(stfr: &S, h: &Pk::Sha256) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        (
            Self { stack: Witness::hash_dissatisfaction(), ..Self::TRIVIAL },
            Self { stack: Witness::sha256_preimage(stfr, h), ..Self::TRIVIAL },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for a `ripemd256` fragment.
    pub(super) fn hash256<S>(stfr: &S, h: &Pk::Hash256) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        (
            Self { stack: Witness::hash_dissatisfaction(), ..Self::TRIVIAL },
            Self { stack: Witness::hash256_preimage(stfr, h), ..Self::TRIVIAL },
        )
    }
}
