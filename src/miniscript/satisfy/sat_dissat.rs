// SPDX-License-Identifier: CC0-1.0

//! Satisfactions and dissatisfactions for individual Miniscript fragments.

use bitcoin::hashes::hash160;
use bitcoin::TapLeafHash;

use super::{Placeholder, Satisfaction, Witness};
use crate::miniscript::limits::{MAX_PUBKEYS_IN_CHECKSIGADD, MAX_PUBKEYS_PER_MULTISIG};
use crate::plan::AssetProvider;
use crate::prelude::*;
use crate::{AbsLockTime, MiniscriptKey, RelLockTime, ScriptContext, Threshold, ToPublicKey};

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

    /// The (dissatisfaction, satisfaction) pair for a `multi` fragment.
    pub(super) fn multi<S, Ctx>(
        stfr: &S,
        thresh: &Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>,
        leaf_hash: &TapLeafHash,
    ) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
        Ctx: ScriptContext,
    {
        let dissat = Self {
            stack: Witness::Stack(vec![Placeholder::PushZero; thresh.k() + 1]),
            ..Self::TRIVIAL
        };

        // Collect all available signatures
        let mut sig_count = 0;
        let mut sigs = Vec::with_capacity(thresh.k());
        for pk in thresh.data() {
            match Witness::signature::<_, Ctx>(stfr, pk, leaf_hash) {
                Witness::Stack(sig) => {
                    sigs.push(sig);
                    sig_count += 1;
                }
                Witness::Impossible => {}
                Witness::Unavailable => {
                    unreachable!("Signature satisfaction without witness must be impossible")
                }
            }
        }

        if sig_count < thresh.k() {
            (dissat, Self::IMPOSSIBLE)
        } else {
            // Throw away the most expensive ones
            for _ in 0..sig_count - thresh.k() {
                let max_idx = sigs
                    .iter()
                    .enumerate()
                    .max_by_key(|&(_, v)| v.len())
                    .unwrap()
                    .0;
                sigs[max_idx] = vec![];
            }

            (
                dissat,
                Self {
                    stack: sigs.into_iter().fold(Witness::push_0(), |acc, sig| {
                        Witness::combine(acc, Witness::Stack(sig))
                    }),
                    has_sig: true,
                    ..Self::TRIVIAL
                },
            )
        }
    }

    /// The (dissatisfaction, satisfaction) pair for a `multi` fragment.
    pub(super) fn multi_a<S, Ctx>(
        stfr: &S,
        thresh: &Threshold<Pk, MAX_PUBKEYS_IN_CHECKSIGADD>,
        leaf_hash: &TapLeafHash,
    ) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
        Ctx: ScriptContext,
    {
        let dissat = Self {
            stack: Witness::Stack(vec![Placeholder::PushZero; thresh.n()]),
            ..Self::TRIVIAL
        };

        // Collect all available signatures
        let mut sig_count = 0;
        let mut sigs = vec![vec![Placeholder::PushZero]; thresh.n()];
        for (i, pk) in thresh.iter().rev().enumerate() {
            match Witness::signature::<_, Ctx>(stfr, pk, leaf_hash) {
                Witness::Stack(sig) => {
                    sigs[i] = sig;
                    sig_count += 1;
                    // This a privacy issue, we are only selecting the first available
                    // sigs. Incase pk at pos 1 is not selected, we know we did not have access to it
                    // bitcoin core also implements the same logic for MULTISIG, so I am not bothering
                    // permuting the sigs for now
                    if sig_count == thresh.k() {
                        break;
                    }
                }
                Witness::Impossible => {}
                Witness::Unavailable => {
                    unreachable!("Signature satisfaction without witness must be impossible")
                }
            }
        }

        if sig_count < thresh.k() {
            (dissat, Self::IMPOSSIBLE)
        } else {
            (
                dissat,
                Self {
                    stack: sigs.into_iter().fold(Witness::empty(), |acc, sig| {
                        Witness::combine(acc, Witness::Stack(sig))
                    }),
                    has_sig: true,
                    ..Self::TRIVIAL
                },
            )
        }
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
