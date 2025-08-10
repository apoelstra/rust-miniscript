// SPDX-License-Identifier: CC0-1.0

//! Satisfactions and dissatisfactions for individual Miniscript fragments.

use bitcoin::hashes::hash160;
use bitcoin::TapLeafHash;

use super::{Placeholder, Satisfaction, Witness};
use crate::iter::TreeLike;
use crate::miniscript::limits::{MAX_PUBKEYS_IN_CHECKSIGADD, MAX_PUBKEYS_PER_MULTISIG};
use crate::plan::AssetProvider;
use crate::prelude::*;
use crate::{
    AbsLockTime, Miniscript, MiniscriptKey, RelLockTime, ScriptContext, Terminal, Threshold,
    ToPublicKey,
};

impl<Pk: MiniscriptKey + ToPublicKey> Satisfaction<Placeholder<Pk>> {
    const IMPOSSIBLE: Self = Self {
        stack: Witness::Impossible,
        has_sig: false,
        relative_timelock: None,
        absolute_timelock: None,
    };

    const TRIVIAL: Self = Self {
        stack: Witness::empty(),
        has_sig: false,
        relative_timelock: None,
        absolute_timelock: None,
    };

    /// Constant that can't be `const` due to Rust limitations
    fn push_0() -> Self { Self { stack: Witness::push_0(), ..Self::TRIVIAL } }

    /// The (dissatisfaction, satisfaction) pair for a `pk_k` fragment.
    fn pk_k<S>(stfr: &S, pk: &Pk, leaf_hash: Option<TapLeafHash>) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        (
            Self::push_0(),
            Self { stack: Witness::signature(stfr, pk, leaf_hash), has_sig: true, ..Self::TRIVIAL },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for a `pk_h` fragment.
    fn pk_h<S, Ctx>(stfr: &S, pk: &Pk, leaf_hash: Option<TapLeafHash>) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
        Ctx: ScriptContext,
    {
        let wit = Witness::signature(stfr, pk, leaf_hash);
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
    fn raw_pk_h<S, Ctx>(
        stfr: &S,
        pkh: &hash160::Hash,
        leaf_hash: Option<TapLeafHash>,
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
    fn multi<S>(stfr: &S, thresh: &Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        let dissat = Self {
            stack: Witness::Stack(vec![Placeholder::PushZero; thresh.k() + 1]),
            ..Self::TRIVIAL
        };

        // Collect all available signatures
        let mut sig_count = 0;
        let mut sigs = Vec::with_capacity(thresh.k());
        for pk in thresh.data() {
            match Witness::signature(stfr, pk, None) {
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
    fn multi_a<S>(
        stfr: &S,
        thresh: &Threshold<Pk, MAX_PUBKEYS_IN_CHECKSIGADD>,
        leaf_hash: TapLeafHash,
    ) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        let dissat = Self {
            stack: Witness::Stack(vec![Placeholder::PushZero; thresh.n()]),
            ..Self::TRIVIAL
        };

        // Collect all available signatures
        let mut sig_count = 0;
        let mut sigs = vec![vec![Placeholder::PushZero]; thresh.n()];
        for (i, pk) in thresh.iter().rev().enumerate() {
            match Witness::signature(stfr, pk, Some(leaf_hash)) {
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
    fn after<S>(stfr: &S, t: AbsLockTime, root_has_sig: bool) -> (Self, Self)
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
    fn older<S>(stfr: &S, t: RelLockTime, root_has_sig: bool) -> (Self, Self)
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
    fn ripemd160<S>(stfr: &S, h: &Pk::Ripemd160) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        (
            Self { stack: Witness::hash_dissatisfaction(), ..Self::TRIVIAL },
            Self { stack: Witness::ripemd160_preimage(stfr, h), ..Self::TRIVIAL },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for a `hash160` fragment.
    fn hash160<S>(stfr: &S, h: &Pk::Hash160) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        (
            Self { stack: Witness::hash_dissatisfaction(), ..Self::TRIVIAL },
            Self { stack: Witness::hash160_preimage(stfr, h), ..Self::TRIVIAL },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for a `ripemd256` fragment.
    fn sha256<S>(stfr: &S, h: &Pk::Sha256) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        (
            Self { stack: Witness::hash_dissatisfaction(), ..Self::TRIVIAL },
            Self { stack: Witness::sha256_preimage(stfr, h), ..Self::TRIVIAL },
        )
    }

    /// The (dissatisfaction, satisfaction) pair for a `ripemd256` fragment.
    fn hash256<S>(stfr: &S, h: &Pk::Hash256) -> (Self, Self)
    where
        S: AssetProvider<Pk>,
    {
        (
            Self { stack: Witness::hash_dissatisfaction(), ..Self::TRIVIAL },
            Self { stack: Witness::hash256_preimage(stfr, h), ..Self::TRIVIAL },
        )
    }

    /// Compute the dissatisfaction and the satisfaction for the given node, by querying
    /// the satisfier `stfr`.
    ///
    /// If the `malleable` flag is set to true, more efficient satisfactions may be found,
    /// but which a 3rd party may be able to replace with less efficient versions. (This
    /// flag does not affect dissatisfactions.)
    pub(super) fn dissat_sat<Ctx, Sat>(
        node: &Miniscript<Pk, Ctx>,
        stfr: &Sat,
        malleable: bool,
        root_has_sig: bool,
        leaf_hash: Option<TapLeafHash>,
    ) -> (Self, Self)
    where
        Ctx: ScriptContext,
        Sat: AssetProvider<Pk>,
    {
        let min_fn = if malleable {
            Self::minimum_mall
        } else {
            Self::minimum
        };
        let thresh_fn = if malleable {
            Self::thresh_mall
        } else {
            Self::thresh
        };

        let mut stack = vec![];
        for item in node.post_order_iter() {
            let new_dissat_sat = match *item.node.as_inner() {
                Terminal::False => (Self::TRIVIAL, Self::IMPOSSIBLE),
                Terminal::True => (Self::IMPOSSIBLE, Self::TRIVIAL),
                Terminal::PkK(ref pk) => Self::pk_k(stfr, pk, leaf_hash),
                Terminal::PkH(ref pk) => Self::pk_h::<_, Ctx>(stfr, pk, leaf_hash),
                Terminal::RawPkH(ref pkh) => Self::raw_pk_h::<_, Ctx>(stfr, pkh, leaf_hash),
                Terminal::Multi(ref thresh) => Self::multi(stfr, thresh),
                Terminal::MultiA(ref thresh) => Self::multi_a(stfr, thresh, leaf_hash.expect("leaf_hash is present when Ctx = Tap, which must be true if multi_a is present")),
                Terminal::After(t) => Self::after(stfr, t, root_has_sig),
                Terminal::Older(t) => Self::older(stfr, t, root_has_sig),
                Terminal::Ripemd160(ref h) => Self::ripemd160(stfr, h),
                Terminal::Hash160(ref h) => Self::hash160(stfr, h),
                Terminal::Sha256(ref h) => Self::sha256(stfr, h),
                Terminal::Hash256(ref h) => Self::hash256(stfr, h),
                // These four wrappers have no effect on either satisfaction nor dissatisfaction
                Terminal::Alt(_)
                | Terminal::Swap(_)
                | Terminal::Check(_)
                | Terminal::ZeroNotEqual(_) => stack.pop().unwrap(),
                Terminal::DupIf(_) => {
                    let (_, sub) = stack.pop().unwrap();
                    (
                        Self::push_0(),
                        Self {
                            stack: Witness::combine(sub.stack, Witness::push_1()),
                            ..sub
                        }
                    )
                }
                Terminal::Verify(_) => {
                    let (_, sub) = stack.pop().unwrap();
                    (Self::IMPOSSIBLE, sub)
                }
                Terminal::NonZero(_) => {
                    let (_, sub) = stack.pop().unwrap();
                    (Self::IMPOSSIBLE, sub)
                }
                Terminal::AndB(_, _) => {
                    let (r_dis, r_sat) = stack.pop().unwrap();
                    let (l_dis, l_sat) = stack.pop().unwrap();
                    (
                        l_dis.concatenate_rev(r_dis),
                        l_sat.concatenate_rev(r_sat),
                    )
                },
                Terminal::AndV(_, _) => {
                    let (r_dis, r_sat) = stack.pop().unwrap();
                    let (_, l_sat) = stack.pop().unwrap();
                    // Left child is a `v` and must be satisfied for both sat and dissat.
                    (
                        l_sat.clone().concatenate_rev(r_dis),
                        l_sat.concatenate_rev(r_sat),
                    )
                },
                Terminal::AndOr(_, _, _) => {
                    let (c_dis, c_sat) = stack.pop().unwrap();
                    let (_, b_sat) = stack.pop().unwrap();
                    let (a_dis, a_sat) = stack.pop().unwrap();

                    (
                        a_dis.clone().concatenate_rev(c_dis),
                        min_fn(a_sat.concatenate_rev(b_sat), a_dis.concatenate_rev(c_sat)),
                    )
                }
                Terminal::OrB(_, _) => {
                    let (r_dis, r_sat) = stack.pop().unwrap();
                    let (l_dis, l_sat) = stack.pop().unwrap();
                    assert!(!l_dis.has_sig);
                    assert!(!r_dis.has_sig);

                    (
                        l_dis.clone().concatenate_rev(r_dis.clone()),
                        min_fn(
                            Self::concatenate_rev(l_dis, r_sat),
                            Self::concatenate_rev(l_sat, r_dis),
                        ),
                    )
                }
                Terminal::OrC(_, _) => {
                    let (_, r_sat) = stack.pop().unwrap();
                    let (l_dis, l_sat) = stack.pop().unwrap();
                    assert!(!l_dis.has_sig);

                    (
                        Self::IMPOSSIBLE,
                        min_fn(l_sat, Self::concatenate_rev(l_dis, r_sat))
                    )
                }
                Terminal::OrD(_, _) => {
                    let (r_dis, r_sat) = stack.pop().unwrap();
                    let (l_dis, l_sat) = stack.pop().unwrap();
                    assert!(!l_dis.has_sig);

                    (
                        l_dis.clone().concatenate_rev(r_dis),
                        min_fn(l_sat, Self::concatenate_rev(l_dis, r_sat))
                    )
                }
                Terminal::OrI(_, _) => {
                    let (r_dis, r_sat) = stack.pop().unwrap();
                    let (l_dis, l_sat) = stack.pop().unwrap();
                    // FIXME existing code sets timelocks to None instead of propagating them,
                    // in the dissat case. This dates to the original plan module and was not
                    // comment on. https://github.com/rust-bitcoin/rust-miniscript/pull/592
                    // Was likely a mistake. Need to find a test case that distinguishes before
                    // merging.
                    (
                        min_fn(
                            Self {
                                stack: Witness::combine(l_dis.stack, Witness::push_1()),
                                ..l_dis
                            },
                            Self {
                                stack: Witness::combine(r_dis.stack, Witness::push_0()),
                                ..r_dis
                            },
                        ),
                        min_fn(
                            Self {
                                stack: Witness::combine(l_sat.stack, Witness::push_1()),
                                ..l_sat
                            },
                            Self {
                                stack: Witness::combine(r_sat.stack, Witness::push_0()),
                                ..r_sat
                            },
                        ),
                    )
                }
                Terminal::Thresh(ref thresh) => {
                    let (dissats, sats) = stack
                        .drain(stack.len() - thresh.n()..)
                        .collect::<(Vec<_>, Vec<_>)>();

                    // Dissatisfaction of a threshold is just the dissatisfaction of its children.
                    let dissat = dissats
                        .iter()
                        .cloned()
                        .fold(Self::empty(), Self::concatenate_rev);

                    // But satisfaction is a bit harder.
                    let sat = if thresh.k() == thresh.n() {
                        // this is just an and
                        sats.into_iter()
                            .fold(Self::empty(), Self::concatenate_rev)
                    } else {
                        thresh_fn(thresh.k(), thresh.n(), dissats, sats)
                    };

                    (dissat, sat)
                }
            };

            stack.push(new_dissat_sat);
        }

        assert_eq!(stack.len(), 1);
        stack.pop().unwrap()
    }
}
