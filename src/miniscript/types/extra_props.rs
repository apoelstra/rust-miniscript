// SPDX-License-Identifier: CC0-1.0

//! Other miscellaneous type properties which are not related to
//! correctness or malleability.

use core::cmp;
use core::iter::once;

use super::ScriptContext;
use crate::miniscript::limits::{MAX_PUBKEYS_IN_CHECKSIGADD, MAX_PUBKEYS_PER_MULTISIG};
use crate::prelude::*;
use crate::{script_num_size, AbsLockTime, MiniscriptKey, RelLockTime, Terminal, ValidationParams};

/// Timelock information for satisfaction of a fragment.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default, Hash)]
pub struct TimelockInfo {
    /// csv with heights
    pub csv_with_height: bool,
    /// csv with times
    pub csv_with_time: bool,
    /// cltv with heights
    pub cltv_with_height: bool,
    /// cltv with times
    pub cltv_with_time: bool,
    /// combination of any heightlocks and timelocks
    pub contains_combination: bool,
}

impl TimelockInfo {
    /// Creates a new `TimelockInfo` with all fields set to false.
    pub const fn new() -> Self {
        TimelockInfo {
            csv_with_height: false,
            csv_with_time: false,
            cltv_with_height: false,
            cltv_with_time: false,
            contains_combination: false,
        }
    }

    /// Returns true if the current `TimelockInfo` contains any possible unspendable paths.
    pub fn contains_unspendable_path(self) -> bool { self.contains_combination }

    /// Combines two `TimelockInfo` structs setting `contains_combination` if required (logical and).
    pub(crate) fn combine_and(a: Self, b: Self) -> Self {
        Self::combine_threshold(2, once(a).chain(once(b)))
    }

    /// Combines two `TimelockInfo` structs, does not set `contains_combination` (logical or).
    pub(crate) fn combine_or(a: Self, b: Self) -> Self {
        Self::combine_threshold(1, once(a).chain(once(b)))
    }

    /// Combines timelocks, if threshold `k` is greater than one we check for any unspendable paths.
    pub(crate) fn combine_threshold<I>(k: usize, timelocks: I) -> TimelockInfo
    where
        I: IntoIterator<Item = TimelockInfo>,
    {
        // Propagate all fields of `TimelockInfo` from each of the node's children to the node
        // itself (by taking the logical-or of all of them). In case `k == 1` (this is a disjunction)
        // this is all we need to do: the node may behave like any of its children, for purposes
        // of timelock accounting.
        //
        // If `k > 1` we have the additional consideration that if any two children have conflicting
        // timelock requirements, this represents an inaccessible spending branch.
        timelocks
            .into_iter()
            .fold(TimelockInfo::default(), |mut acc, t| {
                // If more than one branch may be taken, and some other branch has a requirement
                // that conflicts with this one, set `contains_combination`.
                if k > 1 {
                    let height_and_time = (acc.csv_with_height && t.csv_with_time)
                        || (acc.csv_with_time && t.csv_with_height)
                        || (acc.cltv_with_time && t.cltv_with_height)
                        || (acc.cltv_with_height && t.cltv_with_time);

                    acc.contains_combination |= height_and_time;
                }
                acc.csv_with_height |= t.csv_with_height;
                acc.csv_with_time |= t.csv_with_time;
                acc.cltv_with_height |= t.cltv_with_height;
                acc.cltv_with_time |= t.cltv_with_time;
                acc.contains_combination |= t.contains_combination;
                acc
            })
    }
}

/// Structure representing the satisfaction or dissatisfaction size of a fragment.
///
/// All ECDSA signatures are assumed to be 73 bytes in size (including the length
/// prefix if it's a witness element, or push opcode if it's a script push) and
/// its sighash byte.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct SatData {
    /// The maximum size, in bytes, of the witness stack.
    ///
    /// Includes the length prefixes for the individual elements but NOT the length
    /// prefix for the whole stack.
    pub max_witness_stack_size: usize,
    /// The maximum number of elements on the witness stack.
    pub max_witness_stack_count: usize,
    /// The maximum size, in bytes, of the `scriptSig`.
    ///
    /// Does NOT include the length prefix.
    pub max_script_sig_size: usize,
    /// Maximum number of stack and altstack elements at any point during execution.
    ///
    /// This does **not** include initial witness elements. This element only captures
    /// the additional elements that are pushed during execution.
    pub max_exec_stack_count: usize,
    /// The maximum number of executed, non-push opcodes. Irrelevant in Taproot context.
    pub max_exec_op_count: usize,
}

impl SatData {
    fn fieldwise_max(self, other: Self) -> Self {
        Self {
            max_witness_stack_count: cmp::max(
                self.max_witness_stack_count,
                other.max_witness_stack_count,
            ),
            max_witness_stack_size: cmp::max(
                self.max_witness_stack_size,
                other.max_witness_stack_size,
            ),
            max_script_sig_size: cmp::max(self.max_script_sig_size, other.max_script_sig_size),
            max_exec_stack_count: cmp::max(self.max_exec_stack_count, other.max_exec_stack_count),
            max_exec_op_count: cmp::max(self.max_exec_op_count, other.max_exec_op_count),
        }
    }

    fn fieldwise_max_opt(slf: Option<Self>, other: Option<Self>) -> Option<Self> {
        match (slf, other) {
            (None, None) => None,
            (Some(x), None) => Some(x),
            (None, Some(x)) => Some(x),
            (Some(x), Some(y)) => Some(x.fieldwise_max(y)),
        }
    }
}

/// The number of paths that a multipath key extends into, if this node has any
/// multipath keys.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum MultipathLen {
    /// There are multipath key(s) and this is their length.
    N(usize),
    /// There are multiple multipath keys with different lengths; here are
    /// two of them.
    Inconsistent(usize, usize),
    /// There are no multipath keys.
    NoMultipathKeys,
}

impl MultipathLen {
    /// Constructs a multipath length from a pubkey.
    fn from_pk<Pk: MiniscriptKey>(pk: &Pk) -> Self {
        let n_paths = pk.num_der_paths();
        if n_paths == 0 || n_paths == 1 {
            Self::NoMultipathKeys
        } else {
            Self::N(n_paths)
        }
    }

    /// Combines two multipath lengths in the obvious way.
    fn intersect(self, other: Self) -> Self {
        match (self, other) {
            (x, Self::NoMultipathKeys) | (Self::NoMultipathKeys, x) => x,
            (_, x @ Self::Inconsistent(..)) | (x @ Self::Inconsistent(..), _) => x,
            (Self::N(x), Self::N(y)) => {
                if x == y {
                    Self::N(x)
                } else {
                    Self::Inconsistent(x, y)
                }
            }
        }
    }
}

/// Structure representing the extra type properties of a fragment.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct ExtData {
    /// The number of bytes needed to encode its scriptpubkey
    pub pk_cost: usize,
    /// Whether this fragment can be verify-wrapped for free
    pub has_free_verify: bool,
    /// Static (executed + unexecuted) number of opcodes for the fragment. Irrelevant in Taproot
    /// context.
    pub static_ops: usize,
    /// Various worst-case values for the satisfaction case.
    pub sat_data: Option<SatData>,
    /// Various worst-case values for the dissatisfaction case.
    pub dissat_data: Option<SatData>,
    /// The timelock info about heightlocks and timelocks
    pub timelock_info: TimelockInfo,
    /// The number of paths that a multipath key extends into, if this node has any
    /// multipath keys.
    pub multipath_len: MultipathLen,
    /// The miniscript tree depth/height of this node.
    /// Used for checking the max depth of the miniscript tree to prevent stack overflow.
    pub tree_height: usize,
}

impl ExtData {
    /// Extra data for the `0` combinator
    pub const FALSE: Self = ExtData {
        pk_cost: 1,
        has_free_verify: false,
        static_ops: 0,
        sat_data: None,
        dissat_data: Some(SatData {
            max_witness_stack_size: 0,
            max_witness_stack_count: 0,
            max_script_sig_size: 0,
            max_exec_stack_count: 1,
            max_exec_op_count: 0,
        }),
        timelock_info: TimelockInfo::new(),
        multipath_len: MultipathLen::NoMultipathKeys,
        tree_height: 0,
    };

    /// Extra data for the `1` combinator
    pub const TRUE: Self = ExtData {
        pk_cost: 1,
        has_free_verify: false,
        static_ops: 0,
        sat_data: Some(SatData {
            max_witness_stack_size: 0,
            max_witness_stack_count: 0,
            max_script_sig_size: 0,
            max_exec_stack_count: 1,
            max_exec_op_count: 0,
        }),
        dissat_data: None,
        timelock_info: TimelockInfo::new(),
        multipath_len: MultipathLen::NoMultipathKeys,
        tree_height: 0,
    };
}

impl ExtData {
    /// Extra properties for the `pk_k` fragment.
    ///
    /// The key must be provided to determine its size.
    pub fn pk_k<Pk: MiniscriptKey>(params: &ValidationParams, pk: &Pk) -> Self {
        ExtData {
            pk_cost: params.encoded_key_size(pk),
            has_free_verify: false,
            static_ops: 0,
            sat_data: Some(SatData {
                max_witness_stack_size: params.maximum_encoded_sig_size(),
                max_witness_stack_count: 1,
                max_script_sig_size: params.maximum_encoded_sig_size(),
                max_exec_stack_count: 1, // pushes the pk
                max_exec_op_count: 0,
            }),
            dissat_data: Some(SatData {
                max_witness_stack_size: 1,
                max_witness_stack_count: 1,
                max_script_sig_size: 1,
                max_exec_stack_count: 1, // pushes the pk
                max_exec_op_count: 0,
            }),
            timelock_info: TimelockInfo::default(),
            multipath_len: MultipathLen::from_pk(pk),
            tree_height: 0,
        }
    }

    /// Extra properties for the `pk_h` fragment.
    ///
    /// If the key is known, it should be provided to gain a size estimate from
    /// it. If not, the worst-case for the context will be assumed.
    pub fn pk_h<Pk: MiniscriptKey, Ctx: ScriptContext>(pk: Option<&Pk>) -> Self {
        // With a raw pkh we don't know the preimage size so we have to assume the worst.
        // FIXME with ValidationParams we will be able to determine if Ctx is Segwitv0 and exclude uncompressed keys.
        let (key_bytes, max_sig_bytes) = match (Ctx::sig_type(), pk) {
            (crate::SigType::Ecdsa, Some(pk)) if pk.is_uncompressed() => (65, 73),
            (crate::SigType::Ecdsa, _) => (34, 73),
            (crate::SigType::Schnorr, _) => (33, 66),
        };

        ExtData {
            pk_cost: 24,
            has_free_verify: false,
            static_ops: 3,
            sat_data: Some(SatData {
                max_witness_stack_size: key_bytes + max_sig_bytes,
                max_witness_stack_count: 2,
                max_script_sig_size: key_bytes + max_sig_bytes,
                max_exec_stack_count: 2, // dup and hash push
                max_exec_op_count: 0,
            }),
            dissat_data: Some(SatData {
                max_witness_stack_size: key_bytes + 1,
                max_witness_stack_count: 2,
                max_script_sig_size: key_bytes + 1,
                max_exec_stack_count: 2, // dup and hash push
                max_exec_op_count: 0,
            }),
            timelock_info: TimelockInfo::default(),
            multipath_len: match pk {
                Some(pk) => MultipathLen::from_pk(pk),
                // A raw pubkey hash represents a single concrete key (barring hash collisions),
                // not a multipath (or wildcard, or whatever) key.
                None => MultipathLen::NoMultipathKeys,
            },
            tree_height: 0,
        }
    }

    /// Extra properties for the `multi` fragment.
    pub fn multi<Pk: MiniscriptKey>(
        thresh: &crate::Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>,
    ) -> Self {
        let (n, k) = (thresh.n(), thresh.k());
        let num_cost = match (k > 16, n > 16) {
            (true, true) => 4,
            (false, true) => 3,
            (true, false) => 3,
            (false, false) => 2,
        };
        ExtData {
            pk_cost: num_cost
                + thresh
                    .iter()
                    .map(|k| if k.is_uncompressed() { 65 } else { 34 })
                    .sum::<usize>()
                + 1,
            has_free_verify: true,
            static_ops: 1,
            sat_data: Some(SatData {
                max_witness_stack_size: 1 + 73 * k,
                max_witness_stack_count: k + 1,
                max_script_sig_size: 1 + 73 * k,
                max_exec_stack_count: n, // n pks
                // Multi is the only fragment which has additional executed opcodes to count.
                max_exec_op_count: n,
            }),
            dissat_data: Some(SatData {
                max_witness_stack_size: 1 + k,
                max_witness_stack_count: k + 1,
                max_script_sig_size: 1 + k,
                max_exec_stack_count: n, // n pks
                max_exec_op_count: n,
            }),
            timelock_info: TimelockInfo::new(),
            multipath_len: thresh
                .iter()
                .map(MultipathLen::from_pk)
                .fold(MultipathLen::NoMultipathKeys, MultipathLen::intersect),
            tree_height: 0,
        }
    }

    /// Extra properties for the `multi_a` fragment.
    pub fn multi_a<Pk: MiniscriptKey>(
        thresh: &crate::Threshold<Pk, MAX_PUBKEYS_IN_CHECKSIGADD>,
    ) -> Self {
        let (k, n) = (thresh.k(), thresh.n());
        let num_cost = match (k > 16, n > 16) {
            (true, true) => 4,
            (false, true) => 3,
            (true, false) => 3,
            (false, false) => 2,
        };
        ExtData {
            pk_cost: num_cost + 33 * n /*pks*/ + (n - 1) /*checksigadds*/ + 1,
            has_free_verify: true,
            static_ops: 0, // irrelevant; no ops limit in Taproot
            sat_data: Some(SatData {
                max_witness_stack_size: (n - k) + 66 * k,
                max_witness_stack_count: n,
                max_script_sig_size: 0,
                max_exec_stack_count: 2, // the two nums before num equal verify
                max_exec_op_count: 0,
            }),
            dissat_data: Some(SatData {
                max_witness_stack_size: n,
                max_witness_stack_count: n,
                max_script_sig_size: 0,
                max_exec_stack_count: 2, // the two nums before num equal verify
                max_exec_op_count: 0,
            }),
            timelock_info: TimelockInfo::new(),
            multipath_len: thresh
                .iter()
                .map(MultipathLen::from_pk)
                .fold(MultipathLen::NoMultipathKeys, MultipathLen::intersect),
            tree_height: 0,
        }
    }

    /// Extra properties for the `sha256` fragment.
    pub const fn sha256() -> Self {
        ExtData {
            pk_cost: 33 + 6,
            has_free_verify: true,
            static_ops: 4,
            sat_data: Some(SatData {
                max_witness_stack_size: 33,
                max_witness_stack_count: 1,
                max_script_sig_size: 33,
                max_exec_stack_count: 2, // either size <32> or <sha256> <32 byte>
                max_exec_op_count: 0,
            }),
            dissat_data: Some(SatData {
                max_witness_stack_size: 33,
                max_witness_stack_count: 2,
                max_script_sig_size: 33,
                max_exec_stack_count: 2, // either size <32> or <sha256> <32 byte>
                max_exec_op_count: 0,
            }),
            timelock_info: TimelockInfo::new(),
            multipath_len: MultipathLen::NoMultipathKeys,
            tree_height: 0,
        }
    }

    /// Extra properties for the `hash256` fragment.
    pub const fn hash256() -> Self {
        ExtData {
            pk_cost: 33 + 6,
            has_free_verify: true,
            static_ops: 4,
            sat_data: Some(SatData {
                max_witness_stack_size: 33,
                max_witness_stack_count: 1,
                max_script_sig_size: 33,
                max_exec_stack_count: 2, // either size <32> or <sha256> <32 byte>
                max_exec_op_count: 0,
            }),
            dissat_data: Some(SatData {
                max_witness_stack_size: 33,
                max_witness_stack_count: 2,
                max_script_sig_size: 33,
                max_exec_stack_count: 2, // either size <32> or <sha256> <32 byte>
                max_exec_op_count: 0,
            }),
            timelock_info: TimelockInfo::new(),
            multipath_len: MultipathLen::NoMultipathKeys,
            tree_height: 0,
        }
    }

    /// Extra properties for the `ripemd160` fragment.
    pub const fn ripemd160() -> Self {
        ExtData {
            pk_cost: 21 + 6,
            has_free_verify: true,
            static_ops: 4,
            sat_data: Some(SatData {
                max_witness_stack_size: 33,
                max_witness_stack_count: 1,
                max_script_sig_size: 33,
                max_exec_stack_count: 2, // either size <32> or <sha256> <32 byte>
                max_exec_op_count: 0,
            }),
            dissat_data: Some(SatData {
                max_witness_stack_size: 33,
                max_witness_stack_count: 2,
                max_script_sig_size: 33,
                max_exec_stack_count: 2, // either size <32> or <sha256> <32 byte>
                max_exec_op_count: 0,
            }),
            timelock_info: TimelockInfo::new(),
            multipath_len: MultipathLen::NoMultipathKeys,
            tree_height: 0,
        }
    }

    /// Extra properties for the `hash160` fragment.
    pub const fn hash160() -> Self {
        ExtData {
            pk_cost: 21 + 6,
            has_free_verify: true,
            static_ops: 4,
            sat_data: Some(SatData {
                max_witness_stack_size: 33,
                max_witness_stack_count: 1,
                max_script_sig_size: 33,
                max_exec_stack_count: 2, // either size <32> or <sha256> <32 byte>
                max_exec_op_count: 0,
            }),
            dissat_data: Some(SatData {
                max_witness_stack_size: 33,
                max_witness_stack_count: 2,
                max_script_sig_size: 33,
                max_exec_stack_count: 2, // either size <32> or <sha256> <32 byte>
                max_exec_op_count: 0,
            }),
            timelock_info: TimelockInfo::new(),
            multipath_len: MultipathLen::NoMultipathKeys,
            tree_height: 0,
        }
    }

    /// Extra properties for the `after` fragment.
    pub fn after(t: AbsLockTime) -> Self {
        ExtData {
            pk_cost: script_num_size(t.to_consensus_u32() as usize) + 1,
            has_free_verify: false,
            static_ops: 1,
            sat_data: Some(SatData {
                max_witness_stack_size: 0,
                max_witness_stack_count: 0,
                max_script_sig_size: 0,
                max_exec_stack_count: 1, // <t>
                max_exec_op_count: 0,
            }),
            dissat_data: None,
            timelock_info: TimelockInfo {
                csv_with_height: false,
                csv_with_time: false,
                cltv_with_height: t.is_block_height(),
                cltv_with_time: t.is_block_time(),
                contains_combination: false,
            },
            multipath_len: MultipathLen::NoMultipathKeys,
            tree_height: 0,
        }
    }

    /// Extra properties for the `older` fragment.
    pub fn older(t: RelLockTime) -> Self {
        ExtData {
            pk_cost: script_num_size(t.to_consensus_u32() as usize) + 1,
            has_free_verify: false,
            static_ops: 1,
            sat_data: Some(SatData {
                max_witness_stack_size: 0,
                max_witness_stack_count: 0,
                max_script_sig_size: 0,
                max_exec_stack_count: 1, // <t>
                max_exec_op_count: 0,
            }),
            dissat_data: None,
            timelock_info: TimelockInfo {
                csv_with_height: t.is_height_locked(),
                csv_with_time: t.is_time_locked(),
                cltv_with_height: false,
                cltv_with_time: false,
                contains_combination: false,
            },
            multipath_len: MultipathLen::NoMultipathKeys,
            tree_height: 0,
        }
    }

    /// Extra properties for the `a:` fragment.
    pub const fn cast_alt(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 2,
            has_free_verify: false,
            static_ops: 2 + self.static_ops,
            sat_data: self.sat_data,
            dissat_data: self.dissat_data,
            timelock_info: self.timelock_info,
            multipath_len: self.multipath_len,
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `s:` fragment.
    pub const fn cast_swap(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 1,
            has_free_verify: self.has_free_verify,
            static_ops: 1 + self.static_ops,
            sat_data: self.sat_data,
            dissat_data: self.dissat_data,
            timelock_info: self.timelock_info,
            multipath_len: self.multipath_len,
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `c:` fragment.
    pub const fn cast_check(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 1,
            has_free_verify: true,
            static_ops: 1 + self.static_ops,
            sat_data: self.sat_data,
            dissat_data: self.dissat_data,
            timelock_info: self.timelock_info,
            multipath_len: self.multipath_len,
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `d:` fragment.
    pub fn cast_dupif(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 3,
            has_free_verify: false,
            static_ops: 3 + self.static_ops,
            sat_data: self.sat_data.map(|data| SatData {
                max_witness_stack_size: data.max_witness_stack_size + 1,
                max_witness_stack_count: data.max_witness_stack_count + 2,
                max_script_sig_size: data.max_script_sig_size + 1,
                // Note: in practice this cmp::max always evaluates to data.max_exec_stack_count.
                max_exec_stack_count: cmp::max(1, data.max_exec_stack_count),
                max_exec_op_count: data.max_exec_op_count,
            }),
            dissat_data: Some(SatData {
                max_witness_stack_size: 1,
                max_witness_stack_count: 1,
                max_script_sig_size: 1,
                max_exec_stack_count: 1,
                max_exec_op_count: 0,
            }),
            timelock_info: self.timelock_info,
            multipath_len: self.multipath_len,
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `v:` fragment.
    pub fn cast_verify(self) -> Self {
        let verify_cost = usize::from(!self.has_free_verify);
        ExtData {
            pk_cost: self.pk_cost + usize::from(!self.has_free_verify),
            has_free_verify: false,
            static_ops: verify_cost + self.static_ops,
            sat_data: self.sat_data,
            dissat_data: None,
            timelock_info: self.timelock_info,
            multipath_len: self.multipath_len,
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `j:` fragment.
    pub const fn cast_nonzero(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 4,
            has_free_verify: false,
            static_ops: 4 + self.static_ops,
            sat_data: self.sat_data,
            dissat_data: Some(SatData {
                max_witness_stack_size: 1,
                max_witness_stack_count: 1,
                max_script_sig_size: 1,
                max_exec_stack_count: 1,
                max_exec_op_count: 0,
            }),
            timelock_info: self.timelock_info,
            multipath_len: self.multipath_len,
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `n:` fragment.
    pub const fn cast_zeronotequal(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 1,
            has_free_verify: false,
            static_ops: 1 + self.static_ops,
            // Technically max_exec_stack_count should be max(1, self.max_exec_stack_count), but in practice
            // this evaluates to the same thing, so to avoid opening self.sat_data, we just copy
            // the whole thing. See `cast_dupif`.
            sat_data: self.sat_data,
            dissat_data: self.dissat_data,
            timelock_info: self.timelock_info,
            multipath_len: self.multipath_len,
            tree_height: self.tree_height + 1,
        }
    }

    /// Cast by changing `[X]` to `AndV([X], True)`
    pub fn cast_true(self) -> Self { Self::and_v(self, Self::TRUE) }

    /// Cast by changing `[X]` to `or_i([X], 0)`. Default implementation
    /// simply passes through to `cast_or_i_false`
    pub fn cast_unlikely(self) -> Self { Self::or_i(self, Self::FALSE) }

    /// Cast by changing `[X]` to `or_i(0, [X])`. Default implementation
    /// simply passes through to `cast_or_i_false`
    pub fn cast_likely(self) -> Self { Self::or_i(Self::FALSE, self) }

    /// Extra properties for the `and_b` fragment.
    pub fn and_b(l: Self, r: Self) -> Self {
        ExtData {
            pk_cost: l.pk_cost + r.pk_cost + 1,
            has_free_verify: false,
            static_ops: 1 + l.static_ops + r.static_ops,
            sat_data: l.sat_data.zip(r.sat_data).map(|(l, r)| SatData {
                max_witness_stack_count: l.max_witness_stack_count + r.max_witness_stack_count,
                max_witness_stack_size: l.max_witness_stack_size + r.max_witness_stack_size,
                max_script_sig_size: l.max_script_sig_size + r.max_script_sig_size,
                // Left element leaves a stack result on the stack top and then right element is evaluated
                // Therefore + 1 is added to execution size of second element
                max_exec_stack_count: cmp::max(l.max_exec_stack_count, 1 + r.max_exec_stack_count),
                max_exec_op_count: l.max_exec_op_count + r.max_exec_op_count,
            }),
            dissat_data: l.dissat_data.zip(r.dissat_data).map(|(l, r)| SatData {
                max_witness_stack_count: l.max_witness_stack_count + r.max_witness_stack_count,
                max_witness_stack_size: l.max_witness_stack_size + r.max_witness_stack_size,
                max_script_sig_size: l.max_script_sig_size + r.max_script_sig_size,
                // Left element leaves a stack result on the stack top and then right element is evaluated
                // Therefore + 1 is added to execution size of second element
                max_exec_stack_count: cmp::max(l.max_exec_stack_count, 1 + r.max_exec_stack_count),
                max_exec_op_count: l.max_exec_op_count + r.max_exec_op_count,
            }),
            timelock_info: TimelockInfo::combine_and(l.timelock_info, r.timelock_info),
            multipath_len: l.multipath_len.intersect(r.multipath_len),
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `and_v` fragment.
    pub fn and_v(l: Self, r: Self) -> Self {
        ExtData {
            pk_cost: l.pk_cost + r.pk_cost,
            has_free_verify: r.has_free_verify,
            static_ops: l.static_ops + r.static_ops,
            sat_data: l.sat_data.zip(r.sat_data).map(|(l, r)| SatData {
                max_witness_stack_count: l.max_witness_stack_count + r.max_witness_stack_count,
                max_witness_stack_size: l.max_witness_stack_size + r.max_witness_stack_size,
                max_script_sig_size: l.max_script_sig_size + r.max_script_sig_size,
                // [X] leaves no element after evaluation, hence this is the max
                max_exec_stack_count: cmp::max(l.max_exec_stack_count, r.max_exec_stack_count),
                max_exec_op_count: l.max_exec_op_count + r.max_exec_op_count,
            }),
            dissat_data: None,
            timelock_info: TimelockInfo::combine_and(l.timelock_info, r.timelock_info),
            multipath_len: l.multipath_len.intersect(r.multipath_len),
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `or_b` fragment.
    pub fn or_b(l: Self, r: Self) -> Self {
        let sat_concat = |l: Option<SatData>, r: Option<SatData>| {
            l.zip(r).map(|(l, r)| SatData {
                max_witness_stack_count: l.max_witness_stack_count + r.max_witness_stack_count,
                max_witness_stack_size: l.max_witness_stack_size + r.max_witness_stack_size,
                max_script_sig_size: l.max_script_sig_size + r.max_script_sig_size,
                // Left element leaves a stack result on the stack top and then right element is evaluated
                // Therefore + 1 is added to execution size of second element
                max_exec_stack_count: cmp::max(l.max_exec_stack_count, 1 + r.max_exec_stack_count),
                max_exec_op_count: l.max_exec_op_count + r.max_exec_op_count,
            })
        };

        ExtData {
            pk_cost: l.pk_cost + r.pk_cost + 1,
            has_free_verify: false,
            static_ops: 1 + l.static_ops + r.static_ops,
            sat_data: SatData::fieldwise_max_opt(
                sat_concat(l.sat_data, r.dissat_data),
                sat_concat(l.dissat_data, r.sat_data),
            ),
            dissat_data: sat_concat(l.dissat_data, r.dissat_data),
            timelock_info: TimelockInfo::combine_or(l.timelock_info, r.timelock_info),
            multipath_len: l.multipath_len.intersect(r.multipath_len),
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `or_d` fragment.
    pub fn or_d(l: Self, r: Self) -> Self {
        let sat_concat = |l: Option<SatData>, r: Option<SatData>| {
            l.zip(r).map(|(l, r)| SatData {
                max_witness_stack_count: l.max_witness_stack_count + r.max_witness_stack_count,
                max_witness_stack_size: l.max_witness_stack_size + r.max_witness_stack_size,
                max_script_sig_size: l.max_script_sig_size + r.max_script_sig_size,
                max_exec_stack_count: cmp::max(l.max_exec_stack_count, r.max_exec_stack_count),
                max_exec_op_count: l.max_exec_op_count + r.max_exec_op_count,
            })
        };

        ExtData {
            pk_cost: l.pk_cost + r.pk_cost + 3,
            has_free_verify: false,
            static_ops: 3 + l.static_ops + r.static_ops,
            sat_data: SatData::fieldwise_max_opt(l.sat_data, sat_concat(l.dissat_data, r.sat_data)),
            dissat_data: sat_concat(l.dissat_data, r.dissat_data),
            timelock_info: TimelockInfo::combine_or(l.timelock_info, r.timelock_info),
            multipath_len: l.multipath_len.intersect(r.multipath_len),
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `or_c` fragment.
    pub fn or_c(l: Self, r: Self) -> Self {
        let sat_concat = |l: Option<SatData>, r: Option<SatData>| {
            l.zip(r).map(|(l, r)| SatData {
                max_witness_stack_count: l.max_witness_stack_count + r.max_witness_stack_count,
                max_witness_stack_size: l.max_witness_stack_size + r.max_witness_stack_size,
                max_script_sig_size: l.max_script_sig_size + r.max_script_sig_size,
                max_exec_stack_count: cmp::max(l.max_exec_stack_count, r.max_exec_stack_count),
                max_exec_op_count: l.max_exec_op_count + r.max_exec_op_count,
            })
        };

        ExtData {
            pk_cost: l.pk_cost + r.pk_cost + 2,
            has_free_verify: false,
            static_ops: 2 + l.static_ops + r.static_ops,
            sat_data: SatData::fieldwise_max_opt(l.sat_data, sat_concat(l.dissat_data, r.sat_data)),
            dissat_data: None,
            timelock_info: TimelockInfo::combine_or(l.timelock_info, r.timelock_info),
            multipath_len: l.multipath_len.intersect(r.multipath_len),
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `or_i` fragment.
    pub fn or_i(l: Self, r: Self) -> Self {
        let with_0 = |data: SatData| SatData {
            max_witness_stack_count: 1 + data.max_witness_stack_count,
            max_witness_stack_size: 1 + data.max_witness_stack_size,
            max_script_sig_size: 1 + data.max_script_sig_size,
            max_exec_stack_count: data.max_exec_stack_count,
            max_exec_op_count: data.max_exec_op_count,
        };
        let with_1 = |data: SatData| SatData {
            max_witness_stack_count: 1 + data.max_witness_stack_count,
            max_witness_stack_size: 2 + data.max_witness_stack_size,
            max_script_sig_size: 1 + data.max_script_sig_size,
            max_exec_stack_count: data.max_exec_stack_count,
            max_exec_op_count: data.max_exec_op_count,
        };

        ExtData {
            pk_cost: l.pk_cost + r.pk_cost + 3,
            has_free_verify: false,
            static_ops: 3 + l.static_ops + r.static_ops,
            sat_data: SatData::fieldwise_max_opt(l.sat_data.map(with_1), r.sat_data.map(with_0)),
            dissat_data: SatData::fieldwise_max_opt(
                l.dissat_data.map(with_1),
                r.dissat_data.map(with_0),
            ),
            timelock_info: TimelockInfo::combine_or(l.timelock_info, r.timelock_info),
            multipath_len: l.multipath_len.intersect(r.multipath_len),
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `andor` fragment.
    pub fn and_or(a: Self, b: Self, c: Self) -> Self {
        let sat_concat = |l: Option<SatData>, r: Option<SatData>| {
            l.zip(r).map(|(l, r)| SatData {
                max_witness_stack_count: l.max_witness_stack_count + r.max_witness_stack_count,
                max_witness_stack_size: l.max_witness_stack_size + r.max_witness_stack_size,
                max_script_sig_size: l.max_script_sig_size + r.max_script_sig_size,
                max_exec_stack_count: cmp::max(l.max_exec_stack_count, r.max_exec_stack_count),
                max_exec_op_count: l.max_exec_op_count + r.max_exec_op_count,
            })
        };

        ExtData {
            pk_cost: a.pk_cost + b.pk_cost + c.pk_cost + 3,
            has_free_verify: false,
            static_ops: 3 + a.static_ops + b.static_ops + c.static_ops,
            sat_data: SatData::fieldwise_max_opt(
                sat_concat(a.sat_data, b.sat_data),
                sat_concat(a.dissat_data, c.sat_data),
            ),
            dissat_data: sat_concat(a.dissat_data, c.dissat_data),
            timelock_info: TimelockInfo::combine_or(
                TimelockInfo::combine_and(a.timelock_info, b.timelock_info),
                c.timelock_info,
            ),
            multipath_len: a
                .multipath_len
                .intersect(b.multipath_len)
                .intersect(c.multipath_len),
            tree_height: 1 + cmp::max(a.tree_height, cmp::max(b.tree_height, c.tree_height)),
        }
    }

    /// Extra properties for the `thresh` fragment.
    pub fn threshold<S>(k: usize, n: usize, mut sub_ck: S) -> Self
    where
        S: FnMut(usize) -> Self,
    {
        let mut pk_cost = 1 + script_num_size(k); //Equal and k
        let mut static_ops = 0;
        let mut timelocks = Vec::with_capacity(n);
        let mut max_child_height = 0;

        let mut sat_dissat_vec = Vec::<(Option<SatData>, Option<SatData>)>::with_capacity(n);

        let mut dissat_data = Some(SatData {
            max_witness_stack_count: 0,
            max_witness_stack_size: 0,
            max_script_sig_size: 0,
            max_exec_stack_count: 0,
            max_exec_op_count: 0,
        });
        let mut multipath_len = MultipathLen::NoMultipathKeys;
        for i in 0..n {
            let sub = sub_ck(i);

            pk_cost += sub.pk_cost;
            static_ops += sub.static_ops;
            timelocks.push(sub.timelock_info);
            multipath_len = multipath_len.intersect(sub.multipath_len);

            // The thresh is dissatifiable iff all sub policies are dissatifiable.
            // If it can be dissatisfied this is done by just dissatisfying everything in order.
            dissat_data = dissat_data.zip(sub.dissat_data).map(|(acc, sub)| SatData {
                max_witness_stack_count: acc.max_witness_stack_count + sub.max_witness_stack_count,
                max_witness_stack_size: acc.max_witness_stack_size + sub.max_witness_stack_size,
                max_script_sig_size: acc.max_script_sig_size + sub.max_script_sig_size,
                max_exec_stack_count: cmp::max(acc.max_exec_stack_count, sub.max_exec_stack_count),
                max_exec_op_count: acc.max_exec_op_count + sub.max_exec_op_count,
            });
            // Satisfaction is more complicated.
            sat_dissat_vec.push((sub.sat_data, sub.dissat_data));

            max_child_height = cmp::max(max_child_height, sub.tree_height);
        }

        let mut max_witness_stack_count = None;
        let mut max_witness_stack_size = None;
        let mut max_script_sig_size = None;
        let mut max_exec_stack_count = None;
        let mut max_exec_op_count = None;
        for (field, proj, cmp) in [
            (
                &mut max_witness_stack_count,
                &(|data: SatData| data.max_witness_stack_count) as &dyn Fn(_) -> usize,
                &(|acc: usize, x: usize| acc + x) as &dyn Fn(_, _) -> usize,
            ),
            (
                &mut max_witness_stack_size,
                &(|data: SatData| data.max_witness_stack_size) as &dyn Fn(_) -> usize,
                &(|acc: usize, x: usize| acc + x) as &dyn Fn(_, _) -> usize,
            ),
            (
                &mut max_script_sig_size,
                &(|data: SatData| data.max_script_sig_size) as &dyn Fn(_) -> usize,
                &(|acc: usize, x: usize| acc + x) as &dyn Fn(_, _) -> usize,
            ),
            (
                &mut max_exec_stack_count,
                &(|data: SatData| data.max_exec_stack_count) as &dyn Fn(_) -> usize,
                // For each fragment except the first, we have the accumulated count on the
                // stack, which sits there during the whole child execution before
                // being ADDed to the result at the end.
                //
                // We use "acc > 0" as a hacky way to check "is this the first child
                // or not".
                &(|acc: usize, x: usize| cmp::max(acc, x + usize::from(acc > 0)))
                    as &dyn Fn(_, _) -> usize,
            ),
            (
                &mut max_exec_op_count,
                &(|data: SatData| data.max_exec_op_count) as &dyn Fn(_) -> usize,
                &(|acc: usize, x: usize| acc + x) as &dyn Fn(_, _) -> usize,
            ),
        ] {
            sat_dissat_vec.sort_by_key(|(sat, dissat)| {
                sat.zip(*dissat)
                    .map(|(sat, dissat)| proj(sat) as isize - proj(dissat) as isize)
            });
            *field =
                sat_dissat_vec
                    .iter()
                    .rev()
                    .enumerate()
                    .try_fold(0, |acc, (i, &(sat, dissat))| {
                        if i <= k {
                            sat.map(|x| cmp(acc, proj(x)))
                        } else {
                            dissat.map(|y| cmp(acc, proj(y)))
                        }
                    });
        }

        let sat_data = if let (
            Some(max_witness_stack_count),
            Some(max_witness_stack_size),
            Some(max_script_sig_size),
            Some(max_exec_stack_count),
            Some(max_exec_op_count),
        ) = (
            max_witness_stack_count,
            max_witness_stack_size,
            max_script_sig_size,
            max_exec_stack_count,
            max_exec_op_count,
        ) {
            Some(SatData {
                max_witness_stack_count,
                max_witness_stack_size,
                max_script_sig_size,
                max_exec_stack_count,
                max_exec_op_count,
            })
        } else {
            None
        };

        ExtData {
            pk_cost: pk_cost + n - 1, //all pk cost + (n-1)*ADD
            has_free_verify: true,
            static_ops: static_ops + 1 + (n - 1), // adds and equal
            sat_data,
            dissat_data,
            timelock_info: TimelockInfo::combine_threshold(k, timelocks),
            multipath_len,
            tree_height: max_child_height + 1,
        }
    }

    /// Compute the type of a fragment assuming all the children of
    /// Miniscript have been computed already.
    pub fn type_check<Pk, Ctx>(params: &ValidationParams, fragment: &Terminal<Pk, Ctx>) -> Self
    where
        Ctx: ScriptContext,
        Pk: MiniscriptKey,
    {
        let ret = match *fragment {
            Terminal::True => Self::TRUE,
            Terminal::False => Self::FALSE,
            Terminal::PkK(ref k) => Self::pk_k(params, k),
            Terminal::PkH(ref k) => Self::pk_h::<_, Ctx>(Some(k)),
            Terminal::RawPkH(..) => Self::pk_h::<Pk, Ctx>(None),
            Terminal::Multi(ref thresh) => Self::multi(thresh),
            Terminal::MultiA(ref thresh) => Self::multi_a(thresh),
            Terminal::After(t) => Self::after(t),
            Terminal::Older(t) => Self::older(t),
            Terminal::Sha256(..) => Self::sha256(),
            Terminal::Hash256(..) => Self::hash256(),
            Terminal::Ripemd160(..) => Self::ripemd160(),
            Terminal::Hash160(..) => Self::hash160(),
            Terminal::Alt(ref sub) => Self::cast_alt(sub.ext),
            Terminal::Swap(ref sub) => Self::cast_swap(sub.ext),
            Terminal::Check(ref sub) => Self::cast_check(sub.ext),
            Terminal::DupIf(ref sub) => Self::cast_dupif(sub.ext),
            Terminal::Verify(ref sub) => Self::cast_verify(sub.ext),
            Terminal::NonZero(ref sub) => Self::cast_nonzero(sub.ext),
            Terminal::ZeroNotEqual(ref sub) => Self::cast_zeronotequal(sub.ext),
            Terminal::AndB(ref l, ref r) => {
                let ltype = l.ext;
                let rtype = r.ext;
                Self::and_b(ltype, rtype)
            }
            Terminal::AndV(ref l, ref r) => {
                let ltype = l.ext;
                let rtype = r.ext;
                Self::and_v(ltype, rtype)
            }
            Terminal::OrB(ref l, ref r) => {
                let ltype = l.ext;
                let rtype = r.ext;
                Self::or_b(ltype, rtype)
            }
            Terminal::OrD(ref l, ref r) => {
                let ltype = l.ext;
                let rtype = r.ext;
                Self::or_d(ltype, rtype)
            }
            Terminal::OrC(ref l, ref r) => {
                let ltype = l.ext;
                let rtype = r.ext;
                Self::or_c(ltype, rtype)
            }
            Terminal::OrI(ref l, ref r) => {
                let ltype = l.ext;
                let rtype = r.ext;
                Self::or_i(ltype, rtype)
            }
            Terminal::AndOr(ref a, ref b, ref c) => {
                let atype = a.ext;
                let btype = b.ext;
                let ctype = c.ext;
                Self::and_or(atype, btype, ctype)
            }
            Terminal::Thresh(ref thresh) => {
                Self::threshold(thresh.k(), thresh.n(), |n| thresh.data()[n].ext)
            }
        };
        ret
    }

    /// Accessor for the sum of the static and executed op counts, in the satisfaction
    /// case.
    pub(crate) fn sat_op_count(&self) -> Option<usize> {
        self.sat_data
            .map(|data| self.static_ops + data.max_exec_op_count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn combine_threshold() {
        let mut time1 = TimelockInfo::default();
        let mut time2 = TimelockInfo::default();
        let mut height = TimelockInfo::default();

        time1.csv_with_time = true;
        time2.csv_with_time = true;
        height.csv_with_height = true;

        // For threshold of 1, multiple absolute timelocks do not effect spendable path.
        let v = vec![time1, time2, height];
        let combined = TimelockInfo::combine_threshold(1, v);
        assert!(!combined.contains_unspendable_path());

        // For threshold of 2, multiple absolute timelocks cannot be spent in a single path.
        let v = vec![time1, time2, height];
        let combined = TimelockInfo::combine_threshold(2, v);
        assert!(combined.contains_unspendable_path())
    }
}
