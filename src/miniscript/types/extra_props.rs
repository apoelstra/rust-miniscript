// SPDX-License-Identifier: CC0-1.0

//! Other miscellaneous type properties which are not related to
//! correctness or malleability.

use core::cmp;
use core::iter::once;

use super::ScriptContext;
use crate::miniscript::context::SigType;
use crate::prelude::*;
use crate::{script_num_size, AbsLockTime, MiniscriptKey, RelLockTime, Terminal};

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

/// Helper struct to store information about op code limits. Note that this only
/// counts the non-push opcodes. This is not relevant for TapScript context
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct OpLimits {
    /// The worst case static(executed + unexecuted) ops-count for this Miniscript fragment.
    pub count: usize,
    /// The worst case additional ops-count for satisfying this Miniscript fragment.
    pub sat: Option<usize>,
    /// The worst case additional ops-count for dissatisfying this Miniscript fragment.
    pub nsat: Option<usize>,
}

impl OpLimits {
    /// Creates a new instance of [`OpLimits`]
    pub const fn new(op_static: usize, op_sat: Option<usize>, op_nsat: Option<usize>) -> Self {
        OpLimits { count: op_static, sat: op_sat, nsat: op_nsat }
    }

    /// Worst case opcode count when this element is satisfied
    pub fn op_count(&self) -> Option<usize> { opt_add(Some(self.count), self.sat) }
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

/// Structure representing the extra type properties of a fragment.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct ExtData {
    /// The number of bytes needed to encode its scriptpubkey
    pub pk_cost: usize,
    /// Whether this fragment can be verify-wrapped for free
    pub has_free_verify: bool,
    /// Opcode limits for this fragment.
    pub ops: OpLimits,
    /// The worst case number of stack elements for satisfying this Miniscript fragment.
    pub stack_elem_count_sat: Option<usize>,
    /// The worst case number of stack elements for dissatisfying this Miniscript fragment.
    pub stack_elem_count_dissat: Option<usize>,
    /// Maximum size, in bytes, of a satisfying witness. First elements is the cost for the
    /// witness stack, the second one is the cost for scriptSig.
    /// All signatures are assumed to be 73 bytes in size, including the
    /// length prefix (segwit) or push opcode (pre-segwit) and sighash
    /// postfix.
    pub max_sat_size: Option<(usize, usize)>,
    /// Maximum dissatisfaction cost, in bytes, of a Miniscript fragment. First elements is
    /// the cost for the witness stack, the second one is the cost for scriptSig.
    pub max_dissat_size: Option<(usize, usize)>,
    /// The timelock info about heightlocks and timelocks
    pub timelock_info: TimelockInfo,
    /// Maximum stack + alt stack size during satisfaction execution
    /// This does **not** include initial witness elements. This element only captures
    /// the additional elements that are pushed during execution.
    pub exec_stack_elem_count_sat: Option<usize>,
    /// Maximum stack + alt stack size during dissat execution
    /// This does **not** include initial witness elements. This element only captures
    /// the additional elements that are pushed during execution.
    pub exec_stack_elem_count_dissat: Option<usize>,
    /// The miniscript tree depth/height of this node.
    /// Used for checking the max depth of the miniscript tree to prevent stack overflow.
    pub tree_height: usize,
}

impl ExtData {
    /// Extra data for the `0` combinator
    pub const FALSE: Self = ExtData {
        pk_cost: 1,
        has_free_verify: false,
        ops: OpLimits::new(0, None, Some(0)),
        stack_elem_count_sat: None,
        stack_elem_count_dissat: Some(0),
        max_sat_size: None,
        max_dissat_size: Some((0, 0)),
        timelock_info: TimelockInfo::new(),
        exec_stack_elem_count_sat: None,
        exec_stack_elem_count_dissat: Some(1),
        tree_height: 0,
    };

    /// Extra data for the `1` combinator
    pub const TRUE: Self = ExtData {
        pk_cost: 1,
        has_free_verify: false,
        ops: OpLimits::new(0, Some(0), None),
        stack_elem_count_sat: Some(0),
        stack_elem_count_dissat: None,
        max_sat_size: Some((0, 0)),
        max_dissat_size: None,
        timelock_info: TimelockInfo::new(),
        exec_stack_elem_count_sat: Some(1),
        exec_stack_elem_count_dissat: None,
        tree_height: 0,
    };
}

impl ExtData {
    /// Confirm invariants of the extra property checker.
    pub fn sanity_checks(&self) {
        debug_assert_eq!(
            self.stack_elem_count_sat.is_some(),
            self.exec_stack_elem_count_sat.is_some()
        );
        debug_assert_eq!(
            self.stack_elem_count_dissat.is_some(),
            self.exec_stack_elem_count_dissat.is_some()
        );
    }

    /// Extra properties for the `pk_k` fragment.
    pub fn pk_k<Ctx: ScriptContext>() -> Self {
        ExtData {
            pk_cost: match Ctx::sig_type() {
                SigType::Ecdsa => 34,
                SigType::Schnorr => 33,
            },
            has_free_verify: false,
            ops: OpLimits::new(0, Some(0), Some(0)),
            stack_elem_count_sat: Some(1),
            stack_elem_count_dissat: Some(1),
            max_sat_size: match Ctx::sig_type() {
                SigType::Ecdsa => Some((73, 73)),
                SigType::Schnorr => Some((66, 66)),
            },
            max_dissat_size: Some((1, 1)),
            timelock_info: TimelockInfo::default(),
            exec_stack_elem_count_sat: Some(1), // pushes the pk
            exec_stack_elem_count_dissat: Some(1),
            tree_height: 0,
        }
    }

    /// Extra properties for the `pk_h` fragment.
    pub fn pk_h<Ctx: ScriptContext>() -> Self {
        ExtData {
            pk_cost: 24,
            has_free_verify: false,
            ops: OpLimits::new(3, Some(0), Some(0)),
            stack_elem_count_sat: Some(2),
            stack_elem_count_dissat: Some(2),
            max_sat_size: match Ctx::sig_type() {
                SigType::Ecdsa => Some((34 + 73, 34 + 73)),
                SigType::Schnorr => Some((66 + 33, 33 + 66)),
            },
            max_dissat_size: match Ctx::sig_type() {
                SigType::Ecdsa => Some((35, 35)),
                SigType::Schnorr => Some((34, 34)),
            },
            timelock_info: TimelockInfo::default(),
            exec_stack_elem_count_sat: Some(2), // dup and hash push
            exec_stack_elem_count_dissat: Some(2),
            tree_height: 0,
        }
    }

    /// Extra properties for the `multi` fragment.
    pub fn multi(k: usize, n: usize) -> Self {
        let num_cost = match (k > 16, n > 16) {
            (true, true) => 4,
            (false, true) => 3,
            (true, false) => 3,
            (false, false) => 2,
        };
        ExtData {
            pk_cost: num_cost + 34 * n + 1,
            has_free_verify: true,
            // Multi is the only case because of which we need to count additional
            // executed opcodes.
            ops: OpLimits::new(1, Some(n), Some(n)),
            stack_elem_count_sat: Some(k + 1),
            stack_elem_count_dissat: Some(k + 1),
            max_sat_size: Some((1 + 73 * k, 1 + 73 * k)),
            max_dissat_size: Some((1 + k, 1 + k)),
            timelock_info: TimelockInfo::new(),
            exec_stack_elem_count_sat: Some(n), // n pks
            exec_stack_elem_count_dissat: Some(n),
            tree_height: 0,
        }
    }

    /// Extra properties for the `multi_a` fragment.
    pub fn multi_a(k: usize, n: usize) -> Self {
        let num_cost = match (k > 16, n > 16) {
            (true, true) => 4,
            (false, true) => 3,
            (true, false) => 3,
            (false, false) => 2,
        };
        ExtData {
            pk_cost: num_cost + 33 * n /*pks*/ + (n - 1) /*checksigadds*/ + 1,
            has_free_verify: true,
            // These numbers are irrelevant here are there is no op limit in tapscript
            ops: OpLimits::new(n, Some(0), Some(0)),
            stack_elem_count_sat: Some(n),
            stack_elem_count_dissat: Some(n),
            max_sat_size: Some(((n - k) + 66 * k, (n - k) + 66 * k)),
            max_dissat_size: Some((n, n)),
            timelock_info: TimelockInfo::new(),
            exec_stack_elem_count_sat: Some(2), // the two nums before num equal verify
            exec_stack_elem_count_dissat: Some(2),
            tree_height: 0,
        }
    }

    /// Extra properties for the `sha256` fragment.
    pub const fn sha256() -> Self {
        ExtData {
            pk_cost: 33 + 6,
            has_free_verify: true,
            ops: OpLimits::new(4, Some(0), Some(0)),
            stack_elem_count_sat: Some(1),
            stack_elem_count_dissat: Some(1),
            max_sat_size: Some((33, 33)),
            max_dissat_size: Some((33, 33)),
            timelock_info: TimelockInfo::new(),
            exec_stack_elem_count_sat: Some(2), // either size <32> or <hash256> <32 byte>
            exec_stack_elem_count_dissat: Some(2),
            tree_height: 0,
        }
    }

    /// Extra properties for the `hash256` fragment.
    pub const fn hash256() -> Self {
        ExtData {
            pk_cost: 33 + 6,
            has_free_verify: true,
            ops: OpLimits::new(4, Some(0), Some(0)),
            stack_elem_count_sat: Some(1),
            stack_elem_count_dissat: Some(1),
            max_sat_size: Some((33, 33)),
            max_dissat_size: Some((33, 33)),
            timelock_info: TimelockInfo::new(),
            exec_stack_elem_count_sat: Some(2), // either size <32> or <hash256> <32 byte>
            exec_stack_elem_count_dissat: Some(2),
            tree_height: 0,
        }
    }

    /// Extra properties for the `ripemd160` fragment.
    pub const fn ripemd160() -> Self {
        ExtData {
            pk_cost: 21 + 6,
            has_free_verify: true,
            ops: OpLimits::new(4, Some(0), Some(0)),
            stack_elem_count_sat: Some(1),
            stack_elem_count_dissat: Some(1),
            max_sat_size: Some((33, 33)),
            max_dissat_size: Some((33, 33)),
            timelock_info: TimelockInfo::new(),
            exec_stack_elem_count_sat: Some(2), // either size <32> or <hash256> <20 byte>
            exec_stack_elem_count_dissat: Some(2),
            tree_height: 0,
        }
    }

    /// Extra properties for the `hash160` fragment.
    pub const fn hash160() -> Self {
        ExtData {
            pk_cost: 21 + 6,
            has_free_verify: true,
            ops: OpLimits::new(4, Some(0), Some(0)),
            stack_elem_count_sat: Some(1),
            stack_elem_count_dissat: Some(1),
            max_sat_size: Some((33, 33)),
            max_dissat_size: Some((33, 33)),
            timelock_info: TimelockInfo::new(),
            exec_stack_elem_count_sat: Some(2), // either size <32> or <hash256> <20 byte>
            exec_stack_elem_count_dissat: Some(2),
            tree_height: 0,
        }
    }

    /// Extra properties for the `after` fragment.
    pub fn after(t: AbsLockTime) -> Self {
        ExtData {
            pk_cost: script_num_size(t.to_consensus_u32() as usize) + 1,
            has_free_verify: false,
            ops: OpLimits::new(1, Some(0), None),
            stack_elem_count_sat: Some(0),
            stack_elem_count_dissat: None,
            max_sat_size: Some((0, 0)),
            max_dissat_size: None,
            timelock_info: TimelockInfo {
                csv_with_height: false,
                csv_with_time: false,
                cltv_with_height: t.is_block_height(),
                cltv_with_time: t.is_block_time(),
                contains_combination: false,
            },
            exec_stack_elem_count_sat: Some(1), // <t>
            exec_stack_elem_count_dissat: None,
            tree_height: 0,
        }
    }

    /// Extra properties for the `older` fragment.
    pub fn older(t: RelLockTime) -> Self {
        ExtData {
            pk_cost: script_num_size(t.to_consensus_u32() as usize) + 1,
            has_free_verify: false,
            ops: OpLimits::new(1, Some(0), None),
            stack_elem_count_sat: Some(0),
            stack_elem_count_dissat: None,
            max_sat_size: Some((0, 0)),
            max_dissat_size: None,
            timelock_info: TimelockInfo {
                csv_with_height: t.is_height_locked(),
                csv_with_time: t.is_time_locked(),
                cltv_with_height: false,
                cltv_with_time: false,
                contains_combination: false,
            },
            exec_stack_elem_count_sat: Some(1), // <t>
            exec_stack_elem_count_dissat: None,
            tree_height: 0,
        }
    }

    /// Extra properties for the `a:` fragment.
    pub const fn cast_alt(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 2,
            has_free_verify: false,
            ops: OpLimits::new(2 + self.ops.count, self.ops.sat, self.ops.nsat),
            stack_elem_count_sat: self.stack_elem_count_sat,
            stack_elem_count_dissat: self.stack_elem_count_dissat,
            max_sat_size: self.max_sat_size,
            max_dissat_size: self.max_dissat_size,
            timelock_info: self.timelock_info,
            exec_stack_elem_count_sat: self.exec_stack_elem_count_sat,
            exec_stack_elem_count_dissat: self.exec_stack_elem_count_dissat,
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `s:` fragment.
    pub const fn cast_swap(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 1,
            has_free_verify: self.has_free_verify,
            ops: OpLimits::new(1 + self.ops.count, self.ops.sat, self.ops.nsat),
            stack_elem_count_sat: self.stack_elem_count_sat,
            stack_elem_count_dissat: self.stack_elem_count_dissat,
            max_sat_size: self.max_sat_size,
            max_dissat_size: self.max_dissat_size,
            timelock_info: self.timelock_info,
            exec_stack_elem_count_sat: self.exec_stack_elem_count_sat,
            exec_stack_elem_count_dissat: self.exec_stack_elem_count_dissat,
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `c:` fragment.
    pub const fn cast_check(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 1,
            has_free_verify: true,
            ops: OpLimits::new(1 + self.ops.count, self.ops.sat, self.ops.nsat),
            stack_elem_count_sat: self.stack_elem_count_sat,
            stack_elem_count_dissat: self.stack_elem_count_dissat,
            max_sat_size: self.max_sat_size,
            max_dissat_size: self.max_dissat_size,
            timelock_info: self.timelock_info,
            exec_stack_elem_count_sat: self.exec_stack_elem_count_sat,
            exec_stack_elem_count_dissat: self.exec_stack_elem_count_dissat,
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `d:` fragment.
    pub fn cast_dupif(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 3,
            has_free_verify: false,
            ops: OpLimits::new(3 + self.ops.count, self.ops.sat, Some(0)),
            stack_elem_count_sat: self.stack_elem_count_sat.map(|x| x + 1),
            stack_elem_count_dissat: Some(1),
            max_sat_size: self.max_sat_size.map(|(w, s)| (w + 2, s + 1)),
            max_dissat_size: Some((1, 1)),
            timelock_info: self.timelock_info,
            // Technically max(1, self.exec_stack_elem_count_sat), but all miniscript expressions
            // that can be satisfied push at least one thing onto the stack.
            // Even all V types push something onto the stack and then remove them
            exec_stack_elem_count_sat: self.exec_stack_elem_count_sat,
            exec_stack_elem_count_dissat: Some(1),
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `v:` fragment.
    pub fn cast_verify(self) -> Self {
        let verify_cost = usize::from(!self.has_free_verify);
        ExtData {
            pk_cost: self.pk_cost + usize::from(!self.has_free_verify),
            has_free_verify: false,
            ops: OpLimits::new(verify_cost + self.ops.count, self.ops.sat, None),
            stack_elem_count_sat: self.stack_elem_count_sat,
            stack_elem_count_dissat: None,
            max_sat_size: self.max_sat_size,
            max_dissat_size: None,
            timelock_info: self.timelock_info,
            exec_stack_elem_count_sat: self.exec_stack_elem_count_sat,
            exec_stack_elem_count_dissat: None,
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `j:` fragment.
    pub const fn cast_nonzero(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 4,
            has_free_verify: false,
            ops: OpLimits::new(4 + self.ops.count, self.ops.sat, Some(0)),
            stack_elem_count_sat: self.stack_elem_count_sat,
            stack_elem_count_dissat: Some(1),
            max_sat_size: self.max_sat_size,
            max_dissat_size: Some((1, 1)),
            timelock_info: self.timelock_info,
            exec_stack_elem_count_sat: self.exec_stack_elem_count_sat,
            exec_stack_elem_count_dissat: Some(1),
            tree_height: self.tree_height + 1,
        }
    }

    /// Extra properties for the `n:` fragment.
    pub const fn cast_zeronotequal(self) -> Self {
        ExtData {
            pk_cost: self.pk_cost + 1,
            has_free_verify: false,
            ops: OpLimits::new(1 + self.ops.count, self.ops.sat, self.ops.nsat),
            stack_elem_count_sat: self.stack_elem_count_sat,
            stack_elem_count_dissat: self.stack_elem_count_dissat,
            max_sat_size: self.max_sat_size,
            max_dissat_size: self.max_dissat_size,
            timelock_info: self.timelock_info,
            // Technically max(1, self.exec_stack_elem_count_sat), same rationale as cast_dupif
            exec_stack_elem_count_sat: self.exec_stack_elem_count_sat,
            exec_stack_elem_count_dissat: self.exec_stack_elem_count_dissat,
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
            ops: OpLimits::new(
                1 + l.ops.count + r.ops.count,
                opt_add(l.ops.sat, r.ops.sat),
                opt_add(l.ops.nsat, r.ops.nsat),
            ),
            stack_elem_count_sat: l
                .stack_elem_count_sat
                .and_then(|l| r.stack_elem_count_sat.map(|r| l + r)),
            stack_elem_count_dissat: l
                .stack_elem_count_dissat
                .and_then(|l| r.stack_elem_count_dissat.map(|r| l + r)),
            max_sat_size: l
                .max_sat_size
                .and_then(|(lw, ls)| r.max_sat_size.map(|(rw, rs)| (lw + rw, ls + rs))),
            max_dissat_size: l
                .max_dissat_size
                .and_then(|(lw, ls)| r.max_dissat_size.map(|(rw, rs)| (lw + rw, ls + rs))),
            timelock_info: TimelockInfo::combine_and(l.timelock_info, r.timelock_info),
            // Left element leaves a stack result on the stack top and then right element is evaluated
            // Therefore + 1 is added to execution size of second element
            exec_stack_elem_count_sat: opt_max(
                l.exec_stack_elem_count_sat,
                r.exec_stack_elem_count_sat.map(|x| x + 1),
            ),
            exec_stack_elem_count_dissat: opt_max(
                l.exec_stack_elem_count_dissat,
                r.exec_stack_elem_count_dissat.map(|x| x + 1),
            ),
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `and_v` fragment.
    pub fn and_v(l: Self, r: Self) -> Self {
        ExtData {
            pk_cost: l.pk_cost + r.pk_cost,
            has_free_verify: r.has_free_verify,
            ops: OpLimits::new(l.ops.count + r.ops.count, opt_add(l.ops.sat, r.ops.sat), None),
            stack_elem_count_sat: l
                .stack_elem_count_sat
                .and_then(|l| r.stack_elem_count_sat.map(|r| l + r)),
            stack_elem_count_dissat: None,
            max_sat_size: l
                .max_sat_size
                .and_then(|(lw, ls)| r.max_sat_size.map(|(rw, rs)| (lw + rw, ls + rs))),
            max_dissat_size: None,
            timelock_info: TimelockInfo::combine_and(l.timelock_info, r.timelock_info),
            // [X] leaves no element after evaluation, hence this is the max
            exec_stack_elem_count_sat: opt_max(
                l.exec_stack_elem_count_sat,
                r.exec_stack_elem_count_sat,
            ),
            exec_stack_elem_count_dissat: None,
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `or_b` fragment.
    pub fn or_b(l: Self, r: Self) -> Self {
        ExtData {
            pk_cost: l.pk_cost + r.pk_cost + 1,
            has_free_verify: false,
            ops: OpLimits::new(
                l.ops.count + r.ops.count + 1,
                cmp::max(opt_add(l.ops.sat, r.ops.nsat), opt_add(l.ops.nsat, r.ops.sat)),
                opt_add(l.ops.nsat, r.ops.nsat),
            ),
            stack_elem_count_sat: cmp::max(
                l.stack_elem_count_sat
                    .and_then(|l| r.stack_elem_count_dissat.map(|r| l + r)),
                l.stack_elem_count_dissat
                    .and_then(|l| r.stack_elem_count_sat.map(|r| l + r)),
            ),
            stack_elem_count_dissat: l
                .stack_elem_count_dissat
                .and_then(|l| r.stack_elem_count_dissat.map(|r| l + r)),
            max_sat_size: cmp::max(
                l.max_sat_size
                    .and_then(|(lw, ls)| r.max_dissat_size.map(|(rw, rs)| (lw + rw, ls + rs))),
                l.max_dissat_size
                    .and_then(|(lw, ls)| r.max_sat_size.map(|(rw, rs)| (lw + rw, ls + rs))),
            ),
            max_dissat_size: l
                .max_dissat_size
                .and_then(|(lw, ls)| r.max_dissat_size.map(|(rw, rs)| (lw + rw, ls + rs))),
            timelock_info: TimelockInfo::combine_or(l.timelock_info, r.timelock_info),
            exec_stack_elem_count_sat: cmp::max(
                opt_max(l.exec_stack_elem_count_sat, r.exec_stack_elem_count_dissat.map(|x| x + 1)),
                opt_max(l.exec_stack_elem_count_dissat, r.exec_stack_elem_count_sat.map(|x| x + 1)),
            ),
            exec_stack_elem_count_dissat: opt_max(
                l.exec_stack_elem_count_dissat,
                r.exec_stack_elem_count_dissat.map(|x| x + 1),
            ),
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `or_d` fragment.
    pub fn or_d(l: Self, r: Self) -> Self {
        ExtData {
            pk_cost: l.pk_cost + r.pk_cost + 3,
            has_free_verify: false,
            ops: OpLimits::new(
                l.ops.count + r.ops.count + 3,
                cmp::max(l.ops.sat, opt_add(l.ops.nsat, r.ops.sat)),
                opt_add(l.ops.nsat, r.ops.nsat),
            ),
            stack_elem_count_sat: cmp::max(
                l.stack_elem_count_sat,
                l.stack_elem_count_dissat
                    .and_then(|l_dis| r.stack_elem_count_sat.map(|r_sat| r_sat + l_dis)),
            ),
            stack_elem_count_dissat: l
                .stack_elem_count_dissat
                .and_then(|l_dis| r.stack_elem_count_dissat.map(|r_dis| r_dis + l_dis)),
            max_sat_size: cmp::max(
                l.max_sat_size,
                l.max_dissat_size
                    .and_then(|(lw, ls)| r.max_sat_size.map(|(rw, rs)| (lw + rw, ls + rs))),
            ),
            max_dissat_size: l
                .max_dissat_size
                .and_then(|(lw, ls)| r.max_dissat_size.map(|(rw, rs)| (lw + rw, ls + rs))),
            timelock_info: TimelockInfo::combine_or(l.timelock_info, r.timelock_info),
            exec_stack_elem_count_sat: cmp::max(
                l.exec_stack_elem_count_sat,
                opt_max(r.exec_stack_elem_count_sat, l.exec_stack_elem_count_dissat),
            ),
            exec_stack_elem_count_dissat: opt_max(
                l.exec_stack_elem_count_dissat,
                r.exec_stack_elem_count_dissat.map(|x| x + 1),
            ),
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `or_c` fragment.
    pub fn or_c(l: Self, r: Self) -> Self {
        ExtData {
            pk_cost: l.pk_cost + r.pk_cost + 2,
            has_free_verify: false,
            ops: OpLimits::new(
                l.ops.count + r.ops.count + 2,
                cmp::max(l.ops.sat, opt_add(l.ops.nsat, r.ops.sat)),
                None,
            ),
            stack_elem_count_sat: cmp::max(
                l.stack_elem_count_sat,
                l.stack_elem_count_dissat
                    .and_then(|l_dis| r.stack_elem_count_sat.map(|r_sat| r_sat + l_dis)),
            ),
            stack_elem_count_dissat: None,
            max_sat_size: cmp::max(
                l.max_sat_size,
                l.max_dissat_size
                    .and_then(|(lw, ls)| r.max_sat_size.map(|(rw, rs)| (lw + rw, ls + rs))),
            ),
            max_dissat_size: None,
            timelock_info: TimelockInfo::combine_or(l.timelock_info, r.timelock_info),
            exec_stack_elem_count_sat: cmp::max(
                l.exec_stack_elem_count_sat,
                opt_max(r.exec_stack_elem_count_sat, l.exec_stack_elem_count_dissat),
            ),
            exec_stack_elem_count_dissat: None,
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `or_i` fragment.
    pub fn or_i(l: Self, r: Self) -> Self {
        ExtData {
            pk_cost: l.pk_cost + r.pk_cost + 3,
            has_free_verify: false,
            ops: OpLimits::new(
                l.ops.count + r.ops.count + 3,
                cmp::max(l.ops.sat, r.ops.sat),
                cmp::max(l.ops.nsat, r.ops.nsat),
            ),
            stack_elem_count_sat: match (l.stack_elem_count_sat, r.stack_elem_count_sat) {
                (Some(l), Some(r)) => Some(1 + cmp::max(l, r)),
                (Some(l), None) => Some(1 + l),
                (None, Some(r)) => Some(1 + r),
                (None, None) => None,
            },
            stack_elem_count_dissat: match (l.stack_elem_count_dissat, r.stack_elem_count_dissat) {
                (Some(l), Some(r)) => Some(1 + cmp::max(l, r)),
                (Some(l), None) => Some(1 + l),
                (None, Some(r)) => Some(1 + r),
                (None, None) => None,
            },
            max_sat_size: cmp::max(
                l.max_sat_size.map(|(w, s)| (w + 2, s + 1)),
                r.max_sat_size.map(|(w, s)| (w + 1, s + 1)),
            ),
            max_dissat_size: match (l.max_dissat_size, r.max_dissat_size) {
                (Some(l), Some(r)) => {
                    let max = cmp::max(l, r);
                    Some((1 + max.0, 1 + max.1))
                }
                (None, Some(r)) => Some((1 + r.0, 1 + r.1)),
                (Some(l), None) => Some((2 + l.0, 1 + l.1)),
                (None, None) => None,
            },
            timelock_info: TimelockInfo::combine_or(l.timelock_info, r.timelock_info),
            exec_stack_elem_count_sat: cmp::max(
                l.exec_stack_elem_count_sat,
                r.exec_stack_elem_count_sat,
            ),
            exec_stack_elem_count_dissat: cmp::max(
                l.exec_stack_elem_count_dissat,
                r.exec_stack_elem_count_dissat,
            ),
            tree_height: 1 + cmp::max(l.tree_height, r.tree_height),
        }
    }

    /// Extra properties for the `andor` fragment.
    pub fn and_or(a: Self, b: Self, c: Self) -> Self {
        ExtData {
            pk_cost: a.pk_cost + b.pk_cost + c.pk_cost + 3,
            has_free_verify: false,
            ops: OpLimits::new(
                a.ops.count + b.ops.count + c.ops.count + 3,
                cmp::max(opt_add(a.ops.sat, b.ops.sat), opt_add(a.ops.nsat, c.ops.sat)),
                opt_add(a.ops.nsat, c.ops.nsat),
            ),
            stack_elem_count_sat: cmp::max(
                a.stack_elem_count_sat
                    .and_then(|a| b.stack_elem_count_sat.map(|b| b + a)),
                a.stack_elem_count_dissat
                    .and_then(|a_dis| c.stack_elem_count_sat.map(|c| c + a_dis)),
            ),
            stack_elem_count_dissat: a
                .stack_elem_count_dissat
                .and_then(|a_dis| c.stack_elem_count_dissat.map(|c| c + a_dis)),
            max_sat_size: cmp::max(
                a.max_sat_size
                    .and_then(|(wa, sa)| b.max_sat_size.map(|(wb, sb)| (wa + wb, sa + sb))),
                a.max_dissat_size
                    .and_then(|(wa, sa)| c.max_sat_size.map(|(wc, sc)| (wa + wc, sa + sc))),
            ),
            max_dissat_size: a
                .max_dissat_size
                .and_then(|(wa, sa)| c.max_dissat_size.map(|(wc, sc)| (wa + wc, sa + sc))),
            timelock_info: TimelockInfo::combine_or(
                TimelockInfo::combine_and(a.timelock_info, b.timelock_info),
                c.timelock_info,
            ),
            exec_stack_elem_count_sat: cmp::max(
                opt_max(a.exec_stack_elem_count_sat, b.exec_stack_elem_count_sat),
                opt_max(c.exec_stack_elem_count_sat, a.exec_stack_elem_count_dissat),
            ),
            exec_stack_elem_count_dissat: opt_max(
                a.exec_stack_elem_count_dissat,
                c.exec_stack_elem_count_dissat,
            ),
            tree_height: 1 + cmp::max(a.tree_height, cmp::max(b.tree_height, c.tree_height)),
        }
    }

    /// Extra properties for the `thresh` fragment.
    pub fn threshold<S>(k: usize, n: usize, mut sub_ck: S) -> Self
    where
        S: FnMut(usize) -> Self,
    {
        let mut pk_cost = 1 + script_num_size(k); //Equal and k
        let mut ops_count = 0;
        let mut ops_count_sat_vec = Vec::with_capacity(n);
        let mut ops_count_nsat_sum = 0;
        let mut timelocks = Vec::with_capacity(n);
        let mut stack_elem_count_sat_vec = Vec::with_capacity(n);
        let mut stack_elem_count_dissat = Some(0);
        let mut max_sat_size_vec = Vec::with_capacity(n);
        let mut max_dissat_size = Some((0, 0));
        // the max element count is same as max sat element count when satisfying one element + 1
        let mut exec_stack_elem_count_sat_vec = Vec::with_capacity(n);
        let mut exec_stack_elem_count_dissat = Some(0);
        let mut max_child_height = 0;

        for i in 0..n {
            let sub = sub_ck(i);

            pk_cost += sub.pk_cost;
            ops_count += sub.ops.count;
            timelocks.push(sub.timelock_info);

            if let Some(n_items) = sub.stack_elem_count_dissat {
                stack_elem_count_dissat = stack_elem_count_dissat.map(|x| x + n_items);
                let sub_dissat_size = sub
                    .max_dissat_size
                    .expect("dissat_size is None but not stack_elem?");
                max_dissat_size =
                    max_dissat_size.map(|(w, s)| (w + sub_dissat_size.0, s + sub_dissat_size.1));
            } else {
                // The thresh is dissatifiable iff all sub policies are dissatifiable
                stack_elem_count_dissat = None;
            }
            stack_elem_count_sat_vec.push((sub.stack_elem_count_sat, sub.stack_elem_count_dissat));
            max_sat_size_vec.push((sub.max_sat_size, sub.max_sat_size));

            let sub_nsat = sub.ops.nsat.expect("Thresh children must be d");
            ops_count_nsat_sum += sub_nsat;
            ops_count_sat_vec.push((sub.ops.sat, sub_nsat));
            exec_stack_elem_count_sat_vec
                .push((sub.exec_stack_elem_count_sat, sub.exec_stack_elem_count_dissat));
            exec_stack_elem_count_dissat =
                opt_max(exec_stack_elem_count_dissat, sub.exec_stack_elem_count_dissat);
            max_child_height = cmp::max(max_child_height, sub.tree_height);
        }

        stack_elem_count_sat_vec.sort_by(sat_minus_option_dissat);
        let stack_elem_count_sat =
            stack_elem_count_sat_vec
                .iter()
                .rev()
                .enumerate()
                .try_fold(0, |acc, (i, &(x, y))| {
                    if i <= k {
                        x.map(|x| acc + x)
                    } else {
                        y.map(|y| acc + y)
                    }
                });

        exec_stack_elem_count_sat_vec.sort_by(sat_minus_option_dissat);
        let exec_stack_elem_count_sat = exec_stack_elem_count_sat_vec
            .iter()
            .rev()
            .enumerate()
            .try_fold(0, |acc, (i, &(x, y))| {
                if i <= k {
                    x.map(|x| acc + x)
                } else {
                    y.map(|y| acc + y)
                }
            });

        // FIXME: Maybe make the ExtData struct aware of Ctx and add a one_cost() method here ?
        max_sat_size_vec.sort_by(sat_minus_dissat_witness);
        let max_sat_size =
            max_sat_size_vec
                .iter()
                .enumerate()
                .try_fold((0, 0), |acc, (i, &(x, y))| {
                    if i <= k {
                        x.map(|(x0, x1)| (acc.0 + x0, acc.1 + x1))
                    } else {
                        y.map(|(y0, y1)| (acc.0 + y0, acc.1 + y1))
                    }
                });

        ops_count_sat_vec.sort_by(sat_minus_dissat);
        let op_count_sat = ops_count_sat_vec
            .iter()
            .enumerate()
            .try_fold(0, |acc, (i, &(x, y))| {
                if i <= k {
                    x.map(|x| acc + x)
                } else {
                    Some(acc + y)
                }
            });

        ExtData {
            pk_cost: pk_cost + n - 1, //all pk cost + (n-1)*ADD
            has_free_verify: true,
            ops: OpLimits::new(
                ops_count + 1 + (n - 1), // adds and equal
                op_count_sat,
                Some(ops_count_nsat_sum),
            ),
            stack_elem_count_sat,
            stack_elem_count_dissat,
            max_sat_size,
            max_dissat_size,
            timelock_info: TimelockInfo::combine_threshold(k, timelocks),
            exec_stack_elem_count_sat,
            exec_stack_elem_count_dissat,
            tree_height: max_child_height + 1,
        }
    }

    /// Compute the type of a fragment assuming all the children of
    /// Miniscript have been computed already.
    pub fn type_check<Pk, Ctx>(fragment: &Terminal<Pk, Ctx>) -> Self
    where
        Ctx: ScriptContext,
        Pk: MiniscriptKey,
    {
        let ret = match *fragment {
            Terminal::True => Self::TRUE,
            Terminal::False => Self::FALSE,
            Terminal::PkK(..) => Self::pk_k::<Ctx>(),
            Terminal::PkH(..) | Terminal::RawPkH(..) => Self::pk_h::<Ctx>(),
            Terminal::Multi(ref thresh) => Self::multi(thresh.k(), thresh.n()),
            Terminal::MultiA(ref thresh) => Self::multi_a(thresh.k(), thresh.n()),
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
        ret.sanity_checks();
        ret
    }
}

// Function to pass to sort_by. Sort by (satisfaction cost - dissatisfaction cost).
//
// We sort by (satisfaction cost - dissatisfaction cost) to make a worst-case (the most
// costy satisfactions are satisfied, the most costy dissatisfactions are dissatisfied).
//
// Args are of form: (<count_sat>, <count_dissat>)
fn sat_minus_dissat(a: &(Option<usize>, usize), b: &(Option<usize>, usize)) -> cmp::Ordering {
    a.0.map(|x| x as isize - a.1 as isize)
        .cmp(&b.0.map(|x| x as isize - b.1 as isize))
}

// Function to pass to sort_by. Sort by (satisfaction cost - dissatisfaction cost).
//
// We sort by (satisfaction cost - dissatisfaction cost) to make a worst-case (the most
// costy satisfactions are satisfied, the most costy dissatisfactions are dissatisfied).
//
// Args are of form: (<count_sat>, <count_dissat>)
fn sat_minus_option_dissat(
    a: &(Option<usize>, Option<usize>),
    b: &(Option<usize>, Option<usize>),
) -> cmp::Ordering {
    a.0.map(|x| a.1.map(|y| x as isize - y as isize))
        .cmp(&b.0.map(|x| b.1.map(|y| x as isize - y as isize)))
}

// Function to pass to sort_by. Sort by (satisfaction cost - dissatisfaction cost) of cost of witness.
//
// Args are of form: (<max_sat_size>, <count_dissat_size>)
// max_[dis]sat_size of form: (<cost_of_witness>, <cost_of_sciptsig>)
#[allow(clippy::type_complexity)]
fn sat_minus_dissat_witness(
    a: &(Option<(usize, usize)>, Option<(usize, usize)>),
    b: &(Option<(usize, usize)>, Option<(usize, usize)>),
) -> cmp::Ordering {
    a.0.map(|x| a.1.map(|y| x.0 as isize - y.0 as isize))
        .cmp(&b.0.map(|x| b.1.map(|y| x.0 as isize - y.0 as isize)))
}

/// Returns Some(max(x,y)) is both x and y are Some. Otherwise, returns `None`.
fn opt_max<T: Ord>(a: Option<T>, b: Option<T>) -> Option<T> {
    if let (Some(x), Some(y)) = (a, b) {
        Some(cmp::max(x, y))
    } else {
        None
    }
}

/// Returns Some(x+y) is both x and y are Some. Otherwise, returns `None`.
fn opt_add(a: Option<usize>, b: Option<usize>) -> Option<usize> { a.and_then(|x| b.map(|y| x + y)) }

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
