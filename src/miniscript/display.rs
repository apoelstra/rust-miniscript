// SPDX-License-Identifier: CC0-1.0

//! Miniscript Node Display

use core::{cmp, fmt};

use bitcoin::hashes::hash160;

use crate::iter::{Tree, TreeLike};
use crate::miniscript::types::Type;
use crate::miniscript::Terminal;
use crate::prelude::sync::Arc;
use crate::{Miniscript, MiniscriptKey, ScriptContext};

#[derive(Clone)]
enum DisplayNode<'a, Pk: MiniscriptKey, Ctx: ScriptContext> {
    Node(Type, &'a Terminal<Pk, Ctx>),
    ThresholdK(usize),
    Key(&'a Pk),
    RawKeyHash(&'a hash160::Hash),
    After(&'a crate::AbsLockTime),
    Older(&'a crate::RelLockTime),
    Sha256(&'a Pk::Sha256),
    Hash256(&'a Pk::Hash256),
    Ripemd160(&'a Pk::Ripemd160),
    Hash160(&'a Pk::Hash160),
}

#[derive(Clone)]
enum NaryChildren<'a, Pk: MiniscriptKey, Ctx: ScriptContext> {
    Nodes(usize, &'a [Arc<Miniscript<Pk, Ctx>>]),
    Keys(usize, &'a [Pk]),
}

impl<'a, Pk: MiniscriptKey, Ctx: ScriptContext> TreeLike for DisplayNode<'a, Pk, Ctx> {
    type NaryChildren = NaryChildren<'a, Pk, Ctx>;

    fn nary_len(tc: &Self::NaryChildren) -> usize {
        match tc {
            NaryChildren::Nodes(_, n) => 1 + n.len(),
            NaryChildren::Keys(_, k) => 1 + k.len(),
        }
    }

    fn nary_index(tc: Self::NaryChildren, idx: usize) -> Self {
        if idx == 0 {
            match tc {
                NaryChildren::Nodes(k, _) => DisplayNode::ThresholdK(k),
                NaryChildren::Keys(k, _) => DisplayNode::ThresholdK(k),
            }
        } else {
            match tc {
                NaryChildren::Nodes(_, n) => {
                    DisplayNode::Node(n[idx - 1].ty, n[idx - 1].as_inner())
                }
                NaryChildren::Keys(_, k) => DisplayNode::Key(&k[idx - 1]),
            }
        }
    }

    fn as_node(&self) -> Tree<Self, Self::NaryChildren> {
        match self {
            DisplayNode::Node(_, ref node) => match node {
                Terminal::True | Terminal::False => Tree::Nullary,
                Terminal::PkK(ref pk) | Terminal::PkH(ref pk) => Tree::Unary(DisplayNode::Key(pk)),
                Terminal::RawPkH(ref pkh) => Tree::Unary(DisplayNode::RawKeyHash(pkh)),
                Terminal::After(ref t) => Tree::Unary(DisplayNode::After(t)),
                Terminal::Older(ref t) => Tree::Unary(DisplayNode::Older(t)),
                Terminal::Sha256(ref h) => Tree::Unary(DisplayNode::Sha256(h)),
                Terminal::Hash256(ref h) => Tree::Unary(DisplayNode::Hash256(h)),
                Terminal::Ripemd160(ref h) => Tree::Unary(DisplayNode::Ripemd160(h)),
                Terminal::Hash160(ref h) => Tree::Unary(DisplayNode::Hash160(h)),
                // Check hash to be treated specially as always..
                Terminal::Check(ref sub) => match sub.as_inner() {
                    Terminal::PkK(ref pk) | Terminal::PkH(ref pk) => {
                        Tree::Unary(DisplayNode::Key(pk))
                    }
                    Terminal::RawPkH(ref pkh) => Tree::Unary(DisplayNode::RawKeyHash(pkh)),
                    _ => Tree::Unary(DisplayNode::Node(sub.ty, sub.as_inner())),
                },
                Terminal::Alt(ref sub)
                | Terminal::Swap(ref sub)
                | Terminal::DupIf(ref sub)
                | Terminal::Verify(ref sub)
                | Terminal::NonZero(ref sub)
                | Terminal::ZeroNotEqual(ref sub) => {
                    Tree::Unary(DisplayNode::Node(sub.ty, sub.as_inner()))
                }
                Terminal::AndV(ref left, ref right)
                    if matches!(right.as_inner(), Terminal::True) =>
                {
                    Tree::Unary(DisplayNode::Node(left.ty, left.as_inner()))
                }
                Terminal::OrI(ref left, ref right)
                    if matches!(left.as_inner(), Terminal::False) =>
                {
                    Tree::Unary(DisplayNode::Node(right.ty, right.as_inner()))
                }
                Terminal::OrI(ref left, ref right)
                    if matches!(right.as_inner(), Terminal::False) =>
                {
                    Tree::Unary(DisplayNode::Node(left.ty, left.as_inner()))
                }
                Terminal::AndV(ref left, ref right)
                | Terminal::AndB(ref left, ref right)
                | Terminal::OrB(ref left, ref right)
                | Terminal::OrD(ref left, ref right)
                | Terminal::OrC(ref left, ref right)
                | Terminal::OrI(ref left, ref right) => Tree::Binary(
                    DisplayNode::Node(left.ty, left.as_inner()),
                    DisplayNode::Node(right.ty, right.as_inner()),
                ),
                Terminal::AndOr(ref a, ref b, ref c) if matches!(c.as_inner(), Terminal::False) => {
                    Tree::Binary(
                        DisplayNode::Node(a.ty, a.as_inner()),
                        DisplayNode::Node(b.ty, b.as_inner()),
                    )
                }
                Terminal::AndOr(ref a, ref b, ref c) => Tree::Ternary(
                    DisplayNode::Node(a.ty, a.as_inner()),
                    DisplayNode::Node(b.ty, b.as_inner()),
                    DisplayNode::Node(c.ty, c.as_inner()),
                ),
                Terminal::Thresh(ref thresh) => {
                    Tree::Nary(NaryChildren::Nodes(thresh.k(), thresh.data()))
                }
                Terminal::Multi(ref thresh) => {
                    Tree::Nary(NaryChildren::Keys(thresh.k(), thresh.data()))
                }
                Terminal::SortedMulti(ref thresh) => {
                    Tree::Nary(NaryChildren::Keys(thresh.k(), thresh.data()))
                }
                Terminal::MultiA(ref thresh) => {
                    Tree::Nary(NaryChildren::Keys(thresh.k(), thresh.data()))
                }
                Terminal::SortedMultiA(thresh) => {
                    Tree::Nary(NaryChildren::Keys(thresh.k(), thresh.data()))
                }
            },
            // Only nodes have children; the rest are terminals.
            _ => Tree::Nullary,
        }
    }
}

#[derive(Copy, Clone)]
enum DisplayTypes {
    /// Display no types.
    None,
    /// Display all types, including the initial type.
    All(Type),
    /// Display all types, except that the initial type should be written as [TYPECHECK FAILED].
    AllBadFirst,
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Terminal<Pk, Ctx> {
    fn conditional_fmt(&self, f: &mut fmt::Formatter, display_types: DisplayTypes) -> fmt::Result {
        let initial_type = match display_types {
            DisplayTypes::None => Type::FALSE,
            DisplayTypes::All(ty) => ty,
            DisplayTypes::AllBadFirst => Type::FALSE,
        };

        for item in DisplayNode::Node(initial_type, self).verbose_pre_order_iter() {
            let show_type = match display_types {
                DisplayTypes::None => false,
                DisplayTypes::All(_) => true,
                DisplayTypes::AllBadFirst => item.index > 0,
            };

            match (display_types, item.node) {
                (_, DisplayNode::Node(ty, node)) => {
                    if node.is_wrapper() {
                        // Wrappers are very easy: just write the one-character name and maybe the
                        // type and we are done. No parens, no :s, no commas, etc.
                        if item.n_children_yielded == 0 {
                            if show_type {
                                f.write_str("[")?;
                                fmt::Display::fmt(&ty, f)?;
                                f.write_str("]")?;
                            }
                            f.write_str(node.fragment_name())?;
                        }
                    } else {
                        // Non-wrappers are a little more involved.
                        if item.n_children_yielded == 0 {
                            if let Some(DisplayNode::Node(_, parent)) = item.parent {
                                if parent.is_wrapper() {
                                    f.write_str(":")?;
                                }
                            }

                            if show_type {
                                f.write_str("[")?;
                                fmt::Display::fmt(&ty, f)?;
                                f.write_str("]")?;
                            }
                            f.write_str(node.fragment_name())?;

                            if !item.is_complete {
                                f.write_str("(")?;
                            }
                        } else if item.is_complete {
                            f.write_str(")")?;
                        } else {
                            f.write_str(",")?;
                        }
                    }
                }
                // Only nodes have a complicated algorithm. The other objects we just print.
                (DisplayTypes::None, DisplayNode::ThresholdK(ref k)) => fmt::Display::fmt(k, f)?,
                (DisplayTypes::None, DisplayNode::Key(ref pk)) => fmt::Display::fmt(pk, f)?,
                (DisplayTypes::None, DisplayNode::RawKeyHash(ref h)) => fmt::Display::fmt(h, f)?,
                (DisplayTypes::None, DisplayNode::After(ref t)) => fmt::Display::fmt(t, f)?,
                (DisplayTypes::None, DisplayNode::Older(ref t)) => fmt::Display::fmt(t, f)?,
                (DisplayTypes::None, DisplayNode::Sha256(ref h)) => fmt::Display::fmt(h, f)?,
                (DisplayTypes::None, DisplayNode::Hash256(ref h)) => fmt::Display::fmt(h, f)?,
                (DisplayTypes::None, DisplayNode::Ripemd160(ref h)) => fmt::Display::fmt(h, f)?,
                (DisplayTypes::None, DisplayNode::Hash160(ref h)) => fmt::Display::fmt(h, f)?,
                (_, DisplayNode::ThresholdK(ref k)) => fmt::Debug::fmt(k, f)?,
                (_, DisplayNode::Key(ref pk)) => fmt::Debug::fmt(pk, f)?,
                (_, DisplayNode::RawKeyHash(ref h)) => fmt::Debug::fmt(h, f)?,
                (_, DisplayNode::After(ref t)) => fmt::Debug::fmt(t, f)?,
                (_, DisplayNode::Older(ref t)) => fmt::Debug::fmt(t, f)?,
                (_, DisplayNode::Sha256(ref h)) => fmt::Debug::fmt(h, f)?,
                (_, DisplayNode::Hash256(ref h)) => fmt::Debug::fmt(h, f)?,
                (_, DisplayNode::Ripemd160(ref h)) => fmt::Debug::fmt(h, f)?,
                (_, DisplayNode::Hash160(ref h)) => fmt::Debug::fmt(h, f)?,
            }
        }
        Ok(())
    }

    /// A string representation of the fragment's name.
    ///
    /// This is **not** a recursive representation of the whole fragment;
    /// it does not contain or indicate any children.
    ///
    /// Not public since we intend to move it to the Inner type once that exists.
    fn fragment_name(&self) -> &'static str {
        match *self {
            Self::True => "1",
            Self::False => "0",
            Self::PkK(..) => "pk_k",
            Self::PkH(..) => "pk_h",
            // `RawPkH` is currently unsupported in the descriptor spec. We temporarily
            // display and parse these by prefixing them with 'expr'.
            Self::RawPkH(..) => "expr_raw_pk_h",
            Self::After(..) => "after",
            Self::Older(..) => "older",
            Self::Sha256(..) => "sha256",
            Self::Hash256(..) => "hash256",
            Self::Ripemd160(..) => "ripemd160",
            Self::Hash160(..) => "hash160",
            Self::Alt(..) => "a",
            Self::Swap(..) => "s",
            Self::Check(ref sub) if matches!(sub.as_inner(), Self::PkK(..)) => "pk",
            Self::Check(ref sub) if matches!(sub.as_inner(), Self::PkH(..)) => "pkh",
            Self::Check(ref sub) if matches!(sub.as_inner(), Self::RawPkH(..)) => "expr_raw_pkh",
            Self::Check(..) => "c",
            Self::DupIf(..) => "d",
            Self::Verify(..) => "v",
            Self::NonZero(..) => "j",
            Self::ZeroNotEqual(..) => "n",
            Self::AndV(_, ref r) if matches!(r.as_inner(), Self::True) => "t",
            Self::AndV(..) => "and_v",
            Self::AndOr(_, _, ref c) if matches!(c.as_inner(), Self::False) => "and_n",
            Self::AndB(..) => "and_b",
            Self::AndOr(..) => "andor",
            Self::OrB(..) => "or_b",
            Self::OrD(..) => "or_d",
            Self::OrC(..) => "or_c",
            Self::OrI(_, ref r) if matches!(r.as_inner(), Self::False) => "u",
            Self::OrI(ref l, _) if matches!(l.as_inner(), Self::False) => "l",
            Self::OrI(..) => "or_i",
            Self::Thresh(..) => "thresh",
            Self::Multi(..) => "multi",
            Self::SortedMulti(..) => "sortedmulti",
            Self::MultiA(..) => "multi_a",
            Self::SortedMultiA(..) => "sortedmulti_a",
        }
    }

    /// Whether the fragment in question is a "wrapper" such as `s:` or `a:`.
    ///
    /// Not public since we intend to move it to the Inner type once that exists.
    fn is_wrapper(&self) -> bool {
        !matches!(self, Self::True | Self::False) && self.fragment_name().len() == 1
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> fmt::Debug for Miniscript<Pk, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_inner()
            .conditional_fmt(f, DisplayTypes::All(self.ty))
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> fmt::Display for Miniscript<Pk, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_inner().conditional_fmt(f, DisplayTypes::None)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> fmt::Debug for Terminal<Pk, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let display_types = if let Ok(ty) = Type::type_check(self) {
            DisplayTypes::All(ty)
        } else {
            DisplayTypes::AllBadFirst
        };
        self.conditional_fmt(f, display_types)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> fmt::Display for Terminal<Pk, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.conditional_fmt(f, DisplayTypes::None)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> PartialOrd for Terminal<Pk, Ctx> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Ord for Terminal<Pk, Ctx> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        // First try matching directly on the fragment name to avoid the
        // complexity of building an iterator.
        match self.fragment_name().cmp(other.fragment_name()) {
            cmp::Ordering::Less => cmp::Ordering::Less,
            cmp::Ordering::Greater => cmp::Ordering::Greater,
            cmp::Ordering::Equal => {
                // But if they are equal then we need to iterate. Compare node
                // counts first since `zip` stops at the shorter iterator.
                let me_count = DisplayNode::Node(Type::FALSE, self)
                    .pre_order_iter()
                    .count();
                let you_count = DisplayNode::Node(Type::FALSE, other)
                    .pre_order_iter()
                    .count();
                match me_count.cmp(&you_count) {
                    cmp::Ordering::Equal => {}
                    ordering => return ordering,
                }
                for (me, you) in DisplayNode::Node(Type::FALSE, self)
                    .pre_order_iter()
                    .zip(DisplayNode::Node(Type::FALSE, other).pre_order_iter())
                {
                    let me_you_cmp = match (me, you) {
                        (DisplayNode::Node(_, me), DisplayNode::Node(_, you)) => {
                            me.fragment_name().cmp(you.fragment_name())
                        }
                        (DisplayNode::ThresholdK(me), DisplayNode::ThresholdK(you)) => me.cmp(&you),
                        (DisplayNode::Key(me), DisplayNode::Key(you)) => me.cmp(you),
                        (DisplayNode::RawKeyHash(me), DisplayNode::RawKeyHash(you)) => me.cmp(you),
                        (DisplayNode::After(me), DisplayNode::After(you)) => {
                            me.cmp_by_consensus(*you)
                        }
                        (DisplayNode::Older(me), DisplayNode::Older(you)) => {
                            me.cmp_by_consensus(*you)
                        }
                        (DisplayNode::Sha256(me), DisplayNode::Sha256(you)) => me.cmp(you),
                        (DisplayNode::Hash256(me), DisplayNode::Hash256(you)) => me.cmp(you),
                        (DisplayNode::Ripemd160(me), DisplayNode::Ripemd160(you)) => me.cmp(you),
                        (DisplayNode::Hash160(me), DisplayNode::Hash160(you)) => me.cmp(you),
                        _ => unreachable!(
                            "if the type of a node differs, its parent must have differed"
                        ),
                    };

                    match me_you_cmp {
                        cmp::Ordering::Less => return cmp::Ordering::Less,
                        cmp::Ordering::Greater => return cmp::Ordering::Greater,
                        cmp::Ordering::Equal => {}
                    }
                }

                cmp::Ordering::Equal
            }
        }
    }
}
