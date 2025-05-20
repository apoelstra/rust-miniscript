// SPDX-License-Identifier: CC0-1.0

//! Expression Trees
//!
//! This module represents expression trees, which are trees whose nodes have
//! names and arbitrary numbers of children. As strings, they are defined by
//! the following rules:
//!
//! * Any sequence of valid descriptor characters, including the empty string, is a "name".
//! * A name is an expression (called a "leaf").
//! * Given n expression trees `s_1`, ..., `s_n` and a name `X`, `X(s_1,...,s_n)` is an expression.
//! * Given n expression trees `s_1`, ..., `s_n` and a name `X`, `X{s_1,...,s_n}` is an expression.
//!
//! Note that while `leaf` and `leaf()` are both expressions, only the former is
//! actually a leaf. The latter has one child which is a leaf with an empty name.
//! If these are intended to be equivalent, the caller must add logic to do this
//! when converting the expression tree into its final type.
//!
//! All recursive structures in this library can be serialized and parsed as trees,
//! though of course each data structure further limits the grammar (e.g. to enforce
//! that names be valid Miniscript fragment names, public keys, hashes or timelocks).
//!
//! Users of this library probably do not need to use this module at all, unless they
//! are implementing their own Miniscript-like structures or extensions to Miniscript.
//! It is intended to be used as a utility to implement string parsing.
//!

mod error;

use core::ops;
use core::str::FromStr;

pub use self::error::{ParseNumError, ParseThresholdError, ParseTreeError};
use crate::blanket_traits::StaticDebugAndDisplay;
use crate::descriptor::checksum::verify_checksum;
use crate::prelude::*;
use crate::{AbsLockTime, Error, ParseError, RelLockTime, Threshold, MAX_RECURSION_DEPTH};

/// Allowed characters are descriptor strings.
pub const INPUT_CHARSET: &str = "0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#\"\\ ";

/// Internal data structure representing a node of an expression tree.
///
/// Users of the public API will always interact with this using the
/// wrapper type [`TreeIterItem`] which also contains a reference to
/// the whole tree.
#[derive(Debug, PartialEq, Eq)]
struct TreeNode<'s> {
    name: &'s str,
    name_pos: usize,
    parens: Parens,
    n_children: usize,
    index: usize,
    parent_idx: Option<usize>,
    last_child_idx: Option<usize>,
    right_sibling_idx: Option<usize>,
}

impl TreeNode<'_> {
    fn null(index: usize) -> Self {
        TreeNode {
            name: "",
            name_pos: 0,
            parens: Parens::None,
            n_children: 0,
            index,
            parent_idx: None,
            last_child_idx: None,
            right_sibling_idx: None,
        }
    }
}

/// An iterator over the nodes of a tree, in pre-order.
///
/// This has several differences from the pre-order iterator provided by [`crate::iter::TreeLike`]:
///
/// * this is double-ended, so a right-to-left post-order iterator can be obtained by `.rev()`.
/// * the yielded items represent sub-trees which themselves can be iterated from
/// * the iterator can be told to skip all descendants of the current node, using
///   [`PreOrderIter::skip_descendants`].
pub struct PreOrderIter<'s> {
    nodes: &'s [TreeNode<'s>],
    inner: core::ops::RangeInclusive<usize>,
}

impl PreOrderIter<'_> {
    /// Skip all the descendants of the most recently-yielded item.
    ///
    /// Here "most recently-yielded item" means the most recently-yielded item when
    /// running the iterator forward. If you run the iterator backward, e.g. by iterating
    /// on `iter.by_ref().rev()`, those items are not considered, and the resulting
    /// behavior of this function may be surprising.
    ///
    /// If this method is called before any nodes have been yielded, the entire iterator
    /// will be skipped.
    pub fn skip_descendants(&mut self) {
        if self.inner.is_empty() {
            return;
        }

        let last_index = self.inner.start().saturating_sub(1);
        // Construct a synthetic iterator over all descendants
        let last_item = TreeIterItem { nodes: self.nodes, index: last_index };
        let skip_past = last_item.rightmost_descendant_idx();
        // ...and copy the indices out of that.
        debug_assert!(skip_past + 1 >= *self.inner.start());
        debug_assert!(skip_past <= *self.inner.end());
        self.inner = skip_past + 1..=*self.inner.end();
    }
}

impl<'s> Iterator for PreOrderIter<'s> {
    type Item = TreeIterItem<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|n| TreeIterItem { nodes: self.nodes, index: n })
    }

    fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

impl DoubleEndedIterator for PreOrderIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_back()
            .map(|n| TreeIterItem { nodes: self.nodes, index: n })
    }
}

impl ExactSizeIterator for PreOrderIter<'_> {
    // The inner `RangeInclusive` does not impl ExactSizeIterator because the
    // range 0..=usize::MAX would have length usize::MAX + 1. But we know
    // that our range is limited by the `n_nodes` variable returned by
    // `parse_pre_check`, and if THAT didn't overflow then this won't either.
}

/// A tree node, as yielded from an iterator.
#[derive(Copy, Clone)]
pub struct TreeIterItem<'s> {
    nodes: &'s [TreeNode<'s>],
    index: usize,
}

/// An iterator over the direct children of a tree node.
pub struct DirectChildIterator<'s> {
    current: Option<TreeIterItem<'s>>,
}

impl<'s> Iterator for DirectChildIterator<'s> {
    type Item = TreeIterItem<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.current.take()?;
        self.current = item.nodes[item.index]
            .right_sibling_idx
            .map(|n| TreeIterItem { nodes: item.nodes, index: n });
        Some(item)
    }
}

/// The type of parentheses surrounding a node's children.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Parens {
    /// Node has no children.
    None,
    /// Round parentheses: `(` and `)`.
    Round,
    /// Curly braces: `{` and `}`.
    Curly,
}

/// A trait for extracting a structure from a Tree representation in token form
pub trait FromTree: Sized {
    /// Extract a structure from Tree representation
    fn from_tree(root: TreeIterItem) -> Result<Self, Error>;
}

impl<'s> TreeIterItem<'s> {
    /// The name of this tree node.
    pub fn name(self) -> &'s str { self.nodes[self.index].name }

    /// The 0-indexed byte-position of the name in the original expression tree.
    pub fn name_pos(self) -> usize { self.nodes[self.index].name_pos }

    /// The 0-indexed byte-position of the '(' or '{' character which starts the
    /// expression's children.
    ///
    /// If the expression has no children, returns one past the end of the name.
    pub fn children_pos(self) -> usize { self.name_pos() + self.name().len() + 1 }

    /// The number of children this node has.
    pub fn n_children(self) -> usize { self.nodes[self.index].n_children }

    /// The type of parenthesis surrounding this node's children.
    ///
    /// If the node has no children, this will be `Parens::None`.
    pub fn parens(self) -> Parens { self.nodes[self.index].parens }

    /// An iterator over the direct children of this node.
    ///
    /// If you want to iterate recursively, use the [`Self::pre_order_iter`]
    /// or [`Self::rtl_post_order_iter`] method.
    pub fn children(self) -> DirectChildIterator<'s> {
        DirectChildIterator { current: self.first_child() }
    }

    /// The index of the node in its underlying tree.
    pub fn index(&self) -> usize { self.index }

    /// Accessor for the parent of the node, if it has a parent (is not the root).
    pub fn parent(self) -> Option<Self> {
        self.nodes[self.index]
            .parent_idx
            .map(|n| Self { nodes: self.nodes, index: n })
    }

    /// Whether the node is the first child of its parent.
    ///
    /// Returns false for the root.
    pub fn is_first_child(self) -> bool {
        self.nodes[self.index]
            .parent_idx
            .map(|n| n + 1 == self.index)
            .unwrap_or(false)
    }

    /// Accessor for the first child of the node, if it has a first child.
    pub fn first_child(self) -> Option<Self> {
        // If the node has any children at all, its first child is the one right after it.
        self.nodes[self.index]
            .last_child_idx
            .map(|_| Self { nodes: self.nodes, index: self.index + 1 })
    }

    /// Accessor for the sibling of the node, if it has one.
    pub fn right_sibling(self) -> Option<Self> {
        self.nodes[self.index]
            .right_sibling_idx
            .map(|n| Self { nodes: self.nodes, index: n })
    }

    /// Helper function to find the rightmost descendant of a node.
    ///
    /// Used to construct iterators which cover only the node and its descendants.
    /// If the node has no descendants, returns its own index.
    fn rightmost_descendant_idx(self) -> usize {
        let mut scan = self.index;
        while let Some(idx) = self.nodes[scan].last_child_idx {
            scan = idx;
            while let Some(idx) = self.nodes[scan].right_sibling_idx {
                scan = idx;
            }
        }
        scan
    }

    /// Split the name by a separating character.
    ///
    /// If the separator is present, returns the prefix before the separator and
    /// the suffix after the separator. Otherwise returns the whole name.
    ///
    /// If the separator occurs multiple times, returns an error.
    pub fn name_separated(
        self,
        separator: char,
    ) -> Result<(Option<&'s str>, &'s str), ParseTreeError> {
        let mut name_split = self.name().splitn(3, separator);
        match (name_split.next(), name_split.next(), name_split.next()) {
            (None, _, _) => unreachable!("'split' always yields at least one element"),
            (Some(_), None, _) => Ok((None, self.name())),
            (Some(prefix), Some(name), None) => Ok((Some(prefix), name)),
            (Some(_), Some(_), Some(suffix)) => Err(ParseTreeError::MultipleSeparators {
                separator,
                pos: self.children_pos() - suffix.len() - 1,
            }),
        }
    }

    /// Check that a tree node has the given number of children.
    ///
    /// The `description` argument is only used to populate the error return,
    /// and is not validated in any way.
    pub fn verify_n_children(
        self,
        description: &'static str,
        n_children: impl ops::RangeBounds<usize>,
    ) -> Result<(), ParseTreeError> {
        if n_children.contains(&self.n_children()) {
            Ok(())
        } else {
            let minimum = match n_children.start_bound() {
                ops::Bound::Included(n) => Some(*n),
                ops::Bound::Excluded(n) => Some(*n + 1),
                ops::Bound::Unbounded => None,
            };
            let maximum = match n_children.end_bound() {
                ops::Bound::Included(n) => Some(*n),
                ops::Bound::Excluded(n) => Some(*n - 1),
                ops::Bound::Unbounded => None,
            };
            Err(ParseTreeError::IncorrectNumberOfChildren {
                description,
                n_children: self.n_children(),
                minimum,
                maximum,
            })
        }
    }

    /// Check that a tree node has the given name, one child, and round braces.
    ///
    /// Returns the first child.
    ///
    /// # Panics
    ///
    /// Panics if zero is in bounds for `n_children` (since then there may be
    /// no sensible value to return).
    pub fn verify_toplevel(
        &self,
        name: &'static str,
        n_children: impl ops::RangeBounds<usize>,
    ) -> Result<Self, ParseTreeError> {
        assert!(
            !n_children.contains(&0),
            "verify_toplevel is intended for nodes with >= 1 child"
        );

        if self.name() != name {
            Err(ParseTreeError::IncorrectName { actual: self.name().to_owned(), expected: name })
        } else if self.parens() == Parens::Curly {
            Err(ParseTreeError::IllegalCurlyBrace { pos: self.children_pos() })
        } else {
            self.verify_n_children(name, n_children)?;
            Ok(self.first_child().unwrap())
        }
    }

    /// Check that a tree node has a single terminal child which is an absolute locktime.
    ///
    /// Returns an error assuming that the node is named "after".
    ///
    /// If so, parse the locktime from a string and return it.
    pub fn verify_after(&self) -> Result<AbsLockTime, ParseError> {
        self.verify_n_children("after", 1..=1)
            .map_err(ParseError::Tree)?;
        let child = self.first_child().unwrap();
        child
            .verify_n_children("absolute locktime", 0..=0)
            .map_err(ParseError::Tree)?;
        parse_num(child.name())
            .map_err(ParseError::Num)
            .and_then(|n| AbsLockTime::from_consensus(n).map_err(ParseError::AbsoluteLockTime))
    }

    /// Check that a tree node has a single terminal child which is a relative locktime.
    ///
    /// Returns an error assuming that the node is named "older".
    ///
    /// If so, parse the locktime from a string and return it.
    pub fn verify_older(&self) -> Result<RelLockTime, ParseError> {
        self.verify_n_children("older", 1..=1)
            .map_err(ParseError::Tree)?;
        let child = self.first_child().unwrap();
        child
            .verify_n_children("relative locktime", 0..=0)
            .map_err(ParseError::Tree)?;
        parse_num(child.name())
            .map_err(ParseError::Num)
            .and_then(|n| RelLockTime::from_consensus(n).map_err(ParseError::RelativeLockTime))
    }

    /// Check that a tree node is a terminal (has no children).
    ///
    /// If so, parse the terminal from a string and return it.
    ///
    /// The `description` and `inner_description` arguments are only used to
    /// populate the error return, and is not validated in any way.
    pub fn verify_terminal<T>(&self, description: &'static str) -> Result<T, ParseError>
    where
        T: FromStr,
        T::Err: StaticDebugAndDisplay,
    {
        self.verify_n_children(description, 0..=0)
            .map_err(ParseError::Tree)?;
        T::from_str(self.name()).map_err(ParseError::box_from_str)
    }

    /// Check that a tree node has exactly one child, which is a terminal.
    ///
    /// If so, parse the terminal child from a string and return it.
    ///
    /// The `description` and `inner_description` arguments are only used to
    /// populate the error return, and is not validated in any way.
    pub fn verify_terminal_parent<T>(
        &self,
        description: &'static str,
        inner_description: &'static str,
    ) -> Result<T, ParseError>
    where
        T: FromStr,
        T::Err: StaticDebugAndDisplay,
    {
        self.verify_n_children(description, 1..=1)
            .map_err(ParseError::Tree)?;
        self.first_child()
            .unwrap()
            .verify_terminal(inner_description)
    }

    /// Check that a tree node has exactly two children.
    ///
    /// If so, return them.
    ///
    /// The `description` argument is only used to populate the error return,
    /// and is not validated in any way.
    pub fn verify_binary(&self, description: &'static str) -> Result<(Self, Self), ParseTreeError> {
        self.verify_n_children(description, 2..=2)?;
        let first_child = self.first_child().unwrap();
        let second_child = first_child.right_sibling().unwrap();
        Ok((first_child, second_child))
    }

    /// Parses an expression tree as a threshold (a term with at least one child,
    /// the first of which is a positive integer k).
    ///
    /// This sanity-checks that the threshold is well-formed (begins with a valid
    /// threshold value, etc.) but does not parse the children of the threshold.
    /// Instead it returns a threshold holding the empty type `()`, which is
    /// constructed without any allocations, and expects the caller to convert
    /// this to the "real" threshold type by calling [`Threshold::translate`].
    ///
    /// (An alternate API which does the conversion inline turned out to be
    /// too messy; it needs to take a closure, have multiple generic parameters,
    /// and be able to return multiple error types.)
    pub fn verify_threshold<
        const MAX: usize,
        F: FnMut(Self) -> Result<T, E>,
        T,
        E: From<ParseThresholdError>,
    >(
        &'s self,
        mut map_child: F,
    ) -> Result<Threshold<T, MAX>, E> {
        let mut child_iter = self.children();
        let kchild = match child_iter.next() {
            Some(k) => k,
            None => return Err(ParseThresholdError::NoChildren.into()),
        };
        // First, special case "no arguments" so we can index the first argument without panics.
        if kchild.n_children() > 0 {
            return Err(ParseThresholdError::KNotTerminal.into());
        }

        let k = parse_num(kchild.name()).map_err(ParseThresholdError::ParseK)? as usize;
        Threshold::new(k, vec![(); self.n_children() - 1])
            .map_err(ParseThresholdError::Threshold)
            .map_err(From::from)
            .and_then(|thresh| thresh.translate_by_index(|_| map_child(child_iter.next().unwrap())))
    }

    /// Returns an iterator over the nodes of the tree, in pre-order.
    ///
    /// Constructing the iterator takes O(depth) time.
    pub fn pre_order_iter(&'s self) -> PreOrderIter<'s> {
        PreOrderIter { nodes: self.nodes, inner: self.index..=self.rightmost_descendant_idx() }
    }

    /// Returns an iterator over the nodes of the tree, in right-to-left post-order.
    pub fn rtl_post_order_iter(&'s self) -> core::iter::Rev<PreOrderIter<'s>> {
        self.pre_order_iter().rev()
    }

    /// Check that a tree has no curly-brace children in it.
    pub fn verify_no_curly_braces(&self) -> Result<(), ParseTreeError> {
        for node in self.rtl_post_order_iter() {
            if node.parens() == Parens::Curly {
                return Err(ParseTreeError::IllegalCurlyBrace { pos: node.children_pos() });
            }
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
/// A parsed expression tree. See module-level documentation for syntax.
pub struct Tree<'s> {
    /// The nodes, stored in pre-order.
    nodes: Vec<TreeNode<'s>>,
}

impl<'a> Tree<'a> {
    /// Returns the root node of the tree, or `None` if the tree is empty.
    pub fn root(&'a self) -> TreeIterItem<'a> {
        assert_ne!(
            self.nodes.len(),
            0,
            "trees cannot be empty; the empty string parses as a single root with empty name"
        );
        TreeIterItem { nodes: &self.nodes, index: 0 }
    }

    /// Check that a string is a well-formed expression string, with optional
    /// checksum.
    ///
    /// Returns the string with the checksum removed, the maximum depth, and the
    /// number of nodes in the tree.
    fn parse_pre_check(s: &str) -> Result<(&str, usize, usize), ParseTreeError> {
        // First, scan through string to make sure it is well-formed.
        // Do ASCII/checksum check first; after this we can use .bytes().enumerate() rather
        // than .char_indices(), which is *significantly* faster.
        let s = verify_checksum(s)?;

        let mut n_nodes = 1;
        let mut max_depth = 0;
        let mut open_paren_stack = Vec::with_capacity(128);
        for (pos, ch) in s.bytes().enumerate() {
            if ch == b'(' || ch == b'{' {
                open_paren_stack.push((ch, pos));
                if max_depth < open_paren_stack.len() {
                    max_depth = open_paren_stack.len();
                }
            } else if ch == b')' || ch == b'}' {
                if let Some((open_ch, open_pos)) = open_paren_stack.pop() {
                    if (open_ch == b'(' && ch == b'}') || (open_ch == b'{' && ch == b')') {
                        return Err(ParseTreeError::MismatchedParens {
                            open_ch: open_ch.into(),
                            open_pos,
                            close_ch: ch.into(),
                            close_pos: pos,
                        });
                    }

                    if let Some(&(paren_ch, paren_pos)) = open_paren_stack.last() {
                        // not last paren; this should not be the end of the string,
                        // and the next character should be a , ) or }.
                        if pos == s.len() - 1 {
                            return Err(ParseTreeError::UnmatchedOpenParen {
                                ch: paren_ch.into(),
                                pos: paren_pos,
                            });
                        } else {
                            let next_byte = s.as_bytes()[pos + 1];
                            if next_byte != b')' && next_byte != b'}' && next_byte != b',' {
                                return Err(ParseTreeError::ExpectedParenOrComma {
                                    ch: next_byte.into(),
                                    pos: pos + 1,
                                });
                                //
                            }
                        }
                    } else {
                        // last paren; this SHOULD be the end of the string
                        if pos < s.len() - 1 {
                            return Err(ParseTreeError::TrailingCharacter {
                                ch: s.as_bytes()[pos + 1].into(),
                                pos: pos + 1,
                            });
                        }
                    }
                } else {
                    // In practice, this is only hit if there are no open parens at all.
                    // If there are open parens, like in "())", then on the first ), we
                    // would have returned TrailingCharacter in the previous clause.
                    //
                    // From a user point of view, UnmatchedCloseParen would probably be
                    // a clearer error to get, but it complicates the parser to do this,
                    // and "TralingCharacter" is technically correct, so we leave it for
                    // now.
                    return Err(ParseTreeError::UnmatchedCloseParen { ch: ch.into(), pos });
                }

                n_nodes += 1;
            } else if ch == b',' {
                if open_paren_stack.is_empty() {
                    // We consider commas outside of the tree to be "trailing characters"
                    return Err(ParseTreeError::TrailingCharacter { ch: ch.into(), pos });
                }

                n_nodes += 1;
            }
        }
        // Catch "early end of string"
        if let Some((ch, pos)) = open_paren_stack.pop() {
            return Err(ParseTreeError::UnmatchedOpenParen { ch: ch.into(), pos });
        }

        // FIXME should be able to remove this once we eliminate all recursion
        // in the library.
        if u32::try_from(max_depth).unwrap_or(u32::MAX) > MAX_RECURSION_DEPTH {
            return Err(ParseTreeError::MaxRecursionDepthExceeded {
                actual: max_depth,
                maximum: MAX_RECURSION_DEPTH,
            });
        }

        Ok((s, max_depth, n_nodes))
    }

    /// Parses a tree from a string
    #[allow(clippy::should_implement_trait)] // Cannot use std::str::FromStr because of lifetimes.
    pub fn from_str(s: &'a str) -> Result<Self, ParseError> {
        Self::from_str_inner(s).map_err(ParseError::Tree)
    }

    fn from_str_inner(s: &'a str) -> Result<Self, ParseTreeError> {
        fn new_node<'a>(nodes: &mut [TreeNode<'a>], stack: &[usize], pos: usize) -> TreeNode<'a> {
            let parent_idx = stack.last().copied();
            if let Some(idx) = parent_idx {
                nodes[idx].n_children += 1;
                nodes[idx].last_child_idx = Some(nodes.len());
            }

            let mut new = TreeNode::null(nodes.len());
            new.name_pos = pos;
            new.parent_idx = parent_idx;
            new
        }

        // First, scan through string to make sure it is well-formed.
        let (s, max_depth, n_nodes) = Self::parse_pre_check(s)?;

        let mut nodes = Vec::with_capacity(n_nodes);

        // Now, knowing it is sane and well-formed, we can easily parse it forward,
        // as the string serialization lists all the nodes in pre-order.
        let mut parent_stack = Vec::with_capacity(max_depth);
        let mut current_node = Some(TreeNode::null(0));
        for (pos, ch) in s.bytes().enumerate() {
            if ch == b'(' || ch == b'{' {
                let mut current = current_node.expect("'(' only occurs after a node name");
                current.name = &s[current.name_pos..pos];
                current.parens = match ch {
                    b'(' => Parens::Round,
                    b'{' => Parens::Curly,
                    _ => unreachable!(),
                };
                parent_stack.push(nodes.len());
                nodes.push(current);

                current_node = Some(new_node(&mut nodes, &parent_stack, pos + 1));
            } else if ch == b',' {
                if let Some(mut current) = current_node {
                    current.name = &s[current.name_pos..pos];
                    nodes.push(current);
                }

                if let Some(last_sib_idx) =
                    parent_stack.last().and_then(|n| nodes[*n].last_child_idx)
                {
                    nodes[last_sib_idx].right_sibling_idx = Some(nodes.len());
                }
                current_node = Some(new_node(&mut nodes, &parent_stack, pos + 1));
            } else if ch == b')' || ch == b'}' {
                if let Some(mut current) = current_node {
                    current.name = &s[current.name_pos..pos];
                    nodes.push(current);
                }

                current_node = None;
                parent_stack.pop();
            }
        }
        if let Some(mut current) = current_node {
            current.name = &s[current.name_pos..];
            nodes.push(current);
        }

        assert_eq!(parent_stack.capacity(), max_depth);
        assert_eq!(nodes.capacity(), n_nodes);
        assert_eq!(nodes.len(), nodes.capacity());

        Ok(Tree { nodes })
    }
}

/// Parse a string as a u32, forbidding zero.
pub fn parse_num_nonzero(s: &str, context: &'static str) -> Result<u32, ParseNumError> {
    if s == "0" {
        return Err(ParseNumError::IllegalZero { context });
    }
    if let Some(ch) = s.chars().next() {
        if !('1'..='9').contains(&ch) {
            return Err(ParseNumError::InvalidLeadingDigit(ch));
        }
    }
    u32::from_str(s).map_err(ParseNumError::StdParse)
}

/// Parse a string as a u32, for timelocks or thresholds
pub fn parse_num(s: &str) -> Result<u32, ParseNumError> {
    if s == "0" {
        // Special-case 0 since it is the only number which may start with a leading zero.
        return Ok(0);
    }
    parse_num_nonzero(s, "")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ParseError;

    struct NodeBuilder<'a> {
        inner: Vec<TreeNode<'a>>,
        sibling_stack: Vec<Option<usize>>,
        parent_stack: Vec<usize>,
        str_idx: usize,
    }

    impl<'a> NodeBuilder<'a> {
        fn new() -> Self {
            NodeBuilder {
                inner: vec![],
                sibling_stack: vec![None],
                parent_stack: vec![],
                str_idx: 0,
            }
        }

        fn new_node_internal(&mut self, name: &'a str) -> TreeNode<'a> {
            let mut new = TreeNode::null(self.inner.len());
            if let Some(idx) = self.parent_stack.last().copied() {
                self.inner[idx].n_children += 1;
                self.inner[idx].last_child_idx = Some(self.inner.len());
                new.parent_idx = Some(idx);
            }
            if let Some(idx) = self.sibling_stack.last().unwrap() {
                self.inner[*idx].right_sibling_idx = Some(self.inner.len());
                self.str_idx += 1;
            }
            new.name = name;
            new.name_pos = self.str_idx;

            *self.sibling_stack.last_mut().unwrap() = Some(self.inner.len());
            self.str_idx += name.len();
            new
        }

        fn leaf(mut self, name: &'a str) -> Self {
            let new = self.new_node_internal(name);

            self.inner.push(new);
            self
        }

        fn open(mut self, name: &'a str, paren: char) -> Self {
            let mut new = self.new_node_internal(name);

            new.parens = match paren {
                '(' => Parens::Round,
                '{' => Parens::Curly,
                _ => panic!(),
            };
            self.str_idx += 1;

            self.parent_stack.push(self.inner.len());
            self.sibling_stack.push(None);
            self.inner.push(new);
            self
        }

        fn close(mut self) -> Self {
            self.str_idx += 1;
            self.parent_stack.pop();
            self.sibling_stack.pop();
            self
        }

        fn into_tree(self) -> Tree<'a> {
            assert_eq!(self.parent_stack.len(), 0);
            Tree { nodes: self.inner }
        }
    }

    #[test]
    fn test_parse_num() {
        assert!(parse_num("0").is_ok());
        assert!(parse_num_nonzero("0", "").is_err());
        assert!(parse_num("00").is_err());
        assert!(parse_num("0000").is_err());
        assert!(parse_num("06").is_err());
        assert!(parse_num("+6").is_err());
        assert!(parse_num("-6").is_err());
    }

    #[test]
    fn parse_tree_basic() {
        assert_eq!(
            Tree::from_str("thresh").unwrap(),
            NodeBuilder::new().leaf("thresh").into_tree()
        );

        assert!(matches!(
            Tree::from_str("thresh,").unwrap_err(),
            ParseError::Tree(ParseTreeError::TrailingCharacter { ch: ',', pos: 6 }),
        ));

        assert!(matches!(
            Tree::from_str("thresh,thresh").unwrap_err(),
            ParseError::Tree(ParseTreeError::TrailingCharacter { ch: ',', pos: 6 }),
        ));

        assert!(matches!(
            Tree::from_str("thresh()thresh()").unwrap_err(),
            ParseError::Tree(ParseTreeError::TrailingCharacter { ch: 't', pos: 8 }),
        ));

        assert_eq!(
            Tree::from_str("thresh()").unwrap(),
            NodeBuilder::new()
                .open("thresh", '(')
                .leaf("")
                .close()
                .into_tree()
        );

        assert!(matches!(
            Tree::from_str("thresh(a()b)"),
            Err(ParseError::Tree(ParseTreeError::ExpectedParenOrComma { ch: 'b', pos: 10 })),
        ));

        assert!(matches!(
            Tree::from_str("thresh()xyz"),
            Err(ParseError::Tree(ParseTreeError::TrailingCharacter { ch: 'x', pos: 8 })),
        ));
    }

    #[test]
    fn parse_tree_parens() {
        assert!(matches!(
            Tree::from_str("a(").unwrap_err(),
            ParseError::Tree(ParseTreeError::UnmatchedOpenParen { ch: '(', pos: 1 }),
        ));

        assert!(matches!(
            Tree::from_str(")").unwrap_err(),
            ParseError::Tree(ParseTreeError::UnmatchedCloseParen { ch: ')', pos: 0 }),
        ));

        assert!(matches!(
            Tree::from_str("x(y))").unwrap_err(),
            ParseError::Tree(ParseTreeError::TrailingCharacter { ch: ')', pos: 4 }),
        ));

        assert!(matches!(
            Tree::from_str("a{").unwrap_err(),
            ParseError::Tree(ParseTreeError::UnmatchedOpenParen { ch: '{', pos: 1 }),
        ));

        assert!(matches!(
            Tree::from_str("}").unwrap_err(),
            ParseError::Tree(ParseTreeError::UnmatchedCloseParen { ch: '}', pos: 0 }),
        ));

        assert!(matches!(
            Tree::from_str("x(y)}").unwrap_err(),
            ParseError::Tree(ParseTreeError::TrailingCharacter { ch: '}', pos: 4 }),
        ));

        assert!(matches!(
            Tree::from_str("x{y)").unwrap_err(),
            ParseError::Tree(ParseTreeError::MismatchedParens {
                open_ch: '{',
                open_pos: 1,
                close_ch: ')',
                close_pos: 3,
            }),
        ));
    }

    #[test]
    fn parse_tree_taproot() {
        assert_eq!(
            Tree::from_str("a{b(c),d}").unwrap(),
            NodeBuilder::new()
                .open("a", '{')
                .open("b", '(')
                .leaf("c")
                .close()
                .leaf("d")
                .close()
                .into_tree()
        );
    }

    #[test]
    fn parse_tree_desc() {
        let keys = [
            "02c2fd50ceae468857bb7eb32ae9cd4083e6c7e42fbbec179d81134b3e3830586c",
            "0257f4a2816338436cccabc43aa724cf6e69e43e84c3c8a305212761389dd73a8a",
        ];
        let desc = format!("wsh(t:or_c(pk({}),v:pkh({})))", keys[0], keys[1]);

        assert_eq!(
            Tree::from_str(&desc).unwrap(),
            NodeBuilder::new()
                .open("wsh", '(')
                .open("t:or_c", '(')
                .open("pk", '(')
                .leaf(keys[0])
                .close()
                .open("v:pkh", '(')
                .leaf(keys[1])
                .close()
                .close()
                .close()
                .into_tree()
        );
    }
}
