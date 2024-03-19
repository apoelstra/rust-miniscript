// SPDX-License-Identifier: CC0-1.0

//! Expression Trees
//!
//! Parsed representation of expression trees of the form `a(b(c,d),e(f,g))`.
//! Expression trees retain each node name as a string slice and do not
//! interpret anything beyond parsing out the tree structure.

use core::ops;
use core::str::FromStr;

use super::{check_valid_chars2, LeafError, ParseNumError, ParseTreeError, MAX_RECURSION_DEPTH};
use crate::{ParseThresholdError, ResultExt as _, SpanOnly, Threshold, WithSpan};

/// A node in an expression tree.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Node<T> {
    data: T,
    /// The location of the node within the original expression string. Useful
    /// for error reporting
    span: ops::Range<usize>,
    /// The number of children this node has.
    n_children: usize,
    /// If this node has children, index of its first (leftmost) child.
    idx_child: Option<usize>,
    /// If this node has a parent (i.e. is not the root), index of the parent.
    idx_parent: Option<usize>,
    /// If this node has additional siblings, index of the sibling to its right.
    idx_sibling: Option<usize>,
}

impl<T> Node<T> {
    /// Drops the data from the node, retaining only its span information.
    pub fn span_only(&self) -> Node<SpanOnly> { self.map_ref(|_| SpanOnly) }

    /// Converts a node of one type to a node of another type.
    pub fn map_ref<U, F: FnOnce(&T) -> U>(&self, mapfn: F) -> Node<U> {
        Node {
            data: mapfn(&self.data),
            span: self.span(),
            n_children: self.n_children,
            idx_child: self.idx_child,
            idx_parent: self.idx_parent,
            idx_sibling: self.idx_sibling,
        }
    }

    /// Accessor for the data contained in this node.
    pub const fn data(&self) -> &T { &self.data }

    /// Accessor for the index of the first character of this node within the original string.
    pub const fn span(&self) -> ops::Range<usize> {
        // ops::Range does not impl Copy, for stupid historical reasons,
        // and I cannot call .clone in a constfn, so I need to manually
        // copy it here.
        ops::Range { start: self.span.start, end: self.span.end }
    }

    /// Accessor for the number of children this node has.
    pub const fn n_children(&self) -> usize { self.n_children }
}

impl<'expr> Node<&'expr str> {
    /// Attempt to parse this node as a number.
    pub fn parse_num(&self) -> Result<u32, WithSpan<LeafError<ParseNumError>>> {
        if self.n_children > 0 {
            return Err(LeafError::not_leaf(self.n_children)).with_span(self.span());
        }

        if let Some(ch) = self.data.chars().next() {
            if !('1'..='9').contains(&ch) {
                return Err(LeafError::invalid_start_character(ch)).with_span(self.span());
            }
        }
        self.data
            .parse::<u32>()
            .map_err(LeafError::parse_u32)
            .with_span(self.span())
    }

    /// Attempt to parse this node as an object which can be parsed via [`FromStr`].
    pub fn parse_from_str<T: FromStr>(&self) -> Result<T, WithSpan<LeafError<T::Err>>> {
        T::from_str(self.data)
            .map_err(LeafError::Parse)
            .with_span(self.span())
    }

    /// Drop the lifetime on the node's data by promoting it to an owned type.
    pub fn to_owned(&self) -> Node<String> { self.map_ref(|s| (*s).to_owned()) }

    /// Parses a node and its first child as a threshold (a term with at leas=
    /// one child, the first of which is a positive integer k).
    ///
    /// This sanity-checks that the threshold is well-formed (begins with a valid
    /// threshold value, etc.) but does not parse the children of the threshold.
    /// Instead it returns a threshold holding the empty type `()`, which is
    /// constructed without any allocations, and expects the caller to convert
    /// this to the "real" threshold type by calling [`Threshold::translate`]
    /// or similar.
    ///
    /// (An alternate API which does the conversion inline turned out to be
    /// too messy; it needs to take a closure, have multiple generic parameters,
    /// and be able to return multiple error types.)
    pub fn to_null_threshold<const MAX: usize>(
        &self,
        first_child: Option<&Node<&str>>,
    ) -> Result<Threshold<(), MAX>, WithSpan<ParseThresholdError>> {
        // First, special case "no arguments" so we can index the first argument without panics.
        let k_unparsed = match first_child {
            None => return Err(ParseThresholdError::NoChildren).with_span(self.span()),
            Some(k) => k,
        };
        // If we had a first child, the total number of children should be >0.
        assert_ne!(self.n_children, 0);

        let k = k_unparsed
            .parse_num()
            .map_err(|e| e.map(|e| ParseThresholdError::ParseK(e.to_string())))?
            as usize;

        Threshold::new(k, vec![(); self.n_children - 1])
            .map_err(ParseThresholdError::Threshold)
            .with_span(self.span())
    }
}

impl Node<SpanOnly> {
    /// Given a span-only node, restore the actual string spans by providing the original string.
    ///
    /// # Panics
    ///
    /// Will panic if the span associated with the node is out-of-bounds for the provided string.
    pub fn attach_str<'s>(&'s self, s: &'s str) -> Node<&'s str> {
        self.map_ref(|_| &s[self.span()])
    }
}

#[derive(Debug)]
/// A token of the form `x(...)` or `x`
pub struct Tree<'expr> {
    /// An array of nodes of the tree. The first entry is the root.
    nodes: Vec<Node<&'expr str>>,
}

impl<'expr> Default for Tree<'expr> {
    fn default() -> Self { Self::new() }
}

impl<'expr> Tree<'expr> {
    /// Constructs a new empty tree
    pub const fn new() -> Self { Tree { nodes: Vec::new() } }

    /// Constructs a new empty tree which preallocates capacity for `n` nodes
    pub fn with_capacity(n: usize) -> Self { Tree { nodes: Vec::with_capacity(n) } }

    /// The number of nodes in the tree.
    pub fn len(&self) -> usize { self.nodes.len() }

    /// Whether the tree is empty (has no nodes).
    pub fn is_empty(&self) -> bool { self.nodes.is_empty() }

    /// Pushes a new root node. Returns the index of the newly added node,
    /// which will always be 0.
    ///
    /// # Panics
    ///
    /// Panics if the tree is nonempty.
    fn push_root(&mut self, string_start: usize, data: &'expr str) -> usize {
        assert_eq!(self.nodes.len(), 0);
        self.nodes.push(Node {
            data,
            span: string_start..string_start + data.len(),
            n_children: 0,
            idx_child: None,
            idx_parent: None,
            idx_sibling: None,
        });
        self.nodes.len() - 1
    }

    /// Pushes a new child of the most recently-added node.
    ///
    /// This should also be used to push the initial (root) node. Returns the index
    /// of the newly-added node.
    ///
    /// # Panics
    ///
    /// Panics if the given node already has a child.
    fn push_first_child_of(&mut self, idx: usize, string_start: usize, data: &'expr str) -> usize {
        debug_assert_eq!(self.nodes[idx].n_children, 0);
        debug_assert_eq!(self.nodes[idx].idx_child, None);
        self.nodes[idx].n_children = 1;
        self.nodes[idx].idx_child = Some(self.nodes.len());
        self.nodes.push(Node {
            data,
            span: string_start..string_start + data.len(),
            n_children: 0,
            idx_child: None,
            idx_parent: Some(idx),
            idx_sibling: None,
        });
        self.nodes.len() - 1
    }

    /// Pushes a new right sibling of a node at the specified index. Returns the index
    /// of the newly-added node.
    ///
    /// # Panics
    ///
    /// Panics if the provided index is out of bounds, or if the node at
    /// the specified index already has a right sibling.
    fn push_right_sibling_of(
        &mut self,
        idx: usize,
        string_start: usize,
        data: &'expr str,
    ) -> usize {
        debug_assert_eq!(self.nodes[idx].idx_sibling, None);
        self.nodes[idx].idx_sibling = Some(self.nodes.len());
        if let Some(parent_idx) = self.nodes[idx].idx_parent {
            self.nodes[parent_idx].n_children += 1;
        }
        self.nodes.push(Node {
            data,
            span: string_start..string_start + data.len(),
            n_children: 0,
            idx_child: None,
            idx_parent: self.nodes[idx].idx_parent,
            idx_sibling: None,
        });
        self.nodes.len() - 1
    }

    /// Parse an expression tree with round brackets
    fn from_slice(sl: &'expr str, n_nodes: usize) -> Result<Tree<'expr>, WithSpan<ParseTreeError>> {
        #[derive(Debug)]
        enum NextNodeLoc {
            Root,
            ChildOf(usize),
            SiblingOf(usize),
        }

        let mut ret = Self::with_capacity(n_nodes);

        let mut depth = 0;
        let mut next_loc = NextNodeLoc::Root;
        let mut name_start_idx = 0;
        let mut ch_idx = 0;

        let bytes = sl.as_bytes();
        while ch_idx < sl.len() {
            let ch = bytes[ch_idx];
            if ch == b'(' || ch == b',' || ch == b')' {
                let mut next_idx = match next_loc {
                    NextNodeLoc::Root => ret.push_root(ch_idx, &sl[name_start_idx..ch_idx]),
                    NextNodeLoc::ChildOf(n) => {
                        ret.push_first_child_of(n, ch_idx, &sl[name_start_idx..ch_idx])
                    }
                    NextNodeLoc::SiblingOf(n) => {
                        ret.push_right_sibling_of(n, ch_idx, &sl[name_start_idx..ch_idx])
                    }
                };

                match ch {
                    b'(' => {
                        next_loc = NextNodeLoc::ChildOf(next_idx);
                        depth += 1;
                    }
                    b',' => {
                        next_loc = NextNodeLoc::SiblingOf(next_idx);
                    }
                    b')' => {
                        while ch_idx < bytes.len() && bytes[ch_idx] == b')' {
                            match ret.nodes[next_idx].idx_parent {
                                Some(idx) => next_idx = idx,
                                None => {
                                    return Err(ParseTreeError::overterminated_tree())
                                        .with_index(ch_idx)
                                }
                            }
                            ch_idx += 1;
                            depth -= 1;
                        }
                        next_loc = NextNodeLoc::SiblingOf(next_idx);
                    }
                    _ => unreachable!(),
                }
                name_start_idx = ch_idx + 1;

                if depth >= MAX_RECURSION_DEPTH {
                    let open_paren_loc = ret.nodes[next_idx].span().end + 1;
                    return Err(ParseTreeError::max_recursive_depth_exceeded(MAX_RECURSION_DEPTH))
                        .with_index(open_paren_loc);
                }
            }
            ch_idx += 1;
        }
        if depth != 0 {
            return Err(ParseTreeError::unterminated_tree()).with_index(ch_idx - 1);
        }

        Ok(ret)
    }

    /// Parses a tree from a string
    #[allow(clippy::should_implement_trait)] // https://github.com/rust-lang/rust-clippy/issues/9762
    pub fn from_str(s: &'expr str) -> Result<Tree<'expr>, WithSpan<ParseTreeError>> {
        let n = check_valid_chars2(s).map_err(|e| e.map(ParseTreeError::InvalidCharacter))?;
        Tree::from_slice(s, n)
    }

    /// Accessor for the root of the tree, if it is nonempty.
    pub fn root(&self) -> Option<&Node<&'expr str>> { self.nodes.first() }

    /// Iterator over the elements of the tree in pre-order.
    ///
    /// Because expression trees are constructed in pre-order, this iterator
    /// is as simple as an in-order iterator over a vector, and should therefore
    /// have very good cache locality.
    pub fn pre_order_iter(&self) -> core::slice::Iter<Node<&str>> { self.nodes.iter() }
}

#[cfg(bench)]
mod benches {
    use test::{black_box, Bencher};

    use super::*;

    #[bench]
    pub fn parse_tree(bh: &mut Bencher) {
        bh.iter(|| {
            let tree = Tree::from_str(
                "and(thresh(2,and(sha256(H),or(sha256(H),pk(A))),pk(B),pk(C),pk(D),sha256(H)),pk(E))",
            ).unwrap();
            black_box(tree);
        });
    }

    #[bench]
    pub fn parse_tree_deep(bh: &mut Bencher) {
        bh.iter(|| {
            let tree = Tree::from_str(
                "and(and(and(and(and(and(and(and(and(and(and(and(and(and(and(and(and(and(and(and(1,2),3),4),5),6),7),8),9),10),11),12),13),14),15),16),17),18),19),20),21)"
            ).unwrap();
            black_box(tree);
        });
    }
}
