// SPDX-License-Identifier: CC0-1.0

//! # Function-like Expression Language
//!

mod error;

use core::ops;
use core::str::FromStr;

pub use self::error::{ParseNumError, ParseThresholdError, ParseTreeError};
use crate::blanket_traits::StaticDebugAndDisplay;
use crate::descriptor::checksum::verify_checksum;
use crate::iter::{self, TreeLike};
use crate::prelude::*;
use crate::{AbsLockTime, Error, ParseError, RelLockTime, Threshold, MAX_RECURSION_DEPTH};

/// Allowed characters are descriptor strings.
pub const INPUT_CHARSET: &str = "0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#\"\\ ";

#[derive(Debug)]
/// A token of the form `x(...)` or `x`
pub struct Tree<'a> {
    /// The name `x`
    name: &'a str,
    /// Position one past the last character of the node's name. If it has
    /// children, the position of the '(' or '{'.
    children_pos: usize,
    /// The type of parentheses surrounding the node's children.
    parens: Parens,
    /// The comma-separated contents of the `(...)`, if any
    args: Vec<Tree<'a>>,
}

impl PartialEq for Tree<'_> {
    fn eq(&self, other: &Self) -> bool {
        let mut stack = vec![(self, other)];
        while let Some((me, you)) = stack.pop() {
            if me.name != you.name || me.args.len() != you.args.len() {
                return false;
            }
            stack.extend(me.args.iter().zip(you.args.iter()));
        }
        true
    }
}
impl Eq for Tree<'_> {}

impl<'a, 't> TreeLike for &'t Tree<'a> {
    type NaryChildren = &'t [Tree<'a>];

    fn nary_len(tc: &Self::NaryChildren) -> usize { tc.len() }
    fn nary_index(tc: Self::NaryChildren, idx: usize) -> Self { &tc[idx] }

    fn as_node(&self) -> iter::Tree<Self, Self::NaryChildren> {
        if self.args.is_empty() {
            iter::Tree::Nullary
        } else {
            iter::Tree::Nary(&self.args)
        }
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
    fn from_tree(top: &Tree) -> Result<Self, Error>;
}

impl<'a> Tree<'a> {
    /// The name of this tree node.
    pub fn name(&self) -> &str { self.name }

    /// The 0-indexed byte-position of the name in the original expression tree.
    pub fn name_pos(&self) -> usize { self.children_pos - self.name.len() - 1 }

    /// The 0-indexed byte-position of the '(' or '{' character which starts the
    /// expression's children.
    ///
    /// If the expression has no children, returns one past the end of the name.
    pub fn children_pos(&self) -> usize { self.children_pos - self.name.len() - 1 }

    /// The number of children this node has.
    pub fn n_children(&self) -> usize { self.args.len() }

    /// The type of parenthesis surrounding this node's children.
    ///
    /// If the node has no children, this will be `Parens::None`.
    pub fn parens(&self) -> Parens { self.parens }

    /// An iterator over the direct children of this node.
    ///
    /// If you want to iterate recursively, use the [`TreeLike`] API which
    /// provides methods `pre_order_iter` and `post_order_iter`.
    pub fn children(&self) -> impl ExactSizeIterator<Item = &Self> { self.args.iter() }

    /// Split the name by a separating character.
    ///
    /// If the separator is present, returns the prefix before the separator and
    /// the suffix after the separator. Otherwise returns the whole name.
    ///
    /// If the separator occurs multiple times, returns an error.
    pub fn name_separated(&self, separator: char) -> Result<(Option<&str>, &str), ParseTreeError> {
        let mut name_split = self.name.splitn(3, separator);
        match (name_split.next(), name_split.next(), name_split.next()) {
            (None, _, _) => unreachable!("'split' always yields at least one element"),
            (Some(_), None, _) => Ok((None, self.name)),
            (Some(prefix), Some(name), None) => Ok((Some(prefix), name)),
            (Some(_), Some(_), Some(suffix)) => Err(ParseTreeError::MultipleSeparators {
                separator,
                pos: self.children_pos - suffix.len() - 1,
            }),
        }
    }

    /// Check that a tree node has the given number of children.
    ///
    /// The `description` argument is only used to populate the error return,
    /// and is not validated in any way.
    pub fn verify_n_children(
        &self,
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
    ) -> Result<&Self, ParseTreeError> {
        assert!(
            !n_children.contains(&0),
            "verify_toplevel is intended for nodes with >= 1 child"
        );

        if self.name != name {
            Err(ParseTreeError::IncorrectName { actual: self.name.to_owned(), expected: name })
        } else if self.parens == Parens::Curly {
            Err(ParseTreeError::IllegalCurlyBrace { pos: self.children_pos })
        } else {
            self.verify_n_children(name, n_children)?;
            Ok(&self.args[0])
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
        self.args[0]
            .verify_n_children("absolute locktime", 0..=0)
            .map_err(ParseError::Tree)?;
        parse_num(self.args[0].name)
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
        self.args[0]
            .verify_n_children("relative locktime", 0..=0)
            .map_err(ParseError::Tree)?;
        parse_num(self.args[0].name)
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
        T::from_str(self.name).map_err(ParseError::box_from_str)
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
        self.args[0].verify_terminal(inner_description)
    }

    /// Check that a tree node has exactly two children.
    ///
    /// If so, return them.
    ///
    /// The `description` argument is only used to populate the error return,
    /// and is not validated in any way.
    pub fn verify_binary(
        &self,
        description: &'static str,
    ) -> Result<(&Self, &Self), ParseTreeError> {
        self.verify_n_children(description, 2..=2)?;
        Ok((&self.args[0], &self.args[1]))
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
        F: FnMut(&Self) -> Result<T, E>,
        T,
        E: From<ParseThresholdError>,
    >(
        &self,
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

    /// Check that a tree has no curly-brace children in it.
    pub fn verify_no_curly_braces(&self) -> Result<(), ParseTreeError> {
        for tree in self.pre_order_iter() {
            if tree.parens == Parens::Curly {
                return Err(ParseTreeError::IllegalCurlyBrace { pos: tree.children_pos });
            }
        }
        Ok(())
    }

    /// Check that a string is a well-formed expression string, with optional
    /// checksum.
    ///
    /// Returns the string with the checksum removed and its tree depth.
    fn parse_pre_check(s: &str) -> Result<(&str, usize), ParseTreeError> {
        // First, scan through string to make sure it is well-formed.
        // Do ASCII/checksum check first; after this we can use .bytes().enumerate() rather
        // than .char_indices(), which is *significantly* faster.
        let s = verify_checksum(s)?;

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
            } else if ch == b',' && open_paren_stack.is_empty() {
                // We consider commas outside of the tree to be "trailing characters"
                return Err(ParseTreeError::TrailingCharacter { ch: ch.into(), pos });
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

        Ok((s, max_depth))
    }

    /// Parses a tree from a string
    #[allow(clippy::should_implement_trait)] // Cannot use std::str::FromStr because of lifetimes.
    pub fn from_str(s: &'a str) -> Result<Self, Error> {
        Self::from_str_inner(s)
            .map_err(From::from)
            .map_err(Error::Parse)
    }

    fn from_str_inner(s: &'a str) -> Result<Self, ParseTreeError> {
        // First, scan through string to make sure it is well-formed.
        let (s, max_depth) = Self::parse_pre_check(s)?;

        // Now, knowing it is sane and well-formed, we can easily parse it backward,
        // which will yield a post-order right-to-left iterator of its nodes.
        let mut stack = Vec::with_capacity(max_depth);
        let mut children_parens: Option<(Vec<_>, usize, Parens)> = None;
        let mut node_name_end = s.len();
        for (pos, ch) in s.bytes().enumerate().rev() {
            if ch == b')' || ch == b'}' {
                stack.push(vec![]);
                node_name_end = pos;
            } else if ch == b',' {
                let (mut args, children_pos, parens) =
                    children_parens
                        .take()
                        .unwrap_or((vec![], node_name_end, Parens::None));
                args.reverse();

                let top = stack.last_mut().unwrap();
                let new_tree =
                    Tree { name: &s[pos + 1..node_name_end], children_pos, parens, args };
                top.push(new_tree);
                node_name_end = pos;
            } else if ch == b'(' || ch == b'{' {
                let (mut args, children_pos, parens) =
                    children_parens
                        .take()
                        .unwrap_or((vec![], node_name_end, Parens::None));
                args.reverse();

                let mut top = stack.pop().unwrap();
                let new_tree =
                    Tree { name: &s[pos + 1..node_name_end], children_pos, parens, args };
                top.push(new_tree);
                children_parens = Some((
                    top,
                    pos,
                    match ch {
                        b'(' => Parens::Round,
                        b'{' => Parens::Curly,
                        _ => unreachable!(),
                    },
                ));
                node_name_end = pos;
            }
        }

        assert_eq!(stack.len(), 0);
        let (mut args, children_pos, parens) =
            children_parens
                .take()
                .unwrap_or((vec![], node_name_end, Parens::None));
        args.reverse();
        Ok(Tree { name: &s[..node_name_end], children_pos, parens, args })
    }
}

/// Parse a string as a u32, for timelocks or thresholds
pub fn parse_num(s: &str) -> Result<u32, ParseNumError> {
    if s == "0" {
        // Special-case 0 since it is the only number which may start with a leading zero.
        return Ok(0);
    }
    if let Some(ch) = s.chars().next() {
        if !('1'..='9').contains(&ch) {
            return Err(ParseNumError::InvalidLeadingDigit(ch));
        }
    }
    u32::from_str(s).map_err(ParseNumError::StdParse)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ParseError;

    /// Test functions to manually build trees
    fn leaf(name: &str) -> Tree {
        Tree { name, parens: Parens::None, children_pos: name.len(), args: vec![] }
    }

    fn paren_node<'a>(name: &'a str, mut args: Vec<Tree<'a>>) -> Tree<'a> {
        let mut offset = name.len() + 1; // +1 for open paren
        for arg in &mut args {
            arg.children_pos += offset;
            offset += arg.name.len() + 1; // +1 for comma
        }

        Tree { name, parens: Parens::Round, children_pos: name.len(), args }
    }

    fn brace_node<'a>(name: &'a str, mut args: Vec<Tree<'a>>) -> Tree<'a> {
        let mut offset = name.len() + 1; // +1 for open paren
        for arg in &mut args {
            arg.children_pos += offset;
            offset += arg.name.len() + 1; // +1 for comma
        }

        Tree { name, parens: Parens::Curly, children_pos: name.len(), args }
    }

    #[test]
    fn test_parse_num() {
        assert!(parse_num("0").is_ok());
        assert!(parse_num("00").is_err());
        assert!(parse_num("0000").is_err());
        assert!(parse_num("06").is_err());
        assert!(parse_num("+6").is_err());
        assert!(parse_num("-6").is_err());
    }

    #[test]
    fn parse_tree_basic() {
        assert_eq!(Tree::from_str("thresh").unwrap(), leaf("thresh"));

        assert!(matches!(
            Tree::from_str("thresh,").unwrap_err(),
            Error::Parse(ParseError::Tree(ParseTreeError::TrailingCharacter { ch: ',', pos: 6 })),
        ));

        assert!(matches!(
            Tree::from_str("thresh,thresh").unwrap_err(),
            Error::Parse(ParseError::Tree(ParseTreeError::TrailingCharacter { ch: ',', pos: 6 })),
        ));

        assert!(matches!(
            Tree::from_str("thresh()thresh()").unwrap_err(),
            Error::Parse(ParseError::Tree(ParseTreeError::TrailingCharacter { ch: 't', pos: 8 })),
        ));

        assert_eq!(Tree::from_str("thresh()").unwrap(), paren_node("thresh", vec![leaf("")]));

        assert!(matches!(
            Tree::from_str("thresh(a()b)"),
            Err(Error::Parse(ParseError::Tree(ParseTreeError::ExpectedParenOrComma {
                ch: 'b',
                pos: 10
            }))),
        ));

        assert!(matches!(
            Tree::from_str("thresh()xyz"),
            Err(Error::Parse(ParseError::Tree(ParseTreeError::TrailingCharacter {
                ch: 'x',
                pos: 8
            }))),
        ));
    }

    #[test]
    fn parse_tree_parens() {
        assert!(matches!(
            Tree::from_str("a(").unwrap_err(),
            Error::Parse(ParseError::Tree(ParseTreeError::UnmatchedOpenParen { ch: '(', pos: 1 })),
        ));

        assert!(matches!(
            Tree::from_str(")").unwrap_err(),
            Error::Parse(ParseError::Tree(ParseTreeError::UnmatchedCloseParen { ch: ')', pos: 0 })),
        ));

        assert!(matches!(
            Tree::from_str("x(y))").unwrap_err(),
            Error::Parse(ParseError::Tree(ParseTreeError::TrailingCharacter { ch: ')', pos: 4 })),
        ));

        /* Will be enabled in a later PR which unifies TR and non-TR parsing.
        assert!(matches!(
            Tree::from_str("a{").unwrap_err(),
            Error::Parse(ParseError::Tree(ParseTreeError::UnmatchedOpenParen { ch: '{', pos: 1 })),
        ));

        assert!(matches!(
            Tree::from_str("}").unwrap_err(),
            Error::Parse(ParseError::Tree(ParseTreeError::UnmatchedCloseParen { ch: '}', pos: 0 })),
        ));
        */

        assert!(matches!(
            Tree::from_str("x(y)}").unwrap_err(),
            Error::Parse(ParseError::Tree(ParseTreeError::TrailingCharacter { ch: '}', pos: 4 })),
        ));

        /* Will be enabled in a later PR which unifies TR and non-TR parsing.
        assert!(matches!(
            Tree::from_str("x{y)").unwrap_err(),
            Error::Parse(ParseError::Tree(ParseTreeError::MismatchedParens {
                open_ch: '{',
                open_pos: 1,
                close_ch: ')',
                close_pos: 3,
            }),)
        ));
        */
    }

    #[test]
    fn parse_tree_taproot() {
        assert_eq!(
            Tree::from_str("a{b(c),d}").unwrap(),
            brace_node("a", vec![paren_node("b", vec![leaf("c")]), leaf("d")]),
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
            paren_node(
                "wsh",
                vec![paren_node(
                    "t:or_c",
                    vec![
                        paren_node("pk", vec![leaf(keys[0])]),
                        paren_node("v:pkh", vec![leaf(keys[1])]),
                    ]
                )]
            ),
        );
    }
}
