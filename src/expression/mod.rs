// SPDX-License-Identifier: CC0-1.0

//! # Function-like Expression Language
//!

mod error;
pub mod tree;

use core::fmt;
use core::str::FromStr;

pub use error::{
    InvalidCharacterError, LeafError, ParseNumError, ParseThresholdError, ParseTreeError,
};

use crate::prelude::*;
use crate::{errstr, Error, ResultExt as _, Threshold, WithSpan, MAX_RECURSION_DEPTH};

/// Allowed characters are descriptor strings.
pub const INPUT_CHARSET: &str = "0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#\"\\ ";

/// Map of valid characters in descriptor strings.
#[rustfmt::skip]
pub const VALID_CHARS: [Option<u8>; 128] = [
    None, None, None, None, None, None, None, None, None, None, None, None, None,
    None, None, None, None, None, None, None, None, None, None, None, None, None,
    None, None, None, None, None, None, Some(94), Some(59), Some(92), Some(91),
    Some(28), Some(29), Some(50), Some(15), Some(10), Some(11), Some(17), Some(51),
    Some(14), Some(52), Some(53), Some(16), Some(0), Some(1), Some(2), Some(3),
    Some(4), Some(5), Some(6), Some(7), Some(8), Some(9), Some(27), Some(54),
    Some(55), Some(56), Some(57), Some(58), Some(26), Some(82), Some(83),
    Some(84), Some(85), Some(86), Some(87), Some(88), Some(89), Some(32), Some(33),
    Some(34), Some(35), Some(36), Some(37), Some(38), Some(39), Some(40), Some(41),
    Some(42), Some(43), Some(44), Some(45), Some(46), Some(47), Some(48), Some(49),
    Some(12), Some(93), Some(13), Some(60), Some(61), Some(90), Some(18), Some(19),
    Some(20), Some(21), Some(22), Some(23), Some(24), Some(25), Some(64), Some(65),
    Some(66), Some(67), Some(68), Some(69), Some(70), Some(71), Some(72), Some(73),
    Some(74), Some(75), Some(76), Some(77), Some(78), Some(79), Some(80), Some(81),
    Some(30), Some(62), Some(31), Some(63), None,
];

#[derive(Debug)]
/// A token of the form `x(...)` or `x`
pub struct Tree<'a> {
    /// The name `x`
    pub name: &'a str,
    /// The comma-separated contents of the `(...)`, if any
    pub args: Vec<Tree<'a>>,
}
// or_b(pk(A),pk(B))
//
// A = musig(musig(B,C),D,E)
// or_b()
// pk(A), pk(B)

/// A trait for extracting a structure from a Tree representation in token form
pub trait FromTree: Sized {
    /// Extract a structure from Tree representation
    fn from_tree(top: &Tree) -> Result<Self, Error>;
}

enum Found {
    Nothing,
    LBracket(usize), // Either a left ( or {
    Comma(usize),
    RBracket(usize), // Either a right ) or }
}

fn next_expr(sl: &str, delim: char) -> Found {
    let mut found = Found::Nothing;
    if delim == '(' {
        for (n, ch) in sl.char_indices() {
            match ch {
                '(' => {
                    found = Found::LBracket(n);
                    break;
                }
                ',' => {
                    found = Found::Comma(n);
                    break;
                }
                ')' => {
                    found = Found::RBracket(n);
                    break;
                }
                _ => {}
            }
        }
    } else if delim == '{' {
        let mut new_count = 0;
        for (n, ch) in sl.char_indices() {
            match ch {
                '{' => {
                    found = Found::LBracket(n);
                    break;
                }
                '(' => {
                    new_count += 1;
                }
                ',' => {
                    if new_count == 0 {
                        found = Found::Comma(n);
                        break;
                    }
                }
                ')' => {
                    new_count -= 1;
                }
                '}' => {
                    found = Found::RBracket(n);
                    break;
                }
                _ => {}
            }
        }
    } else {
        unreachable!("{}", "Internal: delimiters in parsing must be '(' or '{'");
    }
    found
}

// Get the corresponding delim
fn closing_delim(delim: char) -> char {
    match delim {
        '(' => ')',
        '{' => '}',
        _ => unreachable!("Unknown delimiter"),
    }
}

impl<'a> Tree<'a> {
    /// Parse an expression with round brackets
    pub fn from_slice(sl: &'a str) -> Result<(Tree<'a>, &'a str), Error> {
        // Parsing TapTree or just miniscript
        Self::from_slice_delim(sl, 0u32, '(')
    }

    pub(crate) fn from_slice_delim(
        mut sl: &'a str,
        depth: u32,
        delim: char,
    ) -> Result<(Tree<'a>, &'a str), Error> {
        if depth >= MAX_RECURSION_DEPTH {
            return Err(Error::MaxRecursiveDepthExceeded);
        }

        match next_expr(sl, delim) {
            // String-ending terminal
            Found::Nothing => Ok((Tree { name: sl, args: vec![] }, "")),
            // Terminal
            Found::Comma(n) | Found::RBracket(n) => {
                Ok((Tree { name: &sl[..n], args: vec![] }, &sl[n..]))
            }
            // Function call
            Found::LBracket(n) => {
                let mut ret = Tree { name: &sl[..n], args: vec![] };

                sl = &sl[n + 1..];
                loop {
                    let (arg, new_sl) = Tree::from_slice_delim(sl, depth + 1, delim)?;
                    ret.args.push(arg);

                    if new_sl.is_empty() {
                        return Err(Error::ExpectedChar(closing_delim(delim)));
                    }

                    sl = &new_sl[1..];
                    match new_sl.as_bytes()[0] {
                        b',' => {}
                        last_byte => {
                            if last_byte == closing_delim(delim) as u8 {
                                break;
                            } else {
                                return Err(Error::ExpectedChar(closing_delim(delim)));
                            }
                        }
                    }
                }
                Ok((ret, sl))
            }
        }
    }

    /// Parses a tree from a string
    #[allow(clippy::should_implement_trait)] // Cannot use std::str::FromStr because of lifetimes.
    pub fn from_str(s: &'a str) -> Result<Tree<'a>, Error> {
        check_valid_chars(s)?;

        let (top, rem) = Tree::from_slice(s)?;
        if rem.is_empty() {
            Ok(top)
        } else {
            Err(errstr(rem))
        }
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
    pub fn to_null_threshold<const MAX: usize>(
        &self,
    ) -> Result<Threshold<(), MAX>, ParseThresholdError> {
        // First, special case "no arguments" so we can index the first argument without panics.
        if self.args.is_empty() {
            return Err(ParseThresholdError::NoChildren);
        }

        if !self.args[0].args.is_empty() {
            return Err(ParseThresholdError::KNotTerminal);
        }

        let k = parse_num(self.args[0].name)
            .map_err(|e| ParseThresholdError::ParseK(e.to_string()))? as usize;
        Threshold::new(k, vec![(); self.args.len() - 1]).map_err(ParseThresholdError::Threshold)
    }
}

/// Filter out non-ASCII because we byte-index strings all over the
/// place and Rust gets very upset when you splinch a string.
pub fn check_valid_chars(s: &str) -> Result<(), Error> {
    for ch in s.bytes() {
        if !ch.is_ascii() {
            return Err(Error::Unprintable(ch));
        }
        // Index bounds: We know that ch is ASCII, so it is <= 127.
        if VALID_CHARS[ch as usize].is_none() {
            return Err(Error::Unexpected(
                "Only characters in INPUT_CHARSET are allowed".to_string(),
            ));
        }
    }
    Ok(())
}

// This function will be renamed to `check_valid_chars`, which will be deleted, in a later commit.
/// Filter out non-ASCII because we byte-index strings all over the
/// place and Rust gets very upset when you splinch a string.
///
/// Returns the number of nodes, as determined by counting `)` and `,`
/// characters.
fn check_valid_chars2(s: &str) -> Result<usize, WithSpan<InvalidCharacterError>> {
    let mut ret = 0;
    for (n, ch) in s.char_indices() {
        // Index bounds: We know that ch is ASCII, so it is <= 127.
        if !ch.is_ascii() || VALID_CHARS[ch as usize].is_none() {
            return Err(InvalidCharacterError::invalid_character(ch)).with_index(n);
        }
        ret += usize::from(ch == ')' || ch == ',');
    }
    Ok(ret)
}

/// Parse a string as a u32, for timelocks or thresholds
pub fn parse_num(s: &str) -> Result<u32, Error> {
    if s.len() > 1 {
        let ch = s.chars().next().unwrap();
        if !('1'..='9').contains(&ch) {
            return Err(Error::Unexpected("Number must start with a digit 1-9".to_string()));
        }
    }
    u32::from_str(s).map_err(|_| errstr(s))
}

/// Attempts to parse a terminal expression
pub fn terminal<T, F, Err>(term: &Tree, convert: F) -> Result<T, Error>
where
    F: FnOnce(&str) -> Result<T, Err>,
    Err: fmt::Display,
{
    if term.args.is_empty() {
        convert(term.name).map_err(|e| Error::Unexpected(e.to_string()))
    } else {
        Err(errstr(term.name))
    }
}

/// Attempts to parse an expression with exactly one child
pub fn unary<L, T, F>(term: &Tree, convert: F) -> Result<T, Error>
where
    L: FromTree,
    F: FnOnce(L) -> T,
{
    if term.args.len() == 1 {
        let left = FromTree::from_tree(&term.args[0])?;
        Ok(convert(left))
    } else {
        Err(errstr(term.name))
    }
}

/// Attempts to parse an expression with exactly two children
pub fn binary<L, R, T, F>(term: &Tree, convert: F) -> Result<T, Error>
where
    L: FromTree,
    R: FromTree,
    F: FnOnce(L, R) -> T,
{
    if term.args.len() == 2 {
        let left = FromTree::from_tree(&term.args[0])?;
        let right = FromTree::from_tree(&term.args[1])?;
        Ok(convert(left, right))
    } else {
        Err(errstr(term.name))
    }
}

#[cfg(test)]
mod tests {
    use super::parse_num;

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
    fn test_valid_char_map() {
        let mut valid_chars = [None; 128];
        for (i, ch) in super::INPUT_CHARSET.chars().enumerate() {
            valid_chars[ch as usize] = Some(i as u8);
        }
        assert_eq!(valid_chars, super::VALID_CHARS);
    }
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
