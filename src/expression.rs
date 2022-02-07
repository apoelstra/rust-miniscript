// Miniscript
// Written in 2019 by
//     Andrew Poelstra <apoelstra@wpsoftware.net>
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

//! # Function-like Expression Language
//!

use std::str::FromStr;

use errstr;
use Error;

use MAX_RECURSION_DEPTH;

#[derive(Debug)]
/// A token of the form `x(...)` or `x`
pub struct Tree<'a> {
    /// The name `x`
    pub name: &'a str,
    /// The comma-separated contents of the `(...)`, if any
    pub args: Vec<Tree<'a>>,
}

/// A trait for extracting a structure from a Tree representation in token form
pub trait FromTree: Sized {
    /// Extract a structure from Tree representation
    fn from_tree(top: &Tree) -> Result<Self, Error>;
}

impl<'a> Tree<'a> {
    /// Parse an expression with round brackets
    pub fn from_slice(sl: &'a str) -> Result<(Tree<'a>, &'a str), Error> {
        // Parsing TapTree or just miniscript
        Self::from_slice_helper_round(sl, 0u32)
    }

    fn from_slice_helper_round(mut sl: &'a str, depth: u32) -> Result<(Tree<'a>, &'a str), Error> {
        if depth >= MAX_RECURSION_DEPTH {
            return Err(Error::MaxRecursiveDepthExceeded);
        }
        enum Found {
            Nothing,
            Lparen(usize),
            Comma(usize),
            Rparen(usize),
        }

        let mut found = Found::Nothing;
        for (n, ch) in sl.char_indices() {
            match ch {
                '(' => {
                    found = Found::Lparen(n);
                    break;
                }
                ',' => {
                    found = Found::Comma(n);
                    break;
                }
                ')' => {
                    found = Found::Rparen(n);
                    break;
                }
                _ => {}
            }
        }

        match found {
            // String-ending terminal
            Found::Nothing => Ok((
                Tree {
                    name: &sl[..],
                    args: vec![],
                },
                "",
            )),
            // Terminal
            Found::Comma(n) | Found::Rparen(n) => Ok((
                Tree {
                    name: &sl[..n],
                    args: vec![],
                },
                &sl[n..],
            )),
            // Function call
            Found::Lparen(n) => {
                let mut ret = Tree {
                    name: &sl[..n],
                    args: vec![],
                };

                sl = &sl[n + 1..];
                loop {
                    let (arg, new_sl) = Tree::from_slice_helper_round(sl, depth + 1)?;
                    ret.args.push(arg);

                    if new_sl.is_empty() {
                        return Err(Error::ExpectedChar(')'));
                    }

                    sl = &new_sl[1..];
                    match new_sl.as_bytes()[0] {
                        b',' => {}
                        b')' => break,
                        _ => return Err(Error::ExpectedChar(',')),
                    }
                }
                Ok((ret, sl))
            }
        }
    }

    // Helper function to parse expressions with curly braces
    pub(crate) fn from_slice_helper_curly(
        mut sl: &'a str,
        depth: u32,
    ) -> Result<(Tree<'a>, &'a str), Error> {
        // contain the context of brackets
        if depth >= MAX_RECURSION_DEPTH {
            return Err(Error::MaxRecursiveDepthExceeded);
        }
        enum Found {
            Nothing,
            Lbrace(usize),
            Comma(usize),
            Rbrace(usize),
        }

        let mut found = Found::Nothing;
        let mut new_count = 0;
        for (n, ch) in sl.char_indices() {
            match ch {
                '{' => {
                    found = Found::Lbrace(n);
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
                    found = Found::Rbrace(n);
                    break;
                }
                _ => {}
            }
        }

        match found {
            // String-ending terminal
            Found::Nothing => Ok((
                Tree {
                    name: &sl[..],
                    args: vec![],
                },
                "",
            )),
            // Terminal
            Found::Comma(n) | Found::Rbrace(n) => Ok((
                Tree {
                    name: &sl[..n],
                    args: vec![],
                },
                &sl[n..],
            )),
            // Function call
            Found::Lbrace(n) => {
                let mut ret = Tree {
                    name: &sl[..n], // Would be empty for left and right assignments
                    args: vec![],
                };

                sl = &sl[n + 1..];
                loop {
                    let (arg, new_sl) = Tree::from_slice_helper_curly(sl, depth + 1)?;
                    ret.args.push(arg);

                    if new_sl.is_empty() {
                        return Err(Error::ExpectedChar('}'));
                    }

                    sl = &new_sl[1..];
                    match new_sl.as_bytes()[0] {
                        b',' => {}
                        b'}' => break,
                        _ => return Err(Error::ExpectedChar(',')),
                    }
                }
                Ok((ret, sl))
            }
        }
    }

    /// Parses a tree from a string
    pub fn from_str(s: &'a str) -> Result<Tree<'a>, Error> {
        // Filter out non-ASCII because we byte-index strings all over the
        // place and Rust gets very upset when you splinch a string.
        for ch in s.bytes() {
            if !ch.is_ascii() {
                return Err(Error::Unprintable(ch));
            }
        }

        let (top, rem) = Tree::from_slice(s)?;
        if rem.is_empty() {
            Ok(top)
        } else {
            Err(errstr(rem))
        }
    }
}

/// Parse a string as a u32, for timelocks or thresholds
pub fn parse_num(s: &str) -> Result<u32, Error> {
    if s.len() > 1 {
        let ch = s.chars().next().unwrap();
        if ch < '1' || ch > '9' {
            return Err(Error::Unexpected(
                "Number must start with a digit 1-9".to_string(),
            ));
        }
    }
    u32::from_str(s).map_err(|_| errstr(s))
}

/// Attempts to parse a terminal expression
pub fn terminal<T, F, Err>(term: &Tree, convert: F) -> Result<T, Error>
where
    F: FnOnce(&str) -> Result<T, Err>,
    Err: ToString,
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

    // Add tests for tapscript parsing
    // tr(D,{or_i(pk(A),pk(B)),{after(9),pk(C)}})
}
