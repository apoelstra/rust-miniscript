// SPDX-License-Identifier: CC0-1.0

//! Expression-related errors

use core::{fmt, num};

use crate::descriptor::checksum;
use crate::prelude::*;
use crate::ThresholdError;

/// An error parsing an expression tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseTreeError {
    /// Error validating the checksum or character set.
    Checksum(checksum::Error),
    /// Expression tree had depth exceeding our hard cap.
    MaxRecursionDepthExceeded {
        /// The depth of the tree that was attempted to be parsed.
        actual: usize,
        /// The maximum depth.
        maximum: u32,
    },
    /// After a close-paren, the only valid next characters are close-parens and commas. Got
    /// something else.
    ExpectedParenOrComma {
        /// What we got instead.
        ch: char,
        /// Its byte-index into the string.
        pos: usize,
    },
    /// An open-parenthesis had no corresponding close-parenthesis.
    UnmatchedOpenParen {
        /// The character in question ('(' or '{')
        ch: char,
        /// Its byte-index into the string.
        pos: usize,
    },
    /// A close-parenthesis had no corresponding open-parenthesis.
    UnmatchedCloseParen {
        /// The character in question (')' or '}')
        ch: char,
        /// Its byte-index into the string.
        pos: usize,
    },
    /// A `(` was matched with a `}` or vice-versa.
    MismatchedParens {
        /// The opening parenthesis ('(' or '{')
        open_ch: char,
        /// The position of the opening parethesis.
        open_pos: usize,
        /// The closing parenthesis (')' or '}')
        close_ch: char,
        /// The position of the closing parethesis.
        close_pos: usize,
    },
    /// A node had the wrong name.
    IncorrectName {
        /// The name that was found.
        actual: String,
        /// The name that was expected.
        expected: &'static str,
    },
    /// A node had the wrong number of children.
    IncorrectNumberOfChildren {
        /// A description of the node in question.
        description: &'static str,
        /// The number of children the node had.
        n_children: usize,
        /// The minimum of children the node should have had.
        minimum: Option<usize>,
        /// The minimum of children the node should have had.
        maximum: Option<usize>,
    },
    /// A Taproot child occurred somewhere it was not allowed.
    IllegalCurlyBrace {
        /// The position of the opening curly brace.
        pos: usize,
    },
    ///  Multiple separators (':' or '@') appeared in a node name.
    MultipleSeparators {
        /// The separator in question.
        separator: char,
        /// The position of the second separator.
        pos: usize,
    },
    /// Data occurred after the final ).
    TrailingCharacter {
        /// The first trailing character.
        ch: char,
        /// Its byte-index into the string.
        pos: usize,
    },
    /// A node's name was not recognized.
    UnknownName {
        /// The name that was not recognized.
        name: String,
    },
}

impl From<checksum::Error> for ParseTreeError {
    fn from(e: checksum::Error) -> Self { Self::Checksum(e) }
}

impl fmt::Display for ParseTreeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseTreeError::Checksum(ref e) => e.fmt(f),
            ParseTreeError::MaxRecursionDepthExceeded { actual, maximum } => {
                write!(f, "maximum recursion depth exceeded (max {}, got {})", maximum, actual)
            }
            ParseTreeError::ExpectedParenOrComma { ch, pos } => {
                write!(
                    f,
                    "invalid character `{}` (position {}); expected comma or close-paren",
                    ch, pos
                )
            }
            ParseTreeError::UnmatchedOpenParen { ch, pos } => {
                write!(f, "`{}` (position {}) not closed", ch, pos)
            }
            ParseTreeError::UnmatchedCloseParen { ch, pos } => {
                write!(f, "`{}` (position {}) not opened", ch, pos)
            }
            ParseTreeError::MismatchedParens { open_ch, open_pos, close_ch, close_pos } => {
                write!(
                    f,
                    "`{}` (position {}) closed by `{}` (position {})",
                    open_ch, open_pos, close_ch, close_pos
                )
            }
            ParseTreeError::IllegalCurlyBrace { pos } => {
                write!(f, "illegal `{{` at position {} (Taproot branches not allowed here)", pos)
            }
            ParseTreeError::IncorrectName { actual, expected } => {
                if expected.is_empty() {
                    write!(f, "found node '{}', expected nameless node", actual)
                } else {
                    write!(f, "expected node '{}', found '{}'", expected, actual)
                }
            }
            ParseTreeError::IncorrectNumberOfChildren {
                description,
                n_children,
                minimum,
                maximum,
            } => {
                write!(f, "{} must have ", description)?;
                match (minimum, maximum) {
                    (_, Some(0)) => f.write_str("no children"),
                    (Some(min), Some(max)) if min == max => write!(f, "{} children", min),
                    (Some(min), None) if n_children < min => write!(f, "at least {} children", min),
                    (Some(min), Some(max)) if n_children < min => write!(f, "at least {} children (maximum {})", min, max),
                    (None, Some(max)) if n_children > max => write!(f, "at most {} children", max),
                    (Some(min), Some(max)) if n_children > max => write!(f, "at most {} children (minimum {})", max, min),
                    (x, y) => panic!("IncorrectNumberOfChildren error was constructed inconsistently (min {:?} max {:?})", x, y),
                }?;
                write!(f, ", but found {}", n_children)
            }
            ParseTreeError::MultipleSeparators { separator, pos } => {
                write!(
                    f,
                    "separator '{}' occurred multiple times (second time at position {})",
                    separator, pos
                )
            }
            ParseTreeError::TrailingCharacter { ch, pos } => {
                write!(f, "trailing data `{}...` (position {})", ch, pos)
            }
            ParseTreeError::UnknownName { name } => write!(f, "unrecognized name '{}'", name),
        }
    }
}
#[cfg(feature = "std")]
impl std::error::Error for ParseTreeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ParseTreeError::Checksum(ref e) => Some(e),
            ParseTreeError::MaxRecursionDepthExceeded { .. }
            | ParseTreeError::ExpectedParenOrComma { .. }
            | ParseTreeError::UnmatchedOpenParen { .. }
            | ParseTreeError::UnmatchedCloseParen { .. }
            | ParseTreeError::MismatchedParens { .. }
            | ParseTreeError::IllegalCurlyBrace { .. }
            | ParseTreeError::IncorrectName { .. }
            | ParseTreeError::IncorrectNumberOfChildren { .. }
            | ParseTreeError::MultipleSeparators { .. }
            | ParseTreeError::TrailingCharacter { .. }
            | ParseTreeError::UnknownName { .. } => None,
        }
    }
}

/// Error parsing a number.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseNumError {
    /// Failed to parse the number at all.
    StdParse(num::ParseIntError),
    /// Number had a leading zero, + or -.
    InvalidLeadingDigit(char),
    /// Number was 0 in a context where zero is not allowed.
    ///
    /// Be aware that locktimes have their own error types and do not use this variant.
    IllegalZero {
        /// A description of the location where 0 was not allowed.
        context: &'static str,
    },
}

impl fmt::Display for ParseNumError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseNumError::StdParse(ref e) => e.fmt(f),
            ParseNumError::InvalidLeadingDigit(ch) => {
                write!(f, "numbers must start with 1-9, not {}", ch)
            }
            ParseNumError::IllegalZero { context } => {
                write!(f, "{} may not be 0", context)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseNumError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ParseNumError::StdParse(ref e) => Some(e),
            ParseNumError::InvalidLeadingDigit(..) => None,
            ParseNumError::IllegalZero { .. } => None,
        }
    }
}

/// Error parsing a threshold expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseThresholdError {
    /// Expression had no children, not even a threshold value.
    NoChildren,
    /// The threshold value appeared to be a sub-expression rather than a number.
    KNotTerminal,
    /// A 1-of-n threshold was used in a context it was not allowed.
    IllegalOr,
    /// A n-of-n threshold was used in a context it was not allowed.
    IllegalAnd,
    /// Failed to parse the threshold value.
    ParseK(ParseNumError),
    /// Threshold parameters were invalid.
    Threshold(ThresholdError),
}

impl fmt::Display for ParseThresholdError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ParseThresholdError::*;

        match *self {
            NoChildren => f.write_str("expected threshold, found terminal"),
            KNotTerminal => f.write_str("expected positive integer, found expression"),
            IllegalOr => f.write_str(
                "1-of-n thresholds not allowed here; please use an 'or' fragment instead",
            ),
            IllegalAnd => f.write_str(
                "n-of-n thresholds not allowed here; please use an 'and' fragment instead",
            ),
            ParseK(ref x) => write!(f, "failed to parse threshold value: {}", x),
            Threshold(ref e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseThresholdError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use ParseThresholdError::*;

        match *self {
            NoChildren | KNotTerminal | IllegalOr | IllegalAnd => None,
            ParseK(ref e) => Some(e),
            Threshold(ref e) => Some(e),
        }
    }
}
