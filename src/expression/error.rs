// SPDX-License-Identifier: CC0-1.0

//! Expression-related errors

use core::fmt;

use crate::prelude::*;
use crate::ThresholdError;

/// Error parsing a threshold expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseThresholdError {
    /// Expression had no children, not even a threshold value.
    NoChildren,
    /// The threshold value appeared to be a sub-expression rather than a number.
    KNotTerminal,
    /// Failed to parse the threshold value.
    // FIXME this should be a more specific type. Will be handled in a later PR
    // that rewrites the expression parsing logic.
    ParseK(String),
    /// Threshold parameters were invalid.
    Threshold(ThresholdError),
}

impl fmt::Display for ParseThresholdError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ParseThresholdError::*;

        match *self {
            NoChildren => f.write_str("expected threshold, found terminal"),
            KNotTerminal => f.write_str("expected positive integer, found expression"),
            ParseK(ref x) => write!(f, "failed to parse threshold value {}", x),
            Threshold(ref e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseThresholdError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use ParseThresholdError::*;

        match *self {
            NoChildren => None,
            KNotTerminal => None,
            ParseK(..) => None,
            Threshold(ref e) => Some(e),
        }
    }
}

/// An expression was not a leaf (it had a nonzero number of children).
#[derive(Debug, PartialEq)]
pub struct NotLeafError {
    n_children: usize,
}

/// An expression tree contained an invalid character (outside of allowed charset).
#[derive(Debug, PartialEq)]
pub struct InvalidStartCharacterError {
    ch: char,
}

/// Error when parsing a number from a leaf node
#[derive(Debug, PartialEq)]
#[non_exhaustive]
pub enum LeafError<E> {
    /// The object to be parsed was not a leaf node.
    NotLeaf(NotLeafError),
    /// Failed to parse the object.
    Parse(E),
}

impl<E> LeafError<E> {
    pub(super) fn not_leaf(n_children: usize) -> Self {
        LeafError::NotLeaf(NotLeafError { n_children })
    }
}

impl<E: fmt::Display> fmt::Display for LeafError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LeafError::NotLeaf(ref inner) => {
                write!(f, "expected terminal, got expression with {} children", inner.n_children)
            }
            LeafError::Parse(ref e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl<E: std::error::Error + 'static> std::error::Error for LeafError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match *self {
            LeafError::NotLeaf(..) => None,
            LeafError::Parse(ref e) => Some(e),
        }
    }
}

/// Error when parsing a number from a leaf node
#[derive(Debug, PartialEq)]
#[non_exhaustive]
pub enum ParseNumError {
    /// A number did not start with a digit in the range 1-9.
    InvalidStartCharacter(InvalidStartCharacterError),
    /// Failed to parse the number as a u32.
    ParseU32(core::num::ParseIntError),
}

impl LeafError<ParseNumError> {
    pub(super) fn invalid_start_character(ch: char) -> Self {
        LeafError::Parse(ParseNumError::InvalidStartCharacter(InvalidStartCharacterError { ch }))
    }

    pub(super) fn parse_u32(err: core::num::ParseIntError) -> Self {
        LeafError::Parse(ParseNumError::ParseU32(err))
    }
}

impl fmt::Display for ParseNumError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ParseNumError::InvalidStartCharacter(ref e) => {
                write!(f, "numbers may not start with '{}'", e.ch)
            }
            ParseNumError::ParseU32(ref e) => {
                write!(f, "could not parse number: {}", e)
            }
        }
    }
}

/// An expression tree contained an invalid character (outside of allowed charset).
#[derive(Debug, PartialEq)]
pub struct InvalidCharacterError {
    ch: char,
}

impl InvalidCharacterError {
    pub(super) fn invalid_character(ch: char) -> Self { InvalidCharacterError { ch } }
}

impl fmt::Display for InvalidCharacterError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "invalid character `{}`", self.ch)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvalidCharacterError {}

/// Maximum recursive depth (distance from root to leaf) was exceeded for a tree.
#[derive(Debug, PartialEq)]
pub struct MaxRecursiveDepthExceededError {
    maximum_depth: u32,
}

impl MaxRecursiveDepthExceededError {
    /// Accessor for the maximum allowed depth
    pub fn maximum_depth(&self) -> u32 { self.maximum_depth }
}

impl fmt::Display for MaxRecursiveDepthExceededError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "exceeded maximum recursive depth (limit {})", self.maximum_depth)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for MaxRecursiveDepthExceededError {}

/// An expression tree had a close-paren without a corresponding open-paren
#[derive(Debug, PartialEq)]
#[non_exhaustive]
pub struct OverterminatedTreeError {}

impl fmt::Display for OverterminatedTreeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("expression tree had an unmatched `)`")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for OverterminatedTreeError {}

/// An expression tree had an open-paren without a corresponding close-paren
#[derive(Debug, PartialEq)]
#[non_exhaustive]
pub struct UnterminatedTreeError {}

impl fmt::Display for UnterminatedTreeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("expression tree had an unmatched `(`")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for UnterminatedTreeError {}

/// Error when parsing a tree from a string
#[derive(Debug, PartialEq)]
#[non_exhaustive]
pub enum ParseTreeError {
    /// An expression tree contained an invalid character (outside of allowed charset).
    InvalidCharacter(InvalidCharacterError),
    /// Maximum recursive depth (distance from root to leaf) was exceeded for a tree.
    MaxRecursiveDepthExceeded(MaxRecursiveDepthExceededError),
    /// An expression tree had a close-paren without a corresponding open-paren
    OverterminatedTree(OverterminatedTreeError),
    /// An expression tree had an open-paren without a corresponding close-paren
    UnterminatedTree(UnterminatedTreeError),
}

impl ParseTreeError {
    pub(super) fn max_recursive_depth_exceeded(maximum_depth: u32) -> Self {
        ParseTreeError::MaxRecursiveDepthExceeded(MaxRecursiveDepthExceededError { maximum_depth })
    }

    pub(super) fn overterminated_tree() -> Self {
        ParseTreeError::OverterminatedTree(OverterminatedTreeError {})
    }

    pub(super) fn unterminated_tree() -> Self {
        ParseTreeError::UnterminatedTree(UnterminatedTreeError {})
    }
}

impl fmt::Display for ParseTreeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ParseTreeError::*;
        match *self {
            InvalidCharacter(ref e) => e.fmt(f),
            MaxRecursiveDepthExceeded(ref e) => e.fmt(f),
            OverterminatedTree(ref e) => e.fmt(f),
            UnterminatedTree(ref e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseTreeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use ParseTreeError::*;
        match *self {
            InvalidCharacter(ref e) => Some(e),
            MaxRecursiveDepthExceeded(ref e) => Some(e),
            OverterminatedTree(ref e) => Some(e),
            UnterminatedTree(ref e) => Some(e),
        }
    }
}
