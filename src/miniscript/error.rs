// SPDX-License-Identifier: CC0-1.0

use core::fmt;
use core::str::FromStr;

use bitcoin::hashes::hash160;

use crate::expression::tree::Node;
use crate::expression::{LeafError, ParseNumError, ParseThresholdError, ParseTreeError};
use crate::miniscript::analyzable::AnalysisError;
use crate::miniscript::types;
use crate::{AbsLockTimeError, BoxedError, RelLockTimeError};

/// Found a fragment that was invalid for the position it was in.
#[derive(Debug, PartialEq)]
pub struct InvalidFragmentError {
    expected: &'static str,
    got: Node<String>,
}

impl fmt::Display for InvalidFragmentError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "expected {}, got {}", self.expected, self.got.data(),)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvalidFragmentError {}

/// A threshold combinator had no children, just a threshold value.
#[derive(Debug, PartialEq)]
pub struct NonTopLevelError {
    ty: types::Base,
}

impl fmt::Display for NonTopLevelError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "top-level expression had type {:?}, not B", self.ty)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for NonTopLevelError {}

/// Error when parsing a tree from a string
#[derive(Debug)]
#[non_exhaustive]
pub enum ParseError {
    /// Error parsing an absolute locktime.
    AbsLockTime(AbsLockTimeError),
    /// Failed some static check (e.g. resource limits)
    Analysis(AnalysisError),
    /// Tried to parse an empty string.
    EmptyString,
    /// Failed to parse the expression tree.
    Expression(ParseTreeError),
    /// Failed to parse a number.
    FromStrNum(LeafError<ParseNumError>),
    /// Failed to parse a public key.
    FromStrPk(LeafError<BoxedError>),
    /// Failed to parse a sha256 hash.
    FromStrSha256(LeafError<BoxedError>),
    /// Failed to parse a hash256 hash.
    FromStrHash256(LeafError<BoxedError>),
    /// Failed to parse a ripemd160 hash.
    FromStrRipemd160(LeafError<BoxedError>),
    /// Failed to parse a hash160 hash.
    FromStrHash160(LeafError<BoxedError>),
    /// Failed to parse a raw hash160 hash.
    FromStrRawHash160(LeafError<<hash160::Hash as FromStr>::Err>),
    /// Found a fragment that was invalid for the position it was in.
    InvalidFragment(InvalidFragmentError),
    /// The top-level fragment did not have the "B" type.
    NonTopLevel(NonTopLevelError),
    /// A threshold combinator had no children, not even a threshold value.
    ParseThreshold(ParseThresholdError),
    /// Error parsing a relative locktime.
    RelLockTime(RelLockTimeError),
}

impl ParseError {
    pub(super) fn invalid_fragment(node: &Node<&str>, expected: &'static str) -> Self {
        ParseError::InvalidFragment(InvalidFragmentError {
            expected,
            got: node.map_ref(|&s| s.to_owned()),
        })
    }

    pub(super) fn non_top_level(ty: types::Base) -> Self {
        ParseError::NonTopLevel(NonTopLevelError { ty })
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ParseError::*;
        match *self {
            AbsLockTime(ref e) => e.fmt(f),
            Analysis(ref e) => e.fmt(f),
            EmptyString => f.write_str("empty string"),
            Expression(ref e) => e.fmt(f),
            FromStrNum(ref e) => e.fmt(f),
            FromStrPk(ref e) => e.fmt(f),
            FromStrSha256(ref e) => e.fmt(f),
            FromStrHash256(ref e) => e.fmt(f),
            FromStrRipemd160(ref e) => e.fmt(f),
            FromStrHash160(ref e) => e.fmt(f),
            FromStrRawHash160(ref e) => e.fmt(f),
            InvalidFragment(ref e) => e.fmt(f),
            NonTopLevel(ref e) => e.fmt(f),
            ParseThreshold(ref e) => e.fmt(f),
            RelLockTime(ref e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use ParseError::*;
        match *self {
            AbsLockTime(ref e) => Some(e),
            Analysis(ref e) => Some(e),
            EmptyString => None,
            Expression(ref e) => Some(e),
            FromStrNum(ref e) => Some(e),
            FromStrPk(ref e) => None,
            FromStrSha256(ref e) => None,
            FromStrHash256(ref e) => None,
            FromStrRipemd160(ref e) => None,
            FromStrHash160(ref e) => None,
            FromStrRawHash160(ref e) => Some(e),
            InvalidFragment(ref e) => Some(e),
            NonTopLevel(ref e) => Some(e),
            ParseThreshold(ref e) => Some(e),
            RelLockTime(ref e) => Some(e),
        }
    }
}
