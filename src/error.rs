// Written in 2019 by Andrew Poelstra <apoelstra@wpsoftware.net>
// SPDX-License-Identifier: CC0-1.0

//! Errors

use core::fmt;
#[cfg(feature = "std")]
use std::error;

use crate::blanket_traits::StaticDebugAndDisplay;
use crate::prelude::{String, Vec};
use crate::primitives::absolute_locktime::AbsLockTimeError;
use crate::primitives::relative_locktime::RelLockTimeError;
use crate::Box;

/// An error parsing a Miniscript object (policy, descriptor or miniscript)
/// from a string.
#[derive(Debug)]
pub enum ParseError {
    /// Invalid absolute locktime
    AbsoluteLockTime(AbsLockTimeError),
    /// Invalid relative locktime
    RelativeLockTime(RelLockTimeError),
    /// Failed to parse a public key or hash.
    ///
    /// Note that the error information is lost for nostd compatibility reasons. See
    /// <https://users.rust-lang.org/t/how-to-box-an-error-type-retaining-std-error-only-when-std-is-enabled/>.
    FromStr(Box<dyn StaticDebugAndDisplay>),
    /// Failed to parse a number.
    Num(crate::ParseNumError),
    /// Failed to parse a threshold.
    Threshold(crate::ParseThresholdError),
    /// Error parsing a string into an expression tree.
    Tree(crate::ParseTreeError),
}

impl ParseError {
    /// Boxes a `FromStr` error for a `Pk` (or associated types) into a `ParseError`
    pub(crate) fn box_from_str<E: StaticDebugAndDisplay>(e: E) -> Self {
        ParseError::FromStr(Box::new(e))
    }
}

impl From<crate::ParseNumError> for ParseError {
    fn from(e: crate::ParseNumError) -> Self { Self::Num(e) }
}

impl From<crate::ParseThresholdError> for ParseError {
    fn from(e: crate::ParseThresholdError) -> Self { Self::Threshold(e) }
}

impl From<crate::ParseTreeError> for ParseError {
    fn from(e: crate::ParseTreeError) -> Self { Self::Tree(e) }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseError::AbsoluteLockTime(ref e) => e.fmt(f),
            ParseError::RelativeLockTime(ref e) => e.fmt(f),
            ParseError::FromStr(ref e) => e.fmt(f),
            ParseError::Num(ref e) => e.fmt(f),
            ParseError::Threshold(ref e) => e.fmt(f),
            ParseError::Tree(ref e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for ParseError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            ParseError::AbsoluteLockTime(ref e) => Some(e),
            ParseError::RelativeLockTime(ref e) => Some(e),
            ParseError::FromStr(..) => None,
            ParseError::Num(ref e) => Some(e),
            ParseError::Threshold(ref e) => Some(e),
            ParseError::Tree(ref e) => Some(e),
        }
    }
}

/// An error type endowede with span information describing where the error occurred.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct WithSpan<E> {
    error: E,
    /// List of 0-indexed string positions at which the error occurred.
    ///
    /// When displayed, these are changed to 1-indexed for the user.
    positions: Vec<usize>,
    string: Option<String>,
}

impl<E> WithSpan<E> {
    /// Constructs a [`WithSpan`] from an error and no span information.
    pub fn new(error: E) -> Self { Self { error, positions: Vec::new(), string: None } }

    /// Sets the string that the error positions index into.
    ///
    /// # Panics
    ///
    /// Panics if it is called twice on the same [`WithSpan`].
    pub fn with_string(mut self, s: String) -> Self {
        assert_eq!(self.string, None, "tried to add two strings to withspan error");
        self.string = Some(s);
        self
    }

    /// Adds a 0-indexed position at which an error occurred.
    ///
    /// May be called multiple times. If it is called multiple times with the same
    /// index, only one call will have any effect.
    pub fn at_position(mut self, i: usize) -> Self {
        if let Err(idx) = self.positions.binary_search(&i) {
            self.positions.insert(idx, i);
        }
        self
    }

    /// Converts one type of spanned error to another.
    pub fn map<F>(self, f: impl FnOnce(E) -> F) -> WithSpan<F> {
        WithSpan { error: f(self.error), positions: self.positions, string: self.string }
    }

    /// Drop the span information and return the underlying error.
    pub fn into_inner(self) -> E { self.error }

    /// Accessor for the underlying error.
    pub fn as_inner(&self) -> &E { &self.error }
}

#[cfg(feature = "std")]
impl<E: std::error::Error> std::error::Error for WithSpan<E> {
    fn cause(&self) -> Option<&dyn error::Error> { Some(&self.error) }
}

impl<E: fmt::Display> fmt::Display for WithSpan<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(ref s) = self.string {
            write!(f, "in \"{}\"", s)?;
            if self.positions.is_empty() {
                f.write_str(": ")?
            } else {
                f.write_str(" ")?
            }
        }
        match self.positions.len() {
            0 => {}
            1 => write!(f, "(position {}): ", self.positions[0] + 1)?,
            _ => {
                write!(f, "(positions {}", self.positions[0] + 1)?;
                for pos in self.positions.iter().skip(1) {
                    write!(f, ", {}", pos + 1)?;
                }

                f.write_str("): ")?;
            }
        }
        self.error.fmt(f)
    }
}
