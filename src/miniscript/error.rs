// SPDX-License-Identifier: CC0-1.0

//! Miniscript Errors

use core::fmt;

use crate::WithSpan;

/// An error constructing a Miniscript.
#[derive(PartialEq, Eq, Debug)]
pub enum ConstructError {
    /// Typechecking failed.
    ///
    /// These errors indicate that the Miniscript was not well-formed,
    /// and if constructed would not have any sensible semantics in the
    /// Bitcoin Script interpreter.
    TypeCheck(WithSpan<crate::miniscript::types::Error>),
    /// Validation of the constructed object failed.
    ///
    /// These errors indicate failed checks that are mostly configurable.
    /// Under many circumstances a script which fails a validation check
    /// can still be used on-chain if the user knows exactly what they
    /// are doing.
    Validation(crate::ValidationError),
}

impl ConstructError {
    /// Assumes that a construction error is a validation error and returns it.
    ///
    /// # Panics
    ///
    /// Panics if the construction error is actually a typecheck error.
    pub fn unwrap_validation_err(self) -> crate::ValidationError {
        match self {
            Self::TypeCheck(e) => {
                panic!("attempted to unwrap a validation error, but had a typecheck error ({})", e)
            }
            Self::Validation(e) => e,
        }
    }
}

impl fmt::Display for ConstructError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::TypeCheck(ref e) => e.fmt(f),
            Self::Validation(ref e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ConstructError {
    fn cause(&self) -> Option<&dyn std::error::Error> {
        match *self {
            Self::TypeCheck(ref e) => Some(e),
            Self::Validation(ref e) => Some(e),
        }
    }
}

/// An error that occurs when converting from an expression tree into a real object.
///
/// There are two types of errors: parsing errors (where the expression tree
/// was malformed or a name was invalid) and construction errors (where the tree
/// was well-formed but the Miniscript fails a consistency or type check.
#[derive(PartialEq, Eq, Debug)]
pub enum ParseMiniscriptError {
    /// A parsing error.
    Parse(crate::ParseError),
    /// Tried to construct a Taproot tree which was too deep.
    TapTreeDepthError(crate::descriptor::TapTreeDepthError),
    /// A validation error.
    Construct(ConstructError),
}

// Lots of sub-errors of ParseError, do do a blanket From from them
// to ParseMiniscriptError.
impl<E> From<E> for ParseMiniscriptError
where
    crate::ParseError: From<E>,
{
    fn from(e: E) -> Self { Self::Parse(crate::ParseError::from(e)) }
}

impl From<crate::descriptor::TapTreeDepthError> for ParseMiniscriptError {
    fn from(e: crate::descriptor::TapTreeDepthError) -> Self { Self::TapTreeDepthError(e) }
}

impl From<ConstructError> for ParseMiniscriptError {
    fn from(e: ConstructError) -> Self { Self::Construct(e) }
}

impl From<crate::ValidationError> for ParseMiniscriptError {
    fn from(e: crate::ValidationError) -> Self { Self::Construct(ConstructError::Validation(e)) }
}

impl From<WithSpan<crate::miniscript::types::Error>> for ParseMiniscriptError {
    fn from(e: WithSpan<crate::miniscript::types::Error>) -> Self {
        Self::Construct(ConstructError::TypeCheck(e))
    }
}

impl fmt::Display for ParseMiniscriptError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Parse(ref e) => e.fmt(f),
            Self::TapTreeDepthError(ref e) => e.fmt(f),
            Self::Construct(ref e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseMiniscriptError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Parse(ref e) => Some(e),
            Self::TapTreeDepthError(ref e) => Some(e),
            Self::Construct(ref e) => Some(e),
        }
    }
}
