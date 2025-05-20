// SPDX-License-Identifier: CC0-1.0

//! Miniscript Errors

use core::fmt;

/// An error constructing a Miniscript.
#[derive(Debug, PartialEq, Eq)]
pub enum ConstructError {
    /// Typechecking failed.
    ///
    /// These errors indicate that the Miniscript was not well-formed,
    /// and if constructed would not have any sensible semantics in the
    /// Bitcoin Script interpreter.
    TypeCheck(crate::miniscript::types::Error),
    /// Validation of the constructed object failed.
    ///
    /// These errors indicate failed checks that are mostly configurable.
    /// Under many circumstances a script which fails a validation check
    /// can still be used on-chain if the user knows exactly what they
    /// are doing.
    Validation(crate::ValidationError),
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
