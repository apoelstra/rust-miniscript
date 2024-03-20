// SPDX-License-Identifier: CC0-1.0

//! Blanket Traits
//!
//! Because of this library's heavy use of generics, we often require complicated
//! trait bounds (especially when it comes to [`FromStr`] and its
//! associated error types). These blanket traits act as aliases, allowing easier
//! descriptions of them.
//!
//! While these traits are not sealed, they have blanket-impls which prevent you
//! from directly implementing them on your own types. The traits will be
//! automatically implemented if you satisfy all the bounds.
//!

use core::str::FromStr;
use core::{fmt, hash};

use crate::error::BoxableError;
use crate::MiniscriptKey;

/// Blanket trait describing a key where all associated types implement `FromStr`,
/// and all `FromStr` errors can be displayed.
pub trait FromStrKey:
    MiniscriptKey<
        Sha256 = Self::_Sha256,
        Hash256 = Self::_Hash256,
        Ripemd160 = Self::_Ripemd160,
        Hash160 = Self::_Hash160,
    > + FromStr<Err = Self::_FromStrErr>
{
    /// Dummy type. Do not use.
    type _Sha256: FromStr<Err = Self::_Sha256FromStrErr>
        + Clone
        + Eq
        + Ord
        + fmt::Display
        + fmt::Debug
        + hash::Hash;
    /// Dummy type. Do not use.
    type _Sha256FromStrErr: fmt::Debug + fmt::Display + BoxableError;
    /// Dummy type. Do not use.
    type _Hash256: FromStr<Err = Self::_Hash256FromStrErr>
        + Clone
        + Eq
        + Ord
        + fmt::Display
        + fmt::Debug
        + hash::Hash;
    /// Dummy type. Do not use.
    type _Hash256FromStrErr: fmt::Debug + fmt::Display + BoxableError;
    /// Dummy type. Do not use.
    type _Ripemd160: FromStr<Err = Self::_Ripemd160FromStrErr>
        + Clone
        + Eq
        + Ord
        + fmt::Display
        + fmt::Debug
        + hash::Hash;
    /// Dummy type. Do not use.
    type _Ripemd160FromStrErr: fmt::Debug + fmt::Display + BoxableError;
    /// Dummy type. Do not use.
    type _Hash160: FromStr<Err = Self::_Hash160FromStrErr>
        + Clone
        + Eq
        + Ord
        + fmt::Display
        + fmt::Debug
        + hash::Hash;
    /// Dummy type. Do not use.
    type _Hash160FromStrErr: fmt::Debug + fmt::Display + BoxableError;
    /// Dummy type. Do not use.
    type _FromStrErr: fmt::Debug + fmt::Display + BoxableError;
}

impl<T> FromStrKey for T
where
    Self: MiniscriptKey + FromStr,
    <Self as MiniscriptKey>::Sha256: FromStr,
    Self::Hash256: FromStr,
    Self::Ripemd160: FromStr,
    Self::Hash160: FromStr,
    <Self as FromStr>::Err: fmt::Debug + fmt::Display,
    <<Self as MiniscriptKey>::Sha256 as FromStr>::Err: fmt::Debug + fmt::Display,
    <Self::Hash256 as FromStr>::Err: fmt::Debug + fmt::Display,
    <Self::Ripemd160 as FromStr>::Err: fmt::Debug + fmt::Display,
    <Self::Hash160 as FromStr>::Err: fmt::Debug + fmt::Display,
{
    type _Sha256 = <T as MiniscriptKey>::Sha256;
    type _Sha256FromStrErr = <<T as MiniscriptKey>::Sha256 as FromStr>::Err;
    type _Hash256 = <T as MiniscriptKey>::Hash256;
    type _Hash256FromStrErr = <<T as MiniscriptKey>::Hash256 as FromStr>::Err;
    type _Ripemd160 = <T as MiniscriptKey>::Ripemd160;
    type _Ripemd160FromStrErr = <<T as MiniscriptKey>::Ripemd160 as FromStr>::Err;
    type _Hash160 = <T as MiniscriptKey>::Hash160;
    type _Hash160FromStrErr = <<T as MiniscriptKey>::Hash160 as FromStr>::Err;
    type _FromStrErr = <T as FromStr>::Err;
}
