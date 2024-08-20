// SPDX-License-Identifier: CC0-1.0

//! Concrete Policy Enum
//!
//! This module defines the [`Inner`] type which represents the kind of a node
//! in a [`super::Policy`] tree.
//!

use crate::{AbsLockTime, MiniscriptKey, RelLockTime, Threshold, Translator};

#[derive(Clone, Debug)]
pub enum Inner<Pk: MiniscriptKey, C> {
    /// Unsatisfiable.
    Unsatisfiable,
    /// Trivially satisfiable.
    Trivial,
    /// A public key which must sign to satisfy the descriptor.
    Key(Pk),
    /// An absolute locktime restriction.
    After(AbsLockTime),
    /// A relative locktime restriction.
    Older(RelLockTime),
    /// A SHA256 whose preimage must be provided to satisfy the descriptor.
    Sha256(Pk::Sha256),
    /// A SHA256d whose preimage must be provided to satisfy the descriptor.
    Hash256(Pk::Hash256),
    /// A RIPEMD160 whose preimage must be provided to satisfy the descriptor.
    Ripemd160(Pk::Ripemd160),
    /// A HASH160 whose preimage must be provided to satisfy the descriptor.
    Hash160(Pk::Hash160),
    /// A list of sub-policies, all of which must be satisfied.
    And(C, C),
    /// A list of sub-policies, one of which must be satisfied, along with
    /// relative probabilities for each one.
    Or((f64, C), (f64, C)),
    /// A set of descriptors, satisfactions must be provided for `k` of them.
    Thresh(Threshold<C, 0>),
}

impl<Pk: MiniscriptKey, C> Inner<Pk, C> {
    /// Maps the children of an [`Inner`] to different types.
    ///
    /// This function is **not** recursive and will only translate a single layer.
    pub fn map_ref<C2, FC>(&self, mut fc: FC) -> Inner<Pk, C2>
    where
        FC: FnMut(&C) -> C2,
    {
        match self {
            Inner::Unsatisfiable => Inner::Unsatisfiable,
            Inner::Trivial => Inner::Trivial,
            Inner::Key(ref pk) => Inner::Key(pk.clone()),
            Inner::Sha256(ref h) => Inner::Sha256(h.clone()),
            Inner::Hash256(ref h) => Inner::Hash256(h.clone()),
            Inner::Ripemd160(ref h) => Inner::Ripemd160(h.clone()),
            Inner::Hash160(ref h) => Inner::Hash160(h.clone()),
            Inner::Older(ref n) => Inner::Older(*n),
            Inner::After(ref n) => Inner::After(*n),
            Inner::And(left, right) => Inner::And(fc(left), fc(right)),
            Inner::Or((lp, left), (rp, right)) => Inner::Or((*lp, fc(left)), (*rp, fc(right))),
            Inner::Thresh(thresh) => Inner::Thresh(thresh.map_ref(fc)),
        }
    }

    /// Converts a one kind of public key to another type of public key.
    ///
    /// This function is **not** recursive and will only translate a single layer.
    pub fn translate_pk<T>(self, t: &mut T) -> Result<Inner<T::TargetPk, C>, T::Error>
    where
        T: Translator<Pk>,
    {
        match self {
            Inner::Unsatisfiable => Ok(Inner::Unsatisfiable),
            Inner::Trivial => Ok(Inner::Trivial),
            Inner::Key(ref pk) => t.pk(pk).map(Inner::Key),
            Inner::Sha256(ref h) => t.sha256(h).map(Inner::Sha256),
            Inner::Hash256(ref h) => t.hash256(h).map(Inner::Hash256),
            Inner::Ripemd160(ref h) => t.ripemd160(h).map(Inner::Ripemd160),
            Inner::Hash160(ref h) => t.hash160(h).map(Inner::Hash160),
            Inner::Older(n) => Ok(Inner::Older(n)),
            Inner::After(n) => Ok(Inner::After(n)),
            Inner::And(left, right) => Ok(Inner::And(left, right)),
            Inner::Or(left, right) => Ok(Inner::Or(left, right)),
            Inner::Thresh(thresh) => Ok(Inner::Thresh(thresh)),
        }
    }
}
