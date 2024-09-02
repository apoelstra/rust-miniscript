// SPDX-License-Identifier: CC0-1.0

//! Abstract Policies
//!
//! We use the terms "semantic" and "abstract" interchangeably because
//! "abstract" is a reserved keyword in Rust.

use core::{fmt, str};

use bitcoin::{absolute, relative};

use super::ENTAILMENT_MAX_TERMINALS;
use crate::iter::{Tree, TreeLike};
use crate::prelude::*;
use crate::sync::Arc;
use crate::{
    expression, AbsLockTime, Error, ForEachKey, FromStrKey, MiniscriptKey, RelLockTime, Threshold,
    Translator,
};

/// Abstract policy which corresponds to the semantics of a miniscript and
/// which allows complex forms of analysis, e.g. filtering and normalization.
///
/// Semantic policies store only hashes of keys to ensure that objects
/// representing the same policy are lifted to the same abstract `Policy`,
/// regardless of their choice of `pk` or `pk_h` nodes.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Policy<Pk: MiniscriptKey> {
    /// Unsatisfiable.
    Unsatisfiable,
    /// Trivially satisfiable.
    Trivial,
    /// Signature and public key matching a given hash is required.
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
    /// A set of descriptors, satisfactions must be provided for `k` of them.
    Thresh(Threshold<Arc<Policy<Pk>>, 0>),
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Policy<Pk> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, mut pred: F) -> bool {
        self.pre_order_iter().all(|policy| match policy {
            Policy::Key(ref pk) => pred(pk),
            _ => true,
        })
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// Converts a policy using one kind of public key to another type of public key.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::str::FromStr;
    /// use miniscript::bitcoin::{hashes::hash160, PublicKey};
    /// use miniscript::{translate_hash_fail, policy::semantic::Policy, Translator};
    /// let alice_pk = "02c79ef3ede6d14f72a00d0e49b4becfb152197b64c0707425c4f231df29500ee7";
    /// let bob_pk = "03d008a849fbf474bd17e9d2c1a827077a468150e58221582ec3410ab309f5afe4";
    /// let placeholder_policy = Policy::<String>::from_str("and(pk(alice_pk),pk(bob_pk))").unwrap();
    ///
    /// // Information to translate abstract string type keys to concrete `bitcoin::PublicKey`s.
    /// // In practice, wallets would map from string key names to BIP32 keys.
    /// struct StrPkTranslator {
    ///     pk_map: HashMap<String, bitcoin::PublicKey>
    /// }
    ///
    /// // If we also wanted to provide mapping of other associated types (sha256, older etc),
    /// // we would use the general [`Translator`] trait.
    /// impl Translator<String> for StrPkTranslator {
    ///     type TargetPk = bitcoin::PublicKey;
    ///     type Error = ();
    ///
    ///     fn pk(&mut self, pk: &String) -> Result<bitcoin::PublicKey, Self::Error> {
    ///         self.pk_map.get(pk).copied().ok_or(()) // Dummy Err
    ///     }
    ///
    ///     // Handy macro for failing if we encounter any other fragment.
    ///     // See also [`translate_hash_clone!`] for cloning instead of failing.
    ///     translate_hash_fail!(String, bitcoin::PublicKey, ());
    /// }
    ///
    /// let mut pk_map = HashMap::new();
    /// pk_map.insert(String::from("alice_pk"), bitcoin::PublicKey::from_str(alice_pk).unwrap());
    /// pk_map.insert(String::from("bob_pk"), bitcoin::PublicKey::from_str(bob_pk).unwrap());
    /// let mut t = StrPkTranslator { pk_map };
    ///
    /// let real_policy = placeholder_policy.translate_pk(&mut t).unwrap();
    ///
    /// let expected_policy = Policy::from_str(&format!("and(pk({}),pk({}))", alice_pk, bob_pk)).unwrap();
    /// assert_eq!(real_policy, expected_policy);
    /// ```
    pub fn translate_pk<T>(&self, t: &mut T) -> Result<Policy<T::TargetPk>, T::Error>
    where
        T: Translator<Pk>,
    {
        use Policy::*;

        let mut translated = vec![];
        for data in self.rtl_post_order_iter() {
            let new_policy = match data.node {
                Unsatisfiable => Unsatisfiable,
                Trivial => Trivial,
                Key(ref pk) => t.pk(pk).map(Key)?,
                Sha256(ref h) => t.sha256(h).map(Sha256)?,
                Hash256(ref h) => t.hash256(h).map(Hash256)?,
                Ripemd160(ref h) => t.ripemd160(h).map(Ripemd160)?,
                Hash160(ref h) => t.hash160(h).map(Hash160)?,
                Older(ref n) => Older(*n),
                After(ref n) => After(*n),
                Thresh(ref thresh) => Thresh(thresh.map_ref(|_| translated.pop().unwrap())),
            };
            translated.push(Arc::new(new_policy));
        }
        // Unwrap is ok because we know we processed at least one node.
        let root_node = translated.pop().unwrap();
        // Unwrap is ok because we know `root_node` is the only strong reference.
        Ok(Arc::try_unwrap(root_node).unwrap())
    }

    /// Computes whether the current policy entails the second one.
    ///
    /// A |- B means every satisfaction of A is also a satisfaction of B.
    ///
    /// This implementation will run slowly for larger policies but should be
    /// sufficient for most practical policies.
    ///
    /// Returns None for very large policies for which entailment cannot
    /// be practically computed.
    // This algorithm has a naive implementation. It is possible to optimize this
    // by memoizing and maintaining a hashmap.
    pub fn entails(self, other: Policy<Pk>) -> Option<bool> {
        if self.n_terminals() > ENTAILMENT_MAX_TERMINALS {
            return None;
        }
        match (self, other) {
            (Policy::Unsatisfiable, _) => Some(true),
            (Policy::Trivial, Policy::Trivial) => Some(true),
            (Policy::Trivial, _) => Some(false),
            (_, Policy::Unsatisfiable) => Some(false),
            (a, b) => {
                let (a_norm, b_norm) = (a.normalized(), b.normalized());
                let first_constraint = a_norm.first_constraint();
                let (a1, b1) = (
                    a_norm.clone().satisfy_constraint(&first_constraint, true),
                    b_norm.clone().satisfy_constraint(&first_constraint, true),
                );
                let (a2, b2) = (
                    a_norm.satisfy_constraint(&first_constraint, false),
                    b_norm.satisfy_constraint(&first_constraint, false),
                );
                Some(Policy::entails(a1, b1)? && Policy::entails(a2, b2)?)
            }
        }
    }

    // Helper function to compute the number of constraints in policy.
    fn n_terminals(&self) -> usize {
        use Policy::*;

        let mut n_terminals = vec![];
        for data in self.rtl_post_order_iter() {
            let num = match data.node {
                Thresh(thresh) => (0..thresh.n()).map(|_| n_terminals.pop().unwrap()).sum(),
                Trivial | Unsatisfiable => 0,
                _leaf => 1,
            };
            n_terminals.push(num);
        }
        // Ok to unwrap because we know we processed at least one node.
        n_terminals.pop().unwrap()
    }

    // Helper function to get the first constraint in the policy.
    // Returns the first leaf policy. Used in policy entailment.
    // Assumes that the current policy is normalized.
    fn first_constraint(&self) -> Policy<Pk> {
        debug_assert!(self.clone().normalized() == self.clone());
        match self {
            Policy::Thresh(ref thresh) => thresh.data()[0].first_constraint(),
            first => first.clone(),
        }
    }

    // Helper function that takes in witness and its availability, changing it
    // to true or false and returning the resultant normalized policy. Witness
    // is currently encoded as policy. Only accepts leaf fragment and a
    // normalized policy
    pub(crate) fn satisfy_constraint(self, witness: &Policy<Pk>, available: bool) -> Policy<Pk> {
        debug_assert!(self.clone().normalized() == self);
        if let Policy::Thresh { .. } = *witness {
            // We can't debug_assert on Policy::Thresh.
            panic!("should be unreachable")
        }

        let ret =
            match self {
                Policy::Thresh(thresh) => Policy::Thresh(thresh.map(|sub| {
                    Arc::new(sub.as_ref().clone().satisfy_constraint(witness, available))
                })),
                ref leaf if leaf == witness => {
                    if available {
                        Policy::Trivial
                    } else {
                        Policy::Unsatisfiable
                    }
                }
                x => x,
            };
        ret.normalized()
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Policy<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Policy::Unsatisfiable => f.write_str("UNSATISFIABLE()"),
            Policy::Trivial => f.write_str("TRIVIAL()"),
            Policy::Key(ref pkh) => write!(f, "pk({:?})", pkh),
            Policy::After(n) => write!(f, "after({})", n),
            Policy::Older(n) => write!(f, "older({})", n),
            Policy::Sha256(ref h) => write!(f, "sha256({})", h),
            Policy::Hash256(ref h) => write!(f, "hash256({})", h),
            Policy::Ripemd160(ref h) => write!(f, "ripemd160({})", h),
            Policy::Hash160(ref h) => write!(f, "hash160({})", h),
            Policy::Thresh(ref thresh) => {
                if thresh.k() == thresh.n() {
                    thresh.debug("and", false).fmt(f)
                } else if thresh.k() == 1 {
                    thresh.debug("or", false).fmt(f)
                } else {
                    thresh.debug("thresh", true).fmt(f)
                }
            }
        }
    }
}

impl<Pk: MiniscriptKey> fmt::Display for Policy<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Policy::Unsatisfiable => f.write_str("UNSATISFIABLE"),
            Policy::Trivial => f.write_str("TRIVIAL"),
            Policy::Key(ref pkh) => write!(f, "pk({})", pkh),
            Policy::After(n) => write!(f, "after({})", n),
            Policy::Older(n) => write!(f, "older({})", n),
            Policy::Sha256(ref h) => write!(f, "sha256({})", h),
            Policy::Hash256(ref h) => write!(f, "hash256({})", h),
            Policy::Ripemd160(ref h) => write!(f, "ripemd160({})", h),
            Policy::Hash160(ref h) => write!(f, "hash160({})", h),
            Policy::Thresh(ref thresh) => {
                if thresh.k() == thresh.n() {
                    thresh.display("and", false).fmt(f)
                } else if thresh.k() == 1 {
                    thresh.display("or", false).fmt(f)
                } else {
                    thresh.display("thresh", true).fmt(f)
                }
            }
        }
    }
}

impl<Pk: FromStrKey> str::FromStr for Policy<Pk> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Policy<Pk>, Error> {
        let tree = expression::Tree::from_str(s)?;
        expression::FromTree::from_tree(&tree)
    }
}

serde_string_impl_pk!(Policy, "a miniscript semantic policy");

impl<Pk: FromStrKey> expression::FromTree for Policy<Pk> {
    fn from_tree(top: &expression::Tree) -> Result<Policy<Pk>, Error> {
        match top.name() {
            "UNSATISFIABLE" => {
                top.verify_n_children("UNSATISFIABLE", 0..=0)
                    .map_err(From::from)
                    .map_err(Error::Parse)?;
                Ok(Policy::Unsatisfiable)
            }
            "TRIVIAL" => {
                top.verify_n_children("TRIVIAL", 0..=0)
                    .map_err(From::from)
                    .map_err(Error::Parse)?;
                Ok(Policy::Trivial)
            }
            "pk" => top
                .verify_terminal_parent("pk", "public key")
                .map(Policy::Key)
                .map_err(Error::Parse),
            "after" => top.verify_after().map_err(Error::Parse).map(Policy::After),
            "older" => top.verify_older().map_err(Error::Parse).map(Policy::Older),
            "sha256" => top
                .verify_terminal_parent("sha256", "hash")
                .map(Policy::Sha256)
                .map_err(Error::Parse),
            "hash256" => top
                .verify_terminal_parent("hash256", "hash")
                .map(Policy::Hash256)
                .map_err(Error::Parse),
            "ripemd160" => top
                .verify_terminal_parent("ripemd160", "hash")
                .map(Policy::Ripemd160)
                .map_err(Error::Parse),
            "hash160" => top
                .verify_terminal_parent("hash160", "hash")
                .map(Policy::Hash160)
                .map_err(Error::Parse),
            "and" => {
                top.verify_n_children("and", 2..)
                    .map_err(From::from)
                    .map_err(Error::Parse)?;
                let subs = top
                    .children()
                    .map(|arg| Self::from_tree(arg).map(Arc::new))
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok(Policy::Thresh(Threshold::new(subs.len(), subs).map_err(Error::Threshold)?))
            }
            "or" => {
                top.verify_n_children("or", 2..)
                    .map_err(From::from)
                    .map_err(Error::Parse)?;
                let subs = top
                    .children()
                    .map(|arg| Self::from_tree(arg).map(Arc::new))
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok(Policy::Thresh(Threshold::new(1, subs).map_err(Error::Threshold)?))
            }
            "thresh" => {
                let thresh = top.verify_threshold(|sub| Self::from_tree(sub).map(Arc::new))?;

                // thresh(1) and thresh(n) are disallowed in semantic policies
                if thresh.is_or() {
                    return Err(Error::ParseThreshold(crate::ParseThresholdError::IllegalOr));
                }
                if thresh.is_and() {
                    return Err(Error::ParseThreshold(crate::ParseThresholdError::IllegalAnd));
                }

                Ok(Policy::Thresh(thresh))
            }
            x => Err(Error::Parse(crate::ParseError::Tree(crate::ParseTreeError::UnknownName {
                name: x.to_owned(),
            }))),
        }
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// Flattens out trees of `And`s and `Or`s; eliminate `Trivial` and
    /// `Unsatisfiable`s. Does not reorder any branches; use `.sort`.
    pub fn normalized(self) -> Policy<Pk> {
        match self {
            Policy::Thresh(thresh) => {
                let mut ret_subs = Vec::with_capacity(thresh.n());

                let subs: Vec<_> = thresh
                    .iter()
                    .map(|sub| Arc::new(sub.as_ref().clone().normalized()))
                    .collect();
                let trivial_count = subs
                    .iter()
                    .filter(|&pol| *pol.as_ref() == Policy::Trivial)
                    .count();
                let unsatisfied_count = subs
                    .iter()
                    .filter(|&pol| *pol.as_ref() == Policy::Unsatisfiable)
                    .count();

                let n = subs.len() - unsatisfied_count - trivial_count; // remove all true/false
                let m = thresh.k().saturating_sub(trivial_count); // satisfy all trivial

                let is_and = m == n;
                let is_or = m == 1;

                for sub in subs {
                    match sub.as_ref() {
                        Policy::Trivial | Policy::Unsatisfiable => {}
                        Policy::Thresh(ref subthresh) => {
                            match (is_and, is_or) {
                                (true, true) => {
                                    // means m = n = 1, thresh(1,X) type thing.
                                    ret_subs.push(Arc::new(Policy::Thresh(subthresh.clone())));
                                }
                                (true, false) if subthresh.k() == subthresh.n() => {
                                    ret_subs.extend(subthresh.iter().cloned())
                                } // and case
                                (false, true) if subthresh.k() == 1 => {
                                    ret_subs.extend(subthresh.iter().cloned())
                                } // or case
                                _ => ret_subs.push(Arc::new(Policy::Thresh(subthresh.clone()))),
                            }
                        }
                        x => ret_subs.push(Arc::new(x.clone())),
                    }
                }
                // Now reason about m of n threshold
                if m == 0 {
                    Policy::Trivial
                } else if m > ret_subs.len() {
                    Policy::Unsatisfiable
                } else if ret_subs.len() == 1 {
                    let policy = ret_subs.pop().unwrap();
                    // Only one strong reference because we created the Arc when pushing to ret_subs.
                    Arc::try_unwrap(policy).unwrap()
                } else if is_and {
                    // unwrap ok since ret_subs is nonempty
                    Policy::Thresh(Threshold::new(ret_subs.len(), ret_subs).unwrap())
                } else if is_or {
                    // unwrap ok since ret_subs is nonempty
                    Policy::Thresh(Threshold::new(1, ret_subs).unwrap())
                } else {
                    // unwrap ok since ret_subs is nonempty and we made sure m <= ret_subs.len
                    Policy::Thresh(Threshold::new(m, ret_subs).unwrap())
                }
            }
            x => x,
        }
    }

    /// Detects a true/trivial policy.
    ///
    /// Only checks whether the policy is `Policy::Trivial`, to check if the
    /// normalized form is trivial, the caller is expected to normalize the
    /// policy first.
    pub fn is_trivial(&self) -> bool { matches!(*self, Policy::Trivial) }

    /// Detects a false/unsatisfiable policy.
    ///
    /// Only checks whether the policy is `Policy::Unsatisfiable`, to check if
    /// the normalized form is unsatisfiable, the caller is expected to
    /// normalize the policy first.
    pub fn is_unsatisfiable(&self) -> bool { matches!(*self, Policy::Unsatisfiable) }

    /// Helper function to do the recursion in `timelocks`.
    fn real_relative_timelocks(&self) -> Vec<u32> {
        self.pre_order_iter()
            .filter_map(|policy| match policy {
                Policy::Older(t) => Some(t.to_consensus_u32()),
                _ => None,
            })
            .collect()
    }

    /// Returns a list of all relative timelocks, not including 0, which appear
    /// in the policy.
    pub fn relative_timelocks(&self) -> Vec<u32> {
        let mut ret = self.real_relative_timelocks();
        ret.sort_unstable();
        ret.dedup();
        ret
    }

    /// Helper function for recursion in `absolute timelocks`
    fn real_absolute_timelocks(&self) -> Vec<u32> {
        self.pre_order_iter()
            .filter_map(|policy| match policy {
                Policy::After(t) => Some(t.to_consensus_u32()),
                _ => None,
            })
            .collect()
    }

    /// Returns a list of all absolute timelocks, not including 0, which appear
    /// in the policy.
    pub fn absolute_timelocks(&self) -> Vec<u32> {
        let mut ret = self.real_absolute_timelocks();
        ret.sort_unstable();
        ret.dedup();
        ret
    }

    /// Filters a policy by eliminating relative timelock constraints
    /// that are not satisfied at the given `age`.
    pub fn at_age(self, age: relative::LockTime) -> Policy<Pk> {
        use Policy::*;

        let mut at_age = vec![];
        for data in Arc::new(self).rtl_post_order_iter() {
            let new_policy = match data.node.as_ref() {
                Older(ref t) => {
                    if relative::LockTime::from(*t).is_implied_by(age) {
                        Some(Older(*t))
                    } else {
                        Some(Unsatisfiable)
                    }
                }
                Thresh(ref thresh) => Some(Thresh(thresh.map_ref(|_| at_age.pop().unwrap()))),
                _ => None,
            };
            match new_policy {
                Some(new_policy) => at_age.push(Arc::new(new_policy)),
                None => at_age.push(Arc::clone(data.node)),
            }
        }
        // Unwrap is ok because we know we processed at least one node.
        let root_node = at_age.pop().unwrap();
        // Unwrap is ok because we know `root_node` is the only strong reference.
        let policy = Arc::try_unwrap(root_node).unwrap();
        policy.normalized()
    }

    /// Filters a policy by eliminating absolute timelock constraints
    /// that are not satisfied at the given `n` (`n OP_CHECKLOCKTIMEVERIFY`).
    pub fn at_lock_time(self, n: absolute::LockTime) -> Policy<Pk> {
        use Policy::*;

        let mut at_age = vec![];
        for data in Arc::new(self).rtl_post_order_iter() {
            let new_policy = match data.node.as_ref() {
                After(t) => {
                    if absolute::LockTime::from(*t).is_implied_by(n) {
                        Some(After(*t))
                    } else {
                        Some(Unsatisfiable)
                    }
                }
                Thresh(ref thresh) => Some(Thresh(thresh.map_ref(|_| at_age.pop().unwrap()))),
                _ => None,
            };
            match new_policy {
                Some(new_policy) => at_age.push(Arc::new(new_policy)),
                None => at_age.push(Arc::clone(data.node)),
            }
        }
        // Unwrap is ok because we know we processed at least one node.
        let root_node = at_age.pop().unwrap();
        // Unwrap is ok because we know `root_node` is the only strong reference.
        let policy = Arc::try_unwrap(root_node).unwrap();
        policy.normalized()
    }

    /// Counts the number of public keys and keyhashes referenced in a policy.
    /// Duplicate keys will be double-counted.
    pub fn n_keys(&self) -> usize {
        self.pre_order_iter()
            .filter(|policy| matches!(policy, Policy::Key(..)))
            .count()
    }

    /// Counts the minimum number of public keys for which signatures could be
    /// used to satisfy the policy.
    ///
    /// # Returns
    ///
    /// Returns `None` if the policy is not satisfiable.
    pub fn minimum_n_keys(&self) -> Option<usize> {
        use Policy::*;

        let mut minimum_n_keys = vec![];
        for data in self.rtl_post_order_iter() {
            let minimum_n_key = match data.node {
                Unsatisfiable => None,
                Trivial | After(..) | Older(..) | Sha256(..) | Hash256(..) | Ripemd160(..)
                | Hash160(..) => Some(0),
                Key(..) => Some(1),
                Thresh(ref thresh) => {
                    let mut sublens = (0..thresh.n())
                        .filter_map(|_| minimum_n_keys.pop().unwrap())
                        .collect::<Vec<usize>>();
                    if sublens.len() < thresh.k() {
                        // Not enough branches are satisfiable
                        None
                    } else {
                        sublens.sort_unstable();
                        Some(sublens[0..thresh.k()].iter().cloned().sum::<usize>())
                    }
                }
            };
            minimum_n_keys.push(minimum_n_key);
        }
        // Ok to unwrap because we know we processed at least one node.
        minimum_n_keys.pop().unwrap()
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// "Sorts" a policy to bring it into a canonical form to allow comparisons.
    ///
    /// Does **not** allow policies to be compared for functional equivalence;
    /// in general this appears to require Gröbner basis techniques that are not
    /// implemented.
    pub fn sorted(self) -> Policy<Pk> {
        use Policy::*;

        let mut sorted = vec![];
        for data in Arc::new(self).rtl_post_order_iter() {
            let new_policy = match data.node.as_ref() {
                Thresh(ref thresh) => {
                    let mut new_thresh = thresh.map_ref(|_| sorted.pop().unwrap());
                    new_thresh.data_mut().sort();
                    Some(Thresh(new_thresh))
                }
                _ => None,
            };
            match new_policy {
                Some(new_policy) => sorted.push(Arc::new(new_policy)),
                None => sorted.push(Arc::clone(data.node)),
            }
        }
        // Unwrap is ok because we know we processed at least one node.
        let root_node = sorted.pop().unwrap();
        // Unwrap is ok because we know `root_node` is the only strong reference.
        Arc::try_unwrap(root_node).unwrap()
    }
}

impl<'a, Pk: MiniscriptKey> TreeLike for &'a Policy<Pk> {
    type NaryChildren = &'a [Arc<Policy<Pk>>];

    fn nary_len(tc: &Self::NaryChildren) -> usize { tc.len() }
    fn nary_index(tc: Self::NaryChildren, idx: usize) -> Self { &tc[idx] }

    fn as_node(&self) -> Tree<Self, Self::NaryChildren> {
        use Policy::*;

        match *self {
            Unsatisfiable | Trivial | Key(_) | After(_) | Older(_) | Sha256(_) | Hash256(_)
            | Ripemd160(_) | Hash160(_) => Tree::Nullary,
            Thresh(ref thresh) => Tree::Nary(thresh.data()),
        }
    }
}

impl<'a, Pk: MiniscriptKey> TreeLike for &'a Arc<Policy<Pk>> {
    type NaryChildren = &'a [Arc<Policy<Pk>>];

    fn nary_len(tc: &Self::NaryChildren) -> usize { tc.len() }
    fn nary_index(tc: Self::NaryChildren, idx: usize) -> Self { &tc[idx] }

    fn as_node(&self) -> Tree<Self, Self::NaryChildren> {
        use Policy::*;

        match ***self {
            Unsatisfiable | Trivial | Key(_) | After(_) | Older(_) | Sha256(_) | Hash256(_)
            | Ripemd160(_) | Hash160(_) => Tree::Nullary,
            Thresh(ref thresh) => Tree::Nary(thresh.data()),
        }
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr as _;

    use bitcoin::PublicKey;

    use super::*;

    type StringPolicy = Policy<String>;

    #[test]
    fn parse_policy_err() {
        assert!(StringPolicy::from_str("(").is_err());
        assert!(StringPolicy::from_str("(x()").is_err());
        assert!(StringPolicy::from_str("(\u{7f}()3").is_err());
        assert!(StringPolicy::from_str("pk()").is_ok());

        assert!(StringPolicy::from_str("or(or)").is_err());

        assert!(Policy::<PublicKey>::from_str("pk()").is_err());
        assert!(Policy::<PublicKey>::from_str(
            "pk(\
             0200000000000000000000000000000000000002\
             )"
        )
        .is_err());
        assert!(Policy::<PublicKey>::from_str(
            "pk(\
                02c79ef3ede6d14f72a00d0e49b4becfb152197b64c0707425c4f231df29500ee7\
             )"
        )
        .is_ok());
    }

    #[test]
    fn semantic_analysis() {
        let policy = StringPolicy::from_str("pk()").unwrap();
        assert_eq!(policy, Policy::Key("".to_owned()));
        assert_eq!(policy.relative_timelocks(), vec![]);
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.clone().at_age(RelLockTime::ZERO.into()), policy);
        assert_eq!(
            policy
                .clone()
                .at_age(RelLockTime::from_height(10000).into()),
            policy
        );
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), Some(1));

        let policy = StringPolicy::from_str("older(1000)").unwrap();
        assert_eq!(policy, Policy::Older(RelLockTime::from_height(1000)));
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.relative_timelocks(), vec![1000]);
        assert_eq!(policy.clone().at_age(RelLockTime::ZERO.into()), Policy::Unsatisfiable);
        assert_eq!(
            policy.clone().at_age(RelLockTime::from_height(999).into()),
            Policy::Unsatisfiable
        );
        assert_eq!(policy.clone().at_age(RelLockTime::from_height(1000).into()), policy);
        assert_eq!(
            policy
                .clone()
                .at_age(RelLockTime::from_height(10000).into()),
            policy
        );
        assert_eq!(policy.n_keys(), 0);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        let policy = StringPolicy::from_str("or(pk(),older(1000))").unwrap();
        assert_eq!(
            policy,
            Policy::Thresh(Threshold::or(
                Policy::Key("".to_owned()).into(),
                Policy::Older(RelLockTime::from_height(1000)).into(),
            ))
        );
        assert_eq!(policy.relative_timelocks(), vec![1000]);
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.clone().at_age(RelLockTime::ZERO.into()), Policy::Key("".to_owned()));
        assert_eq!(
            policy.clone().at_age(RelLockTime::from_height(999).into()),
            Policy::Key("".to_owned())
        );
        assert_eq!(
            policy.clone().at_age(RelLockTime::from_height(1000).into()),
            policy.clone().normalized()
        );
        assert_eq!(
            policy
                .clone()
                .at_age(RelLockTime::from_height(10000).into()),
            policy.clone().normalized()
        );
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        let policy = StringPolicy::from_str("or(pk(),UNSATISFIABLE)").unwrap();
        assert_eq!(
            policy,
            Policy::Thresh(Threshold::or(
                Policy::Key("".to_owned()).into(),
                Policy::Unsatisfiable.into()
            ))
        );
        assert_eq!(policy.relative_timelocks(), vec![]);
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), Some(1));

        let policy = StringPolicy::from_str("and(pk(),UNSATISFIABLE)").unwrap();
        assert_eq!(
            policy,
            Policy::Thresh(Threshold::and(
                Policy::Key("".to_owned()).into(),
                Policy::Unsatisfiable.into()
            ))
        );
        assert_eq!(policy.relative_timelocks(), vec![]);
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), None);

        let policy = StringPolicy::from_str(
            "thresh(\
             2,older(1000),older(10000),older(1000),older(2000),older(2000)\
             )",
        )
        .unwrap();
        assert_eq!(
            policy,
            Policy::Thresh(
                Threshold::new(
                    2,
                    vec![
                        Policy::Older(RelLockTime::from_height(1000)).into(),
                        Policy::Older(RelLockTime::from_height(10000)).into(),
                        Policy::Older(RelLockTime::from_height(1000)).into(),
                        Policy::Older(RelLockTime::from_height(2000)).into(),
                        Policy::Older(RelLockTime::from_height(2000)).into(),
                    ]
                )
                .unwrap()
            )
        );
        assert_eq!(
            policy.relative_timelocks(),
            vec![1000, 2000, 10000] //sorted and dedup'd
        );

        let policy = StringPolicy::from_str(
            "thresh(\
             2,older(1000),older(10000),older(1000),UNSATISFIABLE,UNSATISFIABLE\
             )",
        )
        .unwrap();
        assert_eq!(
            policy,
            Policy::Thresh(
                Threshold::new(
                    2,
                    vec![
                        Policy::Older(RelLockTime::from_height(1000)).into(),
                        Policy::Older(RelLockTime::from_height(10000)).into(),
                        Policy::Older(RelLockTime::from_height(1000)).into(),
                        Policy::Unsatisfiable.into(),
                        Policy::Unsatisfiable.into(),
                    ]
                )
                .unwrap()
            )
        );
        assert_eq!(
            policy.relative_timelocks(),
            vec![1000, 10000] //sorted and dedup'd
        );
        assert_eq!(policy.n_keys(), 0);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        // Block height 1000.
        let policy = StringPolicy::from_str("after(1000)").unwrap();
        assert_eq!(policy, Policy::After(AbsLockTime::from_consensus(1000).unwrap()));
        assert_eq!(policy.absolute_timelocks(), vec![1000]);
        assert_eq!(policy.relative_timelocks(), vec![]);
        assert_eq!(policy.clone().at_lock_time(absolute::LockTime::ZERO), Policy::Unsatisfiable);
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(999).expect("valid block height")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(1000).expect("valid block height")),
            policy
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(10000).expect("valid block height")),
            policy
        );
        // Pass a UNIX timestamp to at_lock_time while policy uses a block height.
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_time(500_000_001).expect("valid timestamp")),
            Policy::Unsatisfiable
        );
        assert_eq!(policy.n_keys(), 0);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        // UNIX timestamp of 10 seconds after the epoch.
        let policy = StringPolicy::from_str("after(500000010)").unwrap();
        assert_eq!(policy, Policy::After(AbsLockTime::from_consensus(500_000_010).unwrap()));
        assert_eq!(policy.absolute_timelocks(), vec![500_000_010]);
        assert_eq!(policy.relative_timelocks(), vec![]);
        // Pass a block height to at_lock_time while policy uses a UNIX timestapm.
        assert_eq!(policy.clone().at_lock_time(absolute::LockTime::ZERO), Policy::Unsatisfiable);
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(999).expect("valid block height")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(1000).expect("valid block height")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_height(10000).expect("valid block height")),
            Policy::Unsatisfiable
        );
        // And now pass a UNIX timestamp to at_lock_time while policy also uses a timestamp.
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_time(500_000_000).expect("valid timestamp")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_time(500_000_001).expect("valid timestamp")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_time(500_000_010).expect("valid timestamp")),
            policy
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(absolute::LockTime::from_time(500_000_012).expect("valid timestamp")),
            policy
        );
        assert_eq!(policy.n_keys(), 0);
        assert_eq!(policy.minimum_n_keys(), Some(0));
    }

    #[test]
    fn entailment_liquid_test() {
        //liquid policy
        let liquid_pol = StringPolicy::from_str(
            "or(and(older(4096),thresh(2,pk(A),pk(B),pk(C))),thresh(11,pk(F1),pk(F2),pk(F3),pk(F4),pk(F5),pk(F6),pk(F7),pk(F8),pk(F9),pk(F10),pk(F11),pk(F12),pk(F13),pk(F14)))").unwrap();
        // Very bad idea to add master key,pk but let's have it have 50M blocks
        let master_key = StringPolicy::from_str("and(older(50000000),pk(master))").unwrap();
        let new_liquid_pol =
            Policy::Thresh(Threshold::or(liquid_pol.clone().into(), master_key.into()));

        assert!(liquid_pol.clone().entails(new_liquid_pol.clone()).unwrap());
        assert!(!new_liquid_pol.entails(liquid_pol.clone()).unwrap());

        // test liquid backup policy before the emergency timeout
        let backup_policy = StringPolicy::from_str("thresh(2,pk(A),pk(B),pk(C))").unwrap();
        assert!(!backup_policy
            .entails(
                liquid_pol
                    .clone()
                    .at_age(RelLockTime::from_height(4095).into())
            )
            .unwrap());

        // Finally test both spending paths
        let fed_pol = StringPolicy::from_str("thresh(11,pk(F1),pk(F2),pk(F3),pk(F4),pk(F5),pk(F6),pk(F7),pk(F8),pk(F9),pk(F10),pk(F11),pk(F12),pk(F13),pk(F14))").unwrap();
        let backup_policy_after_expiry =
            StringPolicy::from_str("and(older(4096),thresh(2,pk(A),pk(B),pk(C)))").unwrap();
        assert!(fed_pol.entails(liquid_pol.clone()).unwrap());
        assert!(backup_policy_after_expiry.entails(liquid_pol).unwrap());
    }

    #[test]
    fn entailment_escrow() {
        // Escrow contract
        let escrow_pol = StringPolicy::from_str("thresh(2,pk(Alice),pk(Bob),pk(Judge))").unwrap();
        // Alice's authorization constraint
        // Authorization is a constraint that states the conditions under which one party must
        // be able to redeem the funds.
        let auth_alice = StringPolicy::from_str("and(pk(Alice),pk(Judge))").unwrap();

        //Alice's Control constraint
        // The control constraint states the conditions that one party requires
        // must be met if the funds are spent by anyone
        // Either Alice must authorize the funds or both Judge and Bob must control it
        let control_alice = StringPolicy::from_str("or(pk(Alice),and(pk(Judge),pk(Bob)))").unwrap();

        // Entailment rules
        // Authorization entails |- policy |- control constraints
        assert!(auth_alice.entails(escrow_pol.clone()).unwrap());
        assert!(escrow_pol.entails(control_alice).unwrap());

        // Entailment HTLC's
        // Escrow contract
        let h = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let htlc_pol = StringPolicy::from_str(&format!(
            "or(and(pk(Alice),older(100)),and(pk(Bob),sha256({})))",
            h
        ))
        .unwrap();
        // Alice's authorization constraint
        // Authorization is a constraint that states the conditions under which one party must
        // be able to redeem the funds. In HLTC, alice only cares that she can
        // authorize her funds with Pk and CSV 100.
        let auth_alice = StringPolicy::from_str("and(pk(Alice),older(100))").unwrap();

        //Alice's Control constraint
        // The control constraint states the conditions that one party requires
        // must be met if the funds are spent by anyone
        // Either Alice must authorize the funds or sha2 preimage must be revealed.
        let control_alice =
            StringPolicy::from_str(&format!("or(pk(Alice),sha256({}))", h)).unwrap();

        // Entailment rules
        // Authorization entails |- policy |- control constraints
        assert!(auth_alice.entails(htlc_pol.clone()).unwrap());
        assert!(htlc_pol.entails(control_alice).unwrap());
    }

    #[test]
    fn for_each_key() {
        let liquid_pol = StringPolicy::from_str(
            "or(and(older(4096),thresh(2,pk(A),pk(B),pk(C))),thresh(11,pk(F1),pk(F2),pk(F3),pk(F4),pk(F5),pk(F6),pk(F7),pk(F8),pk(F9),pk(F10),pk(F11),pk(F12),pk(F13),pk(F14)))").unwrap();
        let mut count = 0;
        assert!(liquid_pol.for_each_key(|_| {
            count += 1;
            true
        }));
        assert_eq!(count, 17);
    }
}
