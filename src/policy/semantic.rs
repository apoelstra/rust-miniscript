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

//! Abstract Policies

use core::str::FromStr;
use core::{fmt, str};

use bitcoin::{LockTime, PackedLockTime, Sequence};

use super::concrete::PolicyError;
use super::ENTAILMENT_MAX_TERMINALS;
use crate::prelude::*;
use crate::{errstr, expression, Error, ForEachKey, MiniscriptKey, Translator};

/// Abstract policy which corresponds to the semantics of a Miniscript
/// and which allows complex forms of analysis, e.g. filtering and
/// normalization.
/// Semantic policies store only hashes of keys to ensure that objects
/// representing the same policy are lifted to the same `Semantic`,
/// regardless of their choice of `pk` or `pk_h` nodes.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Policy<Pk: MiniscriptKey> {
    /// Unsatisfiable
    Unsatisfiable,
    /// Trivially satisfiable
    Trivial,
    /// Signature and public key matching a given hash is required
    Key(Pk),
    /// An absolute locktime restriction
    After(PackedLockTime),
    /// A relative locktime restriction
    Older(Sequence),
    /// A SHA256 whose preimage must be provided to satisfy the descriptor
    Sha256(Pk::Sha256),
    /// A SHA256d whose preimage must be provided to satisfy the descriptor
    Hash256(Pk::Hash256),
    /// A RIPEMD160 whose preimage must be provided to satisfy the descriptor
    Ripemd160(Pk::Ripemd160),
    /// A HASH160 whose preimage must be provided to satisfy the descriptor
    Hash160(Pk::Hash160),
    /// A set of descriptors, satisfactions must be provided for `k` of them
    Threshold(usize, Vec<Policy<Pk>>),
}

impl<Pk> Policy<Pk>
where
    Pk: MiniscriptKey,
{
    /// Construct a `Policy::After` from `n`. Helper function equivalent to
    /// `Policy::After(PackedLockTime::from(LockTime::from_consensus(n)))`.
    pub fn after(n: u32) -> Policy<Pk> {
        Policy::After(PackedLockTime::from(LockTime::from_consensus(n)))
    }

    /// Construct a `Policy::Older` from `n`. Helper function equivalent to
    /// `Policy::Older(Sequence::from_consensus(n))`.
    pub fn older(n: u32) -> Policy<Pk> {
        Policy::Older(Sequence::from_consensus(n))
    }
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Policy<Pk> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, mut pred: F) -> bool
    where
        Pk: 'a,
    {
        self.real_for_each_key(&mut pred)
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    fn real_for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, pred: &mut F) -> bool {
        match *self {
            Policy::Unsatisfiable | Policy::Trivial => true,
            Policy::Key(ref pk) => pred(pk),
            Policy::Sha256(..)
            | Policy::Hash256(..)
            | Policy::Ripemd160(..)
            | Policy::Hash160(..)
            | Policy::After(..)
            | Policy::Older(..) => true,
            Policy::Threshold(_, ref subs) => subs.iter().all(|sub| sub.real_for_each_key(&mut *pred)),
        }
    }

    /// Convert a policy using one kind of public key to another
    /// type of public key
    ///
    /// # Example
    ///
    /// ```
    /// use miniscript::{bitcoin::{hashes::hash160, PublicKey}, policy::semantic::Policy, Translator};
    /// use miniscript::translate_hash_fail;
    /// use std::str::FromStr;
    /// use std::collections::HashMap;
    /// let alice_pk = "02c79ef3ede6d14f72a00d0e49b4becfb152197b64c0707425c4f231df29500ee7";
    /// let bob_pk = "03d008a849fbf474bd17e9d2c1a827077a468150e58221582ec3410ab309f5afe4";
    /// let placeholder_policy = Policy::<String>::from_str("and(pk(alice_pk),pk(bob_pk))").unwrap();
    ///
    /// // Information to translator abstract String type keys to concrete bitcoin::PublicKey.
    /// // In practice, wallets would map from String key names to BIP32 keys
    /// struct StrPkTranslator {
    ///     pk_map: HashMap<String, bitcoin::PublicKey>
    /// }
    ///
    /// // If we also wanted to provide mapping of other associated types(sha256, older etc),
    /// // we would use the general Translator Trait.
    /// impl Translator<String, bitcoin::PublicKey, ()> for StrPkTranslator {
    ///     fn pk(&mut self, pk: &String) -> Result<bitcoin::PublicKey, ()> {
    ///         self.pk_map.get(pk).copied().ok_or(()) // Dummy Err
    ///     }
    ///
    ///    // Handy macro for failing if we encounter any other fragment.
    ///    // also see translate_hash_clone! for cloning instead of failing
    ///     translate_hash_fail!(String, bitcoin::PublicKey, ());
    /// }
    ///
    /// let mut pk_map = HashMap::new();
    /// pk_map.insert(String::from("alice_pk"), bitcoin::PublicKey::from_str(alice_pk).unwrap());
    /// pk_map.insert(String::from("bob_pk"), bitcoin::PublicKey::from_str(bob_pk).unwrap());
    /// let mut t = StrPkTranslator { pk_map: pk_map };
    ///
    /// let real_policy = placeholder_policy.translate_pk(&mut t).unwrap();
    ///
    /// let expected_policy = Policy::from_str(&format!("and(pk({}),pk({}))", alice_pk, bob_pk)).unwrap();
    /// assert_eq!(real_policy, expected_policy);
    /// ```
    pub fn translate_pk<Q, E, T>(&self, t: &mut T) -> Result<Policy<Q>, E>
    where
        T: Translator<Pk, Q, E>,
        Q: MiniscriptKey,
    {
        self._translate_pk(t)
    }

    fn _translate_pk<Q, E, T>(&self, t: &mut T) -> Result<Policy<Q>, E>
    where
        T: Translator<Pk, Q, E>,
        Q: MiniscriptKey,
    {
        match *self {
            Policy::Unsatisfiable => Ok(Policy::Unsatisfiable),
            Policy::Trivial => Ok(Policy::Trivial),
            Policy::Key(ref pk) => t.pk(pk).map(Policy::Key),
            Policy::Sha256(ref h) => t.sha256(h).map(Policy::Sha256),
            Policy::Hash256(ref h) => t.hash256(h).map(Policy::Hash256),
            Policy::Ripemd160(ref h) => t.ripemd160(h).map(Policy::Ripemd160),
            Policy::Hash160(ref h) => t.hash160(h).map(Policy::Hash160),
            Policy::After(n) => Ok(Policy::After(n)),
            Policy::Older(n) => Ok(Policy::Older(n)),
            Policy::Threshold(k, ref subs) => {
                let new_subs: Result<Vec<Policy<Q>>, _> =
                    subs.iter().map(|sub| sub._translate_pk(t)).collect();
                new_subs.map(|ok| Policy::Threshold(k, ok))
            }
        }
    }

    /// This function computes whether the current policy entails the second one.
    /// A |- B means every satisfaction of A is also a satisfaction of B.
    /// This implementation will run slow for larger policies but should be sufficient for
    /// most practical policies.

    // This algorithm has a naive implementation. It is possible to optimize this
    // by memoizing and maintaining a hashmap.
    pub fn entails(self, other: Policy<Pk>) -> Result<bool, PolicyError> {
        if self.n_terminals() > ENTAILMENT_MAX_TERMINALS {
            return Err(PolicyError::EntailmentMaxTerminals);
        }
        match (self, other) {
            (Policy::Unsatisfiable, _) => Ok(true),
            (Policy::Trivial, Policy::Trivial) => Ok(true),
            (Policy::Trivial, _) => Ok(false),
            (_, Policy::Unsatisfiable) => Ok(false),
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
                Ok(Policy::entails(a1, b1)? && Policy::entails(a2, b2)?)
            }
        }
    }

    // Helper function to compute the number of constraints in policy.
    fn n_terminals(&self) -> usize {
        match self {
            &Policy::Threshold(_k, ref subs) => subs.iter().map(|sub| sub.n_terminals()).sum(),
            &Policy::Trivial | &Policy::Unsatisfiable => 0,
            _leaf => 1,
        }
    }

    // Helper function to get the first constraint in the policy.
    // Returns the first leaf policy. Used in policy entailment.
    // Assumes that the current policy is normalized.
    fn first_constraint(&self) -> Policy<Pk> {
        debug_assert!(self.clone().normalized() == self.clone());
        match self {
            &Policy::Threshold(_k, ref subs) => subs[0].first_constraint(),
            first => first.clone(),
        }
    }

    // Helper function that takes in witness and its availability,
    // changing it to true or false and returning the resultant normalized
    // policy.
    // Witness is currently encoded as policy. Only accepts leaf fragment and
    // a normalized policy
    pub(crate) fn satisfy_constraint(self, witness: &Policy<Pk>, available: bool) -> Policy<Pk> {
        debug_assert!(self.clone().normalized() == self);
        match *witness {
            // only for internal purposes, safe to use unreachable!
            Policy::Threshold(..) => unreachable!(),
            _ => {}
        };
        let ret = match self {
            Policy::Threshold(k, subs) => {
                let mut ret_subs = vec![];
                for sub in subs {
                    ret_subs.push(sub.satisfy_constraint(witness, available));
                }
                Policy::Threshold(k, ret_subs)
            }
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
            Policy::Threshold(k, ref subs) => {
                if k == subs.len() {
                    write!(f, "and(")?;
                } else if k == 1 {
                    write!(f, "or(")?;
                } else {
                    write!(f, "thresh({},", k)?;
                }
                for (i, sub) in subs.iter().enumerate() {
                    if i == 0 {
                        write!(f, "{}", sub)?;
                    } else {
                        write!(f, ",{}", sub)?;
                    }
                }
                f.write_str(")")
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
            Policy::Threshold(k, ref subs) => {
                if k == subs.len() {
                    write!(f, "and(")?;
                } else if k == 1 {
                    write!(f, "or(")?;
                } else {
                    write!(f, "thresh({},", k)?;
                }
                for (i, sub) in subs.iter().enumerate() {
                    if i == 0 {
                        write!(f, "{}", sub)?;
                    } else {
                        write!(f, ",{}", sub)?;
                    }
                }
                f.write_str(")")
            }
        }
    }
}

impl_from_str!(
    Policy<Pk>,
    type Err = Error;,
    fn from_str(s: &str) -> Result<Policy<Pk>, Error> {
        for ch in s.as_bytes() {
            if *ch < 20 || *ch > 127 {
                return Err(Error::Unprintable(*ch));
            }
        }

        let tree = expression::Tree::from_str(s)?;
        expression::FromTree::from_tree(&tree)
    }
);

serde_string_impl_pk!(Policy, "a miniscript semantic policy");

impl_from_tree!(
    Policy<Pk>,
    fn from_tree(top: &expression::Tree) -> Result<Policy<Pk>, Error> {
        match (top.name, top.args.len()) {
            ("UNSATISFIABLE", 0) => Ok(Policy::Unsatisfiable),
            ("TRIVIAL", 0) => Ok(Policy::Trivial),
            ("pk", 1) => expression::terminal(&top.args[0], |pk| Pk::from_str(pk).map(Policy::Key)),
            ("after", 1) => expression::terminal(&top.args[0], |x| {
                expression::parse_num(x).map(|x| Policy::after(x))
            }),
            ("older", 1) => expression::terminal(&top.args[0], |x| {
                expression::parse_num(x).map(|x| Policy::older(x))
            }),
            ("sha256", 1) => expression::terminal(&top.args[0], |x| {
                Pk::Sha256::from_str(x).map(Policy::Sha256)
            }),
            ("hash256", 1) => expression::terminal(&top.args[0], |x| {
                Pk::Hash256::from_str(x).map(Policy::Hash256)
            }),
            ("ripemd160", 1) => expression::terminal(&top.args[0], |x| {
                Pk::Ripemd160::from_str(x).map(Policy::Ripemd160)
            }),
            ("hash160", 1) => expression::terminal(&top.args[0], |x| {
                Pk::Hash160::from_str(x).map(Policy::Hash160)
            }),
            ("and", nsubs) => {
                if nsubs < 2 {
                    return Err(Error::PolicyError(PolicyError::InsufficientArgsforAnd));
                }
                let mut subs = Vec::with_capacity(nsubs);
                for arg in &top.args {
                    subs.push(Policy::from_tree(arg)?);
                }
                Ok(Policy::Threshold(nsubs, subs))
            }
            ("or", nsubs) => {
                if nsubs < 2 {
                    return Err(Error::PolicyError(PolicyError::InsufficientArgsforOr));
                }
                let mut subs = Vec::with_capacity(nsubs);
                for arg in &top.args {
                    subs.push(Policy::from_tree(arg)?);
                }
                Ok(Policy::Threshold(1, subs))
            }
            ("thresh", nsubs) => {
                if nsubs == 0 || nsubs == 1 {
                    // thresh() and thresh(k) are err
                    return Err(errstr("thresh without args"));
                }
                if !top.args[0].args.is_empty() {
                    return Err(errstr(top.args[0].args[0].name));
                }

                let thresh = expression::parse_num(top.args[0].name)?;

                // thresh(1) and thresh(n) are disallowed in semantic policies
                if thresh <= 1 || thresh >= (nsubs as u32 - 1) {
                    return Err(errstr(
                        "Semantic Policy thresh cannot have k = 1 or k =n, use `and`/`or` instead",
                    ));
                }
                if thresh >= (nsubs as u32) {
                    return Err(errstr(top.args[0].name));
                }

                let mut subs = Vec::with_capacity(top.args.len() - 1);
                for arg in &top.args[1..] {
                    subs.push(Policy::from_tree(arg)?);
                }
                Ok(Policy::Threshold(thresh as usize, subs))
            }
            _ => Err(errstr(top.name)),
        }
    }
);

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// Flatten out trees of `And`s and `Or`s; eliminate `Trivial` and
    /// `Unsatisfiable`s. Does not reorder any branches; use `.sort`.
    pub fn normalized(self) -> Policy<Pk> {
        match self {
            Policy::Threshold(k, subs) => {
                let mut ret_subs = Vec::with_capacity(subs.len());

                let subs: Vec<_> = subs.into_iter().map(|sub| sub.normalized()).collect();
                let trivial_count = subs.iter().filter(|&pol| *pol == Policy::Trivial).count();
                let unsatisfied_count = subs
                    .iter()
                    .filter(|&pol| *pol == Policy::Unsatisfiable)
                    .count();

                let n = subs.len() - unsatisfied_count - trivial_count; // remove all true/false
                let m = k.checked_sub(trivial_count).map_or(0, |x| x); // satisfy all trivial
                                                                       // m == n denotes `and` and m == 1 denotes `or`
                let is_and = m == n;
                let is_or = m == 1;
                for sub in subs {
                    match sub {
                        Policy::Trivial | Policy::Unsatisfiable => {}
                        Policy::Threshold(k, subs) => {
                            match (is_and, is_or) {
                                (true, true) => {
                                    // means m = n = 1, thresh(1,X) type thing.
                                    ret_subs.push(Policy::Threshold(k, subs));
                                }
                                (true, false) if k == subs.len() => ret_subs.extend(subs), // and case
                                (false, true) if k == 1 => ret_subs.extend(subs), // or case
                                _ => ret_subs.push(Policy::Threshold(k, subs)),
                            }
                        }
                        x => ret_subs.push(x),
                    }
                }
                // Now reason about m of n threshold
                if m == 0 {
                    Policy::Trivial
                } else if m > ret_subs.len() {
                    Policy::Unsatisfiable
                } else if ret_subs.len() == 1 {
                    ret_subs.pop().unwrap()
                } else if is_and {
                    Policy::Threshold(ret_subs.len(), ret_subs)
                } else if is_or {
                    Policy::Threshold(1, ret_subs)
                } else {
                    Policy::Threshold(m, ret_subs)
                }
            }
            x => x,
        }
    }

    /// Helper function to detect a true/trivial policy
    /// This function only checks whether the policy is Policy::Trivial
    /// For checking if the normalized form is trivial, the caller
    /// is expected to normalize the policy first.
    pub fn is_trivial(&self) -> bool {
        match *self {
            Policy::Trivial => true,
            _ => false,
        }
    }

    /// Helper function to detect a false/unsatisfiable policy
    /// This function only checks whether the policy is Policy::Unsatisfiable
    /// For checking if the normalized form is unsatisfiable, the caller
    /// is expected to normalize the policy first.
    pub fn is_unsatisfiable(&self) -> bool {
        match *self {
            Policy::Unsatisfiable => true,
            _ => false,
        }
    }

    /// Helper function to do the recursion in `timelocks`.
    fn real_relative_timelocks(&self) -> Vec<u32> {
        match *self {
            Policy::Unsatisfiable
            | Policy::Trivial
            | Policy::Key(..)
            | Policy::Sha256(..)
            | Policy::Hash256(..)
            | Policy::Ripemd160(..)
            | Policy::Hash160(..) => vec![],
            Policy::After(..) => vec![],
            Policy::Older(t) => vec![t.to_consensus_u32()],
            Policy::Threshold(_, ref subs) => subs.iter().fold(vec![], |mut acc, x| {
                acc.extend(x.real_relative_timelocks());
                acc
            }),
        }
    }

    /// Returns a list of all relative timelocks, not including 0,
    /// which appear in the policy
    pub fn relative_timelocks(&self) -> Vec<u32> {
        let mut ret = self.real_relative_timelocks();
        ret.sort_unstable();
        ret.dedup();
        ret
    }

    /// Helper function for recursion in `absolute timelocks`
    fn real_absolute_timelocks(&self) -> Vec<u32> {
        match *self {
            Policy::Unsatisfiable
            | Policy::Trivial
            | Policy::Key(..)
            | Policy::Sha256(..)
            | Policy::Hash256(..)
            | Policy::Ripemd160(..)
            | Policy::Hash160(..) => vec![],
            Policy::Older(..) => vec![],
            Policy::After(t) => vec![t.0],
            Policy::Threshold(_, ref subs) => subs.iter().fold(vec![], |mut acc, x| {
                acc.extend(x.real_absolute_timelocks());
                acc
            }),
        }
    }

    /// Returns a list of all absolute timelocks, not including 0,
    /// which appear in the policy
    pub fn absolute_timelocks(&self) -> Vec<u32> {
        let mut ret = self.real_absolute_timelocks();
        ret.sort_unstable();
        ret.dedup();
        ret
    }

    /// Filter a policy by eliminating relative timelock constraints
    /// that are not satisfied at the given `age`.
    pub fn at_age(mut self, age: Sequence) -> Policy<Pk> {
        self = match self {
            Policy::Older(t) => {
                if t.is_height_locked() && age.is_time_locked()
                    || t.is_time_locked() && age.is_height_locked()
                {
                    Policy::Unsatisfiable
                } else if t.to_consensus_u32() > age.to_consensus_u32() {
                    Policy::Unsatisfiable
                } else {
                    Policy::Older(t)
                }
            }
            Policy::Threshold(k, subs) => {
                Policy::Threshold(k, subs.into_iter().map(|sub| sub.at_age(age)).collect())
            }
            x => x,
        };
        self.normalized()
    }

    /// Filter a policy by eliminating absolute timelock constraints
    /// that are not satisfied at the given `n` (`n OP_CHECKLOCKTIMEVERIFY`).
    pub fn at_lock_time(mut self, n: LockTime) -> Policy<Pk> {
        use LockTime::*;

        self = match self {
            Policy::After(t) => {
                let t = LockTime::from(t);
                let is_satisfied_by = match (t, n) {
                    (Blocks(t), Blocks(n)) => t <= n,
                    (Seconds(t), Seconds(n)) => t <= n,
                    _ => false,
                };
                if !is_satisfied_by {
                    Policy::Unsatisfiable
                } else {
                    Policy::After(t.into())
                }
            }
            Policy::Threshold(k, subs) => {
                Policy::Threshold(k, subs.into_iter().map(|sub| sub.at_lock_time(n)).collect())
            }
            x => x,
        };
        self.normalized()
    }

    /// Count the number of public keys and keyhashes referenced in a policy.
    /// Duplicate keys will be double-counted.
    pub fn n_keys(&self) -> usize {
        match *self {
            Policy::Unsatisfiable | Policy::Trivial => 0,
            Policy::Key(..) => 1,
            Policy::After(..)
            | Policy::Older(..)
            | Policy::Sha256(..)
            | Policy::Hash256(..)
            | Policy::Ripemd160(..)
            | Policy::Hash160(..) => 0,
            Policy::Threshold(_, ref subs) => subs.iter().map(|sub| sub.n_keys()).sum::<usize>(),
        }
    }

    /// Count the minimum number of public keys for which signatures
    /// could be used to satisfy the policy.
    /// Returns `None` if the policy is not satisfiable.
    pub fn minimum_n_keys(&self) -> Option<usize> {
        match *self {
            Policy::Unsatisfiable => None,
            Policy::Trivial => Some(0),
            Policy::Key(..) => Some(1),
            Policy::After(..)
            | Policy::Older(..)
            | Policy::Sha256(..)
            | Policy::Hash256(..)
            | Policy::Ripemd160(..)
            | Policy::Hash160(..) => Some(0),
            Policy::Threshold(k, ref subs) => {
                let mut sublens: Vec<usize> =
                    subs.iter().filter_map(Policy::minimum_n_keys).collect();
                if sublens.len() < k {
                    // Not enough branches are satisfiable
                    None
                } else {
                    sublens.sort_unstable();
                    Some(sublens[0..k].iter().cloned().sum::<usize>())
                }
            }
        }
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// "Sort" a policy to bring it into a canonical form to allow comparisons.
    /// Does **not** allow policies to be compared for functional equivalence;
    /// in general this appears to require Gröbner basis techniques that are not
    /// implemented.
    pub fn sorted(self) -> Policy<Pk> {
        match self {
            Policy::Threshold(k, subs) => {
                let mut new_subs: Vec<_> = subs.into_iter().map(Policy::sorted).collect();
                new_subs.sort();
                Policy::Threshold(k, new_subs)
            }
            x => x,
        }
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

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
        assert_eq!(policy.clone().at_age(Sequence::ZERO), policy.clone());
        assert_eq!(
            policy.clone().at_age(Sequence::from_height(10000)),
            policy.clone()
        );
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), Some(1));

        let policy = StringPolicy::from_str("older(1000)").unwrap();
        assert_eq!(policy, Policy::Older(Sequence::from_height(1000)));
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.relative_timelocks(), vec![1000]);
        assert_eq!(policy.clone().at_age(Sequence::ZERO), Policy::Unsatisfiable);
        assert_eq!(
            policy.clone().at_age(Sequence::from_height(999)),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy.clone().at_age(Sequence::from_height(1000)),
            policy.clone()
        );
        assert_eq!(
            policy.clone().at_age(Sequence::from_height(10000)),
            policy.clone()
        );
        assert_eq!(policy.n_keys(), 0);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        let policy = StringPolicy::from_str("or(pk(),older(1000))").unwrap();
        assert_eq!(
            policy,
            Policy::Threshold(
                1,
                vec![
                    Policy::Key("".to_owned()),
                    Policy::Older(Sequence::from_height(1000)),
                ]
            )
        );
        assert_eq!(policy.relative_timelocks(), vec![1000]);
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(
            policy.clone().at_age(Sequence::ZERO),
            Policy::Key("".to_owned())
        );
        assert_eq!(
            policy.clone().at_age(Sequence::from_height(999)),
            Policy::Key("".to_owned())
        );
        assert_eq!(
            policy.clone().at_age(Sequence::from_height(1000)),
            policy.clone().normalized()
        );
        assert_eq!(
            policy.clone().at_age(Sequence::from_height(10000)),
            policy.clone().normalized()
        );
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        let policy = StringPolicy::from_str("or(pk(),UNSATISFIABLE)").unwrap();
        assert_eq!(
            policy,
            Policy::Threshold(1, vec![Policy::Key("".to_owned()), Policy::Unsatisfiable,])
        );
        assert_eq!(policy.relative_timelocks(), vec![]);
        assert_eq!(policy.absolute_timelocks(), vec![]);
        assert_eq!(policy.n_keys(), 1);
        assert_eq!(policy.minimum_n_keys(), Some(1));

        let policy = StringPolicy::from_str("and(pk(),UNSATISFIABLE)").unwrap();
        assert_eq!(
            policy,
            Policy::Threshold(2, vec![Policy::Key("".to_owned()), Policy::Unsatisfiable,])
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
            Policy::Threshold(
                2,
                vec![
                    Policy::Older(Sequence::from_height(1000)),
                    Policy::Older(Sequence::from_height(10000)),
                    Policy::Older(Sequence::from_height(1000)),
                    Policy::Older(Sequence::from_height(2000)),
                    Policy::Older(Sequence::from_height(2000)),
                ]
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
            Policy::Threshold(
                2,
                vec![
                    Policy::Older(Sequence::from_height(1000)),
                    Policy::Older(Sequence::from_height(10000)),
                    Policy::Older(Sequence::from_height(1000)),
                    Policy::Unsatisfiable,
                    Policy::Unsatisfiable,
                ]
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
        assert_eq!(policy, Policy::after(1000));
        assert_eq!(policy.absolute_timelocks(), vec![1000]);
        assert_eq!(policy.relative_timelocks(), vec![]);
        assert_eq!(
            policy.clone().at_lock_time(LockTime::ZERO),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_height(999).expect("valid block height")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_height(1000).expect("valid block height")),
            policy.clone()
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_height(10000).expect("valid block height")),
            policy.clone()
        );
        // Pass a UNIX timestamp to at_lock_time while policy uses a block height.
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_time(500_000_001).expect("valid timestamp")),
            Policy::Unsatisfiable
        );
        assert_eq!(policy.n_keys(), 0);
        assert_eq!(policy.minimum_n_keys(), Some(0));

        // UNIX timestamp of 10 seconds after the epoch.
        let policy = StringPolicy::from_str("after(500000010)").unwrap();
        assert_eq!(policy, Policy::after(500_000_010));
        assert_eq!(policy.absolute_timelocks(), vec![500_000_010]);
        assert_eq!(policy.relative_timelocks(), vec![]);
        // Pass a block height to at_lock_time while policy uses a UNIX timestapm.
        assert_eq!(
            policy.clone().at_lock_time(LockTime::ZERO),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_height(999).expect("valid block height")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_height(1000).expect("valid block height")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_height(10000).expect("valid block height")),
            Policy::Unsatisfiable
        );
        // And now pass a UNIX timestamp to at_lock_time while policy also uses a timestamp.
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_time(500_000_000).expect("valid timestamp")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_time(500_000_001).expect("valid timestamp")),
            Policy::Unsatisfiable
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_time(500_000_010).expect("valid timestamp")),
            policy.clone()
        );
        assert_eq!(
            policy
                .clone()
                .at_lock_time(LockTime::from_time(500_000_012).expect("valid timestamp")),
            policy.clone()
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
        let new_liquid_pol = Policy::Threshold(1, vec![liquid_pol.clone(), master_key]);

        assert!(liquid_pol.clone().entails(new_liquid_pol.clone()).unwrap());
        assert!(!new_liquid_pol.entails(liquid_pol.clone()).unwrap());

        // test liquid backup policy before the emergency timeout
        let backup_policy = StringPolicy::from_str("thresh(2,pk(A),pk(B),pk(C))").unwrap();
        assert!(!backup_policy
            .clone()
            .entails(liquid_pol.clone().at_age(Sequence::from_height(4095)))
            .unwrap());

        // Finally test both spending paths
        let fed_pol = StringPolicy::from_str("thresh(11,pk(F1),pk(F2),pk(F3),pk(F4),pk(F5),pk(F6),pk(F7),pk(F8),pk(F9),pk(F10),pk(F11),pk(F12),pk(F13),pk(F14))").unwrap();
        let backup_policy_after_expiry =
            StringPolicy::from_str("and(older(4096),thresh(2,pk(A),pk(B),pk(C)))").unwrap();
        assert!(fed_pol.entails(liquid_pol.clone()).unwrap());
        assert!(backup_policy_after_expiry
            .entails(liquid_pol.clone())
            .unwrap());
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
        assert!(liquid_pol.for_each_key(|_| { count +=1; true }));
        assert_eq!(count, 17);
    }
}
