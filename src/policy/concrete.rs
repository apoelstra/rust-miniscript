// SPDX-License-Identifier: CC0-1.0

//! Concrete Policies
//!

use core::{fmt, str};
#[cfg(feature = "std")]
use std::error;

use bitcoin::absolute;
#[cfg(feature = "compiler")]
use {
    crate::descriptor::TapTree,
    crate::miniscript::ScriptContext,
    crate::policy::compiler::{self, CompilerError, OrdF64},
    crate::Descriptor,
    crate::Miniscript,
    crate::Tap,
    core::cmp::Reverse,
};

use crate::expression::{self, FromTree};
use crate::iter::{Tree, TreeLike};
use crate::miniscript::types::extra_props::TimelockInfo;
use crate::prelude::*;
use crate::sync::Arc;
#[cfg(all(doc, not(feature = "compiler")))]
use crate::Descriptor;
use crate::{
    AbsLockTime, Error, ForEachKey, FromStrKey, MiniscriptKey, RelLockTime, Threshold, Translator,
};

/// Maximum TapLeafs allowed in a compiled TapTree
#[cfg(feature = "compiler")]
const MAX_COMPILATION_LEAVES: usize = 1024;

/// Concrete policy which corresponds directly to a miniscript structure,
/// and whose disjunctions are annotated with satisfaction probabilities
/// to assist the compiler.
// Currently the vectors in And/Or are limited to two elements, this is a general miniscript thing
// not specific to rust-miniscript. Eventually we would like to extend these to be n-ary, but first
// we need to decide on a game plan for how to efficiently compile n-ary disjunctions
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Policy<Pk: MiniscriptKey> {
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
    And(Vec<Arc<Policy<Pk>>>),
    /// A list of sub-policies, one of which must be satisfied, along with
    /// relative probabilities for each one.
    Or(Vec<(usize, Arc<Policy<Pk>>)>),
    /// A set of descriptors, satisfactions must be provided for `k` of them.
    Thresh(Threshold<Arc<Policy<Pk>>, 0>),
}

/// Detailed error type for concrete policies.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum PolicyError {
    /// `And` fragments only support two args.
    NonBinaryArgAnd,
    /// `Or` fragments only support two args.
    NonBinaryArgOr,
    /// Cannot lift policies that have a combination of height and timelocks.
    HeightTimelockCombination,
    /// Duplicate Public Keys.
    DuplicatePubKeys,
}

/// Descriptor context for [`Policy`] compilation into a [`Descriptor`].
pub enum DescriptorCtx<Pk> {
    /// See docs for [`Descriptor::Bare`].
    Bare,
    /// See docs for [`Descriptor::Sh`].
    Sh,
    /// See docs for [`Descriptor::Wsh`].
    Wsh,
    /// See docs for [`Descriptor::Wsh`].
    ShWsh,
    /// [`Descriptor::Tr`] where the `Option<Pk>` corresponds to the internal key if no
    /// internal key can be inferred from the given policy.
    Tr(Option<Pk>),
}

impl fmt::Display for PolicyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            PolicyError::NonBinaryArgAnd => {
                f.write_str("And policy fragment must take 2 arguments")
            }
            PolicyError::NonBinaryArgOr => f.write_str("Or policy fragment must take 2 arguments"),
            PolicyError::HeightTimelockCombination => {
                f.write_str("Cannot lift policies that have a heightlock and timelock combination")
            }
            PolicyError::DuplicatePubKeys => f.write_str("Policy contains duplicate keys"),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for PolicyError {
    fn cause(&self) -> Option<&dyn error::Error> {
        use self::PolicyError::*;

        match self {
            NonBinaryArgAnd | NonBinaryArgOr | HeightTimelockCombination | DuplicatePubKeys => None,
        }
    }
}

#[cfg(feature = "compiler")]
struct TapleafProbabilityIter<'p, Pk: MiniscriptKey> {
    stack: Vec<(f64, &'p Policy<Pk>)>,
}

#[cfg(feature = "compiler")]
impl<'p, Pk: MiniscriptKey> Iterator for TapleafProbabilityIter<'p, Pk> {
    type Item = (f64, &'p Policy<Pk>);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (top_prob, top) = self.stack.pop()?;

            match top {
                Policy::Or(ref subs) => {
                    let total_sub_prob = subs.iter().map(|prob_sub| prob_sub.0).sum::<usize>();
                    for (sub_prob, sub) in subs.iter().rev() {
                        let ratio = *sub_prob as f64 / total_sub_prob as f64;
                        self.stack.push((top_prob * ratio, sub));
                    }
                }
                Policy::Thresh(ref thresh) if thresh.is_or() => {
                    let n64 = thresh.n() as f64;
                    for sub in thresh.iter().rev() {
                        self.stack.push((top_prob / n64, sub));
                    }
                }
                _ => return Some((top_prob, top)),
            }
        }
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// Flattens the [`Policy`] tree structure into an iterator of tuples `(leaf script, leaf probability)`
    /// with leaf probabilities corresponding to odds for each sub-branch in the policy.
    /// We calculate the probability of selecting the sub-branch at every level and calculate the
    /// leaf probabilities as the probability of traversing through required branches to reach the
    /// leaf node, i.e. multiplication of the respective probabilities.
    ///
    /// For example, the policy tree:       OR
    ///                                   /   \
    ///                                  2     1            odds
    ///                                /        \
    ///                               A         OR
    ///                                        /  \
    ///                                       3    1        odds
    ///                                     /       \
    ///                                    B         C
    ///
    /// gives the vector [(2/3, A), (1/3 * 3/4, B), (1/3 * 1/4, C)].
    ///
    /// ## Constraints
    ///
    /// Since this splitting might lead to exponential blow-up, we constrain the number of
    /// leaf-nodes to [`MAX_COMPILATION_LEAVES`].
    #[cfg(feature = "compiler")]
    fn tapleaf_probability_iter(&self) -> TapleafProbabilityIter<Pk> {
        TapleafProbabilityIter { stack: vec![(1.0, self)] }
    }

    /// Extracts the internal_key from this policy tree.
    #[cfg(feature = "compiler")]
    fn extract_key(self, unspendable_key: Option<Pk>) -> Result<(Pk, Policy<Pk>), CompilerError> {
        let internal_key = self
            .tapleaf_probability_iter()
            .filter_map(|(prob, ref pol)| match pol {
                Policy::Key(pk) => Some((OrdF64(prob), pk)),
                _ => None,
            })
            .max_by_key(|(prob, _)| *prob)
            .map(|(_, pk)| pk.clone());

        match (internal_key, unspendable_key) {
            (Some(ref key), _) => Ok((key.clone(), self.translate_unsatisfiable_pk(key))),
            (_, Some(key)) => Ok((key, self)),
            _ => Err(CompilerError::NoInternalKey),
        }
    }

    /// Compiles the [`Policy`] into a [`Descriptor::Tr`].
    ///
    /// ### TapTree compilation
    ///
    /// The policy tree constructed by root-level disjunctions over [`Policy::Or`] and
    /// [`Policy::Thresh`](1, ..) which is flattened into a vector (with respective
    /// probabilities derived from odds) of policies.
    ///
    /// For example, the policy `thresh(1,or(pk(A),pk(B)),and(or(pk(C),pk(D)),pk(E)))` gives the
    /// vector `[pk(A),pk(B),and(or(pk(C),pk(D)),pk(E)))]`. Each policy in the vector is compiled
    /// into the respective miniscripts. A Huffman Tree is created from this vector which optimizes
    /// over the probabilitity of satisfaction for the respective branch in the TapTree.
    ///
    /// Refer to [this link](https://gist.github.com/SarcasticNastik/9e70b2b43375aab3e78c51e09c288c89)
    /// or [doc/Tr compiler.pdf] in the root of the repository to understand why such compilation
    /// is also *cost-efficient*.
    // TODO: We might require other compile errors for Taproot.
    #[cfg(feature = "compiler")]
    pub fn compile_tr(&self, unspendable_key: Option<Pk>) -> Result<Descriptor<Pk>, CompilerError> {
        self.is_valid().map_err(CompilerError::PolicyError)?;
        match self.is_safe_nonmalleable() {
            (false, _) => Err(CompilerError::TopLevelNonSafe),
            (_, false) => Err(CompilerError::ImpossibleNonMalleableCompilation),
            _ => {
                let (internal_key, policy) = self.clone().extract_key(unspendable_key)?;
                policy.check_num_tapleaves()?;
                let tree = Descriptor::new_tr(
                    internal_key,
                    match policy {
                        Policy::Trivial => None,
                        policy => {
                            let mut leaf_compilations: Vec<(OrdF64, Miniscript<Pk, Tap>)> = vec![];
                            for (prob, pol) in policy.tapleaf_probability_iter() {
                                // policy corresponding to the key (replaced by unsatisfiable) is skipped
                                if *pol == Policy::Unsatisfiable {
                                    continue;
                                }
                                let compilation = compiler::best_compilation::<Pk, Tap>(pol)?;
                                compilation
                                    .sanity_check()
                                    .expect("compiler produces sane output");
                                leaf_compilations.push((OrdF64(prob), compilation));
                            }
                            if !leaf_compilations.is_empty() {
                                let tap_tree = with_huffman_tree::<Pk>(leaf_compilations);
                                Some(tap_tree)
                            } else {
                                // no policies remaining once the extracted key is skipped
                                None
                            }
                        }
                    },
                )
                .expect("compiler produces sane output");
                Ok(tree)
            }
        }
    }

    /// Compiles the [`Policy`] into a [`Descriptor::Tr`].
    ///
    /// ### TapTree compilation
    ///
    /// The policy tree constructed by root-level disjunctions over [`Policy::Or`] and
    /// [`Policy::Thresh`](k, ..n..) which is flattened into a vector (with respective
    /// probabilities derived from odds) of policies. For example, the policy
    /// `thresh(1,or(pk(A),pk(B)),and(or(pk(C),pk(D)),pk(E)))` gives the vector
    /// `[pk(A),pk(B),and(or(pk(C),pk(D)),pk(E)))]`.
    ///
    /// ### Policy enumeration
    ///
    /// Generates a root-level disjunctive tree over the given policy tree.
    ///
    /// Uses a fixed-point algorithm to enumerate the disjunctions until exhaustive root-level
    /// enumeration or limits exceed. For a given [`Policy`], we maintain an [ordered
    /// set](`BTreeSet`) of `(prob, policy)` (ordered by probability) to maintain the list of
    /// enumerated sub-policies whose disjunction is isomorphic to initial policy (*invariant*).
    #[cfg(feature = "compiler")]
    pub fn compile_tr_private_experimental(
        &self,
        unspendable_key: Option<Pk>,
    ) -> Result<Descriptor<Pk>, Error> {
        self.is_valid().map_err(Error::ConcretePolicy)?;
        match self.is_safe_nonmalleable() {
            (false, _) => Err(Error::from(CompilerError::TopLevelNonSafe)),
            (_, false) => Err(Error::from(CompilerError::ImpossibleNonMalleableCompilation)),
            _ => {
                let (internal_key, policy) = self.clone().extract_key(unspendable_key)?;
                let tree = Descriptor::new_tr(
                    internal_key,
                    match policy {
                        Policy::Trivial => None,
                        policy => {
                            let leaf_compilations: Vec<_> = policy
                                .enumerate_policy_tree(1.0)
                                .into_iter()
                                .filter(|x| x.1 != Arc::new(Policy::Unsatisfiable))
                                .map(|(prob, pol)| {
                                    (
                                        OrdF64(prob),
                                        compiler::best_compilation(pol.as_ref()).unwrap(),
                                    )
                                })
                                .collect();

                            if !leaf_compilations.is_empty() {
                                let tap_tree = with_huffman_tree::<Pk>(leaf_compilations);
                                Some(tap_tree)
                            } else {
                                // no policies remaining once the extracted key is skipped
                                None
                            }
                        }
                    },
                )?;
                Ok(tree)
            }
        }
    }

    /// Compiles the [`Policy`] into `desc_ctx` [`Descriptor`]
    ///
    /// In case of [`DescriptorCtx::Tr`], `internal_key` is used for the taproot compilation when
    /// no public key can be inferred from the given policy.
    ///
    /// # NOTE:
    ///
    /// It is **not recommended** to use policy as a stable identifier for a miniscript. You should
    /// use the policy compiler once, and then use the miniscript output as a stable identifier. See
    /// the compiler document in [`doc/compiler.md`] for more details.
    #[cfg(feature = "compiler")]
    pub fn compile_to_descriptor<Ctx: ScriptContext>(
        &self,
        desc_ctx: DescriptorCtx<Pk>,
    ) -> Result<Descriptor<Pk>, Error> {
        self.is_valid().map_err(Error::ConcretePolicy)?;
        match self.is_safe_nonmalleable() {
            (false, _) => Err(Error::from(CompilerError::TopLevelNonSafe)),
            (_, false) => Err(Error::from(CompilerError::ImpossibleNonMalleableCompilation)),
            _ => match desc_ctx {
                DescriptorCtx::Bare => Descriptor::new_bare(compiler::best_compilation(self)?),
                DescriptorCtx::Sh => Descriptor::new_sh(compiler::best_compilation(self)?),
                DescriptorCtx::Wsh => Descriptor::new_wsh(compiler::best_compilation(self)?),
                DescriptorCtx::ShWsh => Descriptor::new_sh_wsh(compiler::best_compilation(self)?),
                DescriptorCtx::Tr(unspendable_key) => self
                    .compile_tr(unspendable_key)
                    .map_err(Error::CompilerError),
            },
        }
    }

    /// Compiles the descriptor into an optimized `Miniscript` representation.
    ///
    /// # NOTE:
    ///
    /// It is **not recommended** to use policy as a stable identifier for a miniscript. You should
    /// use the policy compiler once, and then use the miniscript output as a stable identifier. See
    /// the compiler document in doc/compiler.md for more details.
    #[cfg(feature = "compiler")]
    pub fn compile<Ctx: ScriptContext>(&self) -> Result<Miniscript<Pk, Ctx>, CompilerError> {
        self.is_valid()?;
        match self.is_safe_nonmalleable() {
            (false, _) => Err(CompilerError::TopLevelNonSafe),
            (_, false) => Err(CompilerError::ImpossibleNonMalleableCompilation),
            _ => compiler::best_compilation(self),
        }
    }
}

#[cfg(feature = "compiler")]
impl<Pk: MiniscriptKey> Policy<Pk> {
    /// Returns a vector of policies whose disjunction is isomorphic to the initial one.
    ///
    /// This function is supposed to incrementally expand i.e. represent the policy as
    /// disjunction over sub-policies output by it. The probability calculations are similar
    /// to [`Policy::tapleaf_probability_iter`].
    #[cfg(feature = "compiler")]
    fn enumerate_pol(&self, prob: f64) -> Vec<(f64, Arc<Self>)> {
        match self {
            Policy::Or(subs) => {
                let total_odds = subs.iter().fold(0, |acc, x| acc + x.0);
                subs.iter()
                    .map(|(odds, pol)| (prob * *odds as f64 / total_odds as f64, pol.clone()))
                    .collect::<Vec<_>>()
            }
            Policy::Thresh(ref thresh) if thresh.is_or() => {
                let total_odds = thresh.n();
                thresh
                    .iter()
                    .map(|pol| (prob / total_odds as f64, pol.clone()))
                    .collect::<Vec<_>>()
            }
            Policy::Thresh(ref thresh) if !thresh.is_and() => generate_combination(thresh, prob),
            pol => vec![(prob, Arc::new(pol.clone()))],
        }
    }

    /// Generates a root-level disjunctive tree over the given policy tree.
    ///
    /// Uses a fixed-point algorithm to enumerate the disjunctions until exhaustive root-level
    /// enumeration or limits exceed. For a given [`Policy`], we maintain an [ordered
    /// set](`BTreeSet`) of `(prob, policy)` (ordered by probability) to maintain the list of
    /// enumerated sub-policies whose disjunction is isomorphic to initial policy (*invariant*).
    #[cfg(feature = "compiler")]
    fn enumerate_policy_tree(self, prob: f64) -> Vec<(f64, Arc<Self>)> {
        let mut tapleaf_prob_vec = BTreeSet::<(Reverse<OrdF64>, Arc<Self>)>::new();
        // Store probability corresponding to policy in the enumerated tree. This is required since
        // owing to the current [policy element enumeration algorithm][`Policy::enumerate_pol`],
        // two passes of the algorithm might result in same sub-policy showing up. Currently, we
        // merge the nodes by adding up the corresponding probabilities for the same policy.
        let mut pol_prob_map = BTreeMap::<Arc<Self>, OrdF64>::new();

        let arc_self = Arc::new(self);
        tapleaf_prob_vec.insert((Reverse(OrdF64(prob)), Arc::clone(&arc_self)));
        pol_prob_map.insert(Arc::clone(&arc_self), OrdF64(prob));

        // Since we know that policy enumeration *must* result in increase in total number of nodes,
        // we can maintain the length of the ordered set to check if the
        // [enumeration pass][`Policy::enumerate_pol`] results in further policy split or not.
        let mut prev_len = 0usize;
        // This is required since we merge some corresponding policy nodes, so we can explicitly
        // store the variables
        let mut enum_len = tapleaf_prob_vec.len();

        let mut ret: Vec<(f64, Arc<Self>)> = vec![];

        // Stopping condition: When NONE of the inputs can be further enumerated.
        'outer: loop {
            //--- FIND a plausible node ---
            let mut prob: Reverse<OrdF64> = Reverse(OrdF64(0.0));
            let mut curr_policy: Arc<Self> = Arc::new(Policy::Unsatisfiable);
            let mut curr_pol_replace_vec: Vec<(f64, Arc<Self>)> = vec![];
            let mut no_more_enum = false;

            // The nodes which can't be enumerated further are directly appended to ret and removed
            // from the ordered set.
            let mut to_del: Vec<(f64, Arc<Self>)> = vec![];
            'inner: for (i, (p, pol)) in tapleaf_prob_vec.iter().enumerate() {
                curr_pol_replace_vec = pol.enumerate_pol(p.0 .0);
                enum_len += curr_pol_replace_vec.len() - 1; // A disjunctive node should have seperated this into more nodes
                assert!(prev_len <= enum_len);

                if prev_len < enum_len {
                    // Plausible node found
                    prob = *p;
                    curr_policy = Arc::clone(pol);
                    break 'inner;
                } else if i == tapleaf_prob_vec.len() - 1 {
                    // No enumerable node found i.e. STOP
                    // Move all the elements to final return set
                    no_more_enum = true;
                } else {
                    // Either node is enumerable, or we have
                    // Mark all non-enumerable nodes to remove,
                    // if not returning value in the current iteration.
                    to_del.push((p.0 .0, Arc::clone(pol)));
                }
            }

            // --- Sanity Checks ---
            if enum_len > MAX_COMPILATION_LEAVES || no_more_enum {
                for (p, pol) in tapleaf_prob_vec.into_iter() {
                    ret.push((p.0 .0, pol));
                }
                break 'outer;
            }

            // If total number of nodes are in limits, we remove the current node and replace it
            // with children nodes

            // Remove current node
            assert!(tapleaf_prob_vec.remove(&(prob, curr_policy.clone())));

            // OPTIMIZATION - Move marked nodes into final vector
            for (p, pol) in to_del {
                assert!(tapleaf_prob_vec.remove(&(Reverse(OrdF64(p)), pol.clone())));
                ret.push((p, pol.clone()));
            }

            // Append node if not previously exists, else update the respective probability
            for (p, policy) in curr_pol_replace_vec {
                match pol_prob_map.get(&policy) {
                    Some(prev_prob) => {
                        assert!(tapleaf_prob_vec.remove(&(Reverse(*prev_prob), policy.clone())));
                        tapleaf_prob_vec.insert((Reverse(OrdF64(prev_prob.0 + p)), policy.clone()));
                        pol_prob_map.insert(policy.clone(), OrdF64(prev_prob.0 + p));
                    }
                    None => {
                        tapleaf_prob_vec.insert((Reverse(OrdF64(p)), policy.clone()));
                        pol_prob_map.insert(policy.clone(), OrdF64(p));
                    }
                }
            }
            // --- Update --- total sub-policies count (considering no merging of nodes)
            prev_len = enum_len;
        }

        ret
    }
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
    /// For example usage please see [`crate::policy::semantic::Policy::translate_pk`].
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
                And(ref subs) => And((0..subs.len()).map(|_| translated.pop().unwrap()).collect()),
                Or(ref subs) => Or(subs
                    .iter()
                    .map(|(prob, _)| (*prob, translated.pop().unwrap()))
                    .collect()),
                Thresh(ref thresh) => Thresh(thresh.map_ref(|_| translated.pop().unwrap())),
            };
            translated.push(Arc::new(new_policy));
        }
        // Unwrap is ok because we know we processed at least one node.
        let root_node = translated.pop().unwrap();
        // Unwrap is ok because we know `root_node` is the only strong reference.
        Ok(Arc::try_unwrap(root_node).unwrap())
    }

    /// Translates `Concrete::Key(key)` to `Concrete::Unsatisfiable` when extracting `TapKey`.
    pub fn translate_unsatisfiable_pk(self, key: &Pk) -> Policy<Pk> {
        use Policy::*;

        let mut translated = vec![];
        for data in Arc::new(self).rtl_post_order_iter() {
            let new_policy = match data.node.as_ref() {
                Policy::Key(ref k) if k.clone() == *key => Some(Policy::Unsatisfiable),
                And(ref subs) => {
                    Some(And((0..subs.len()).map(|_| translated.pop().unwrap()).collect()))
                }
                Or(ref subs) => Some(Or(subs
                    .iter()
                    .map(|(prob, _)| (*prob, translated.pop().unwrap()))
                    .collect())),
                Thresh(ref thresh) => Some(Thresh(thresh.map_ref(|_| translated.pop().unwrap()))),
                _ => None,
            };
            match new_policy {
                Some(new_policy) => translated.push(Arc::new(new_policy)),
                None => translated.push(Arc::clone(data.node)),
            }
        }
        // Ok to unwrap because we know we processed at least one node.
        let root_node = translated.pop().unwrap();
        // Ok to unwrap because we know `root_node` is the only strong reference.
        Arc::try_unwrap(root_node).unwrap()
    }

    /// Gets all keys in the policy.
    pub fn keys(&self) -> Vec<&Pk> {
        self.pre_order_iter()
            .filter_map(|policy| match policy {
                Policy::Key(ref pk) => Some(pk),
                _ => None,
            })
            .collect()
    }

    /// Gets the number of [TapLeaf](`TapTree::Leaf`)s considering exhaustive root-level [`Policy::Or`]
    /// and [`Policy::Thresh`] disjunctions for the `TapTree`.
    #[cfg(feature = "compiler")]
    fn num_tap_leaves(&self) -> usize { self.tapleaf_probability_iter().count() }

    /// Does checks on the number of `TapLeaf`s.
    #[cfg(feature = "compiler")]
    fn check_num_tapleaves(&self) -> Result<(), CompilerError> {
        let n = self.num_tap_leaves();
        if n > MAX_COMPILATION_LEAVES {
            return Err(CompilerError::TooManyTapleaves { n, max: MAX_COMPILATION_LEAVES });
        }
        Ok(())
    }

    /// Checks whether the policy contains duplicate public keys.
    pub fn check_duplicate_keys(&self) -> Result<(), PolicyError> {
        let pks = self.keys();
        let pks_len = pks.len();
        let unique_pks_len = pks.into_iter().collect::<BTreeSet<_>>().len();

        if pks_len > unique_pks_len {
            Err(PolicyError::DuplicatePubKeys)
        } else {
            Ok(())
        }
    }

    /// Checks whether the given concrete policy contains a combination of
    /// timelocks and heightlocks.
    ///
    /// # Returns
    ///
    /// Returns an error if there is at least one satisfaction that contains
    /// a combination of heightlock and timelock.
    pub fn check_timelocks(&self) -> Result<(), PolicyError> {
        let aggregated_timelock_info = self.timelock_info();
        if aggregated_timelock_info.contains_combination {
            Err(PolicyError::HeightTimelockCombination)
        } else {
            Ok(())
        }
    }

    /// Processes `Policy` using `post_order_iter`, creates a `TimelockInfo` for each `Nullary` node
    /// and combines them together for `Nary` nodes.
    ///
    /// # Returns
    ///
    /// A single `TimelockInfo` that is the combination of all others after processing each node.
    fn timelock_info(&self) -> TimelockInfo {
        use Policy::*;

        let mut infos = vec![];
        for data in self.rtl_post_order_iter() {
            let info = match data.node {
                Policy::After(ref t) => TimelockInfo {
                    csv_with_height: false,
                    csv_with_time: false,
                    cltv_with_height: absolute::LockTime::from(*t).is_block_height(),
                    cltv_with_time: absolute::LockTime::from(*t).is_block_time(),
                    contains_combination: false,
                },
                Policy::Older(ref t) => TimelockInfo {
                    csv_with_height: t.is_height_locked(),
                    csv_with_time: t.is_time_locked(),
                    cltv_with_height: false,
                    cltv_with_time: false,
                    contains_combination: false,
                },
                And(ref subs) => {
                    let iter = (0..subs.len()).map(|_| infos.pop().unwrap());
                    TimelockInfo::combine_threshold(subs.len(), iter)
                }
                Or(ref subs) => {
                    let iter = (0..subs.len()).map(|_| infos.pop().unwrap());
                    TimelockInfo::combine_threshold(1, iter)
                }
                Thresh(ref thresh) => {
                    let iter = (0..thresh.n()).map(|_| infos.pop().unwrap());
                    TimelockInfo::combine_threshold(thresh.k(), iter)
                }
                _ => TimelockInfo::default(),
            };
            infos.push(info);
        }
        // Ok to unwrap, we had to have visited at least one node.
        infos.pop().unwrap()
    }

    /// This returns whether the given policy is valid or not. It maybe possible that the policy
    /// contains Non-two argument `and`, `or` or a `0` arg thresh.
    /// Validity condition also checks whether there is a possible satisfaction
    /// combination of timelocks and heightlocks
    pub fn is_valid(&self) -> Result<(), PolicyError> {
        use Policy::*;

        self.check_timelocks()?;
        self.check_duplicate_keys()?;

        for policy in self.pre_order_iter() {
            match *policy {
                And(ref subs) => {
                    if subs.len() != 2 {
                        return Err(PolicyError::NonBinaryArgAnd);
                    }
                }
                Or(ref subs) => {
                    if subs.len() != 2 {
                        return Err(PolicyError::NonBinaryArgOr);
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Checks if any possible compilation of the policy could be compiled
    /// as non-malleable and safe.
    ///
    /// # Returns
    ///
    /// Returns a tuple `(safe, non-malleable)` to avoid the fact that
    /// non-malleability depends on safety and we would like to cache results.
    pub fn is_safe_nonmalleable(&self) -> (bool, bool) {
        use Policy::*;

        let mut acc = vec![];
        for data in self.rtl_post_order_iter() {
            let new = match data.node {
                Unsatisfiable | Trivial | Key(_) => (true, true),
                Sha256(_) | Hash256(_) | Ripemd160(_) | Hash160(_) | After(_) | Older(_) => {
                    (false, true)
                }
                And(ref subs) => {
                    let (atleast_one_safe, all_non_mall) = (0..subs.len())
                        .map(|_| acc.pop().unwrap())
                        .fold((false, true), |acc, x: (bool, bool)| (acc.0 || x.0, acc.1 && x.1));
                    (atleast_one_safe, all_non_mall)
                }
                Or(ref subs) => {
                    let (all_safe, atleast_one_safe, all_non_mall) = (0..subs.len())
                        .map(|_| acc.pop().unwrap())
                        .fold((true, false, true), |acc, x| {
                            (acc.0 && x.0, acc.1 || x.0, acc.2 && x.1)
                        });
                    (all_safe, atleast_one_safe && all_non_mall)
                }
                Thresh(ref thresh) => {
                    let (safe_count, non_mall_count) = (0..thresh.n())
                        .map(|_| acc.pop().unwrap())
                        .fold((0, 0), |(safe_count, non_mall_count), (safe, non_mall)| {
                            (safe_count + safe as usize, non_mall_count + non_mall as usize)
                        });
                    (
                        safe_count >= (thresh.n() - thresh.k() + 1),
                        non_mall_count == thresh.n() && safe_count >= (thresh.n() - thresh.k()),
                    )
                }
            };
            acc.push(new);
        }
        // Ok to unwrap because we know we processed at least one node.
        acc.pop().unwrap()
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Policy<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Policy::Unsatisfiable => f.write_str("UNSATISFIABLE()"),
            Policy::Trivial => f.write_str("TRIVIAL()"),
            Policy::Key(ref pk) => write!(f, "pk({:?})", pk),
            Policy::After(n) => write!(f, "after({})", n),
            Policy::Older(n) => write!(f, "older({})", n),
            Policy::Sha256(ref h) => write!(f, "sha256({})", h),
            Policy::Hash256(ref h) => write!(f, "hash256({})", h),
            Policy::Ripemd160(ref h) => write!(f, "ripemd160({})", h),
            Policy::Hash160(ref h) => write!(f, "hash160({})", h),
            Policy::And(ref subs) => {
                f.write_str("and(")?;
                if !subs.is_empty() {
                    write!(f, "{:?}", subs[0])?;
                    for sub in &subs[1..] {
                        write!(f, ",{:?}", sub)?;
                    }
                }
                f.write_str(")")
            }
            Policy::Or(ref subs) => {
                f.write_str("or(")?;
                if !subs.is_empty() {
                    write!(f, "{}@{:?}", subs[0].0, subs[0].1)?;
                    for sub in &subs[1..] {
                        write!(f, ",{}@{:?}", sub.0, sub.1)?;
                    }
                }
                f.write_str(")")
            }
            Policy::Thresh(ref thresh) => fmt::Debug::fmt(&thresh.debug("thresh", true), f),
        }
    }
}

impl<Pk: MiniscriptKey> fmt::Display for Policy<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Policy::Unsatisfiable => f.write_str("UNSATISFIABLE"),
            Policy::Trivial => f.write_str("TRIVIAL"),
            Policy::Key(ref pk) => write!(f, "pk({})", pk),
            Policy::After(n) => write!(f, "after({})", n),
            Policy::Older(n) => write!(f, "older({})", n),
            Policy::Sha256(ref h) => write!(f, "sha256({})", h),
            Policy::Hash256(ref h) => write!(f, "hash256({})", h),
            Policy::Ripemd160(ref h) => write!(f, "ripemd160({})", h),
            Policy::Hash160(ref h) => write!(f, "hash160({})", h),
            Policy::And(ref subs) => {
                f.write_str("and(")?;
                if !subs.is_empty() {
                    write!(f, "{}", subs[0])?;
                    for sub in &subs[1..] {
                        write!(f, ",{}", sub)?;
                    }
                }
                f.write_str(")")
            }
            Policy::Or(ref subs) => {
                f.write_str("or(")?;
                if !subs.is_empty() {
                    write!(f, "{}@{}", subs[0].0, subs[0].1)?;
                    for sub in &subs[1..] {
                        write!(f, ",{}@{}", sub.0, sub.1)?;
                    }
                }
                f.write_str(")")
            }
            Policy::Thresh(ref thresh) => fmt::Display::fmt(&thresh.display("thresh", true), f),
        }
    }
}

impl<Pk: FromStrKey> str::FromStr for Policy<Pk> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Policy<Pk>, Error> {
        let tree = expression::Tree::from_str(s)?;
        let policy: Policy<Pk> = FromTree::from_tree(&tree)?;
        policy.check_timelocks().map_err(Error::ConcretePolicy)?;
        Ok(policy)
    }
}

serde_string_impl_pk!(Policy, "a miniscript concrete policy");

impl<Pk: FromStrKey> Policy<Pk> {
    /// Helper function for `from_tree` to parse subexpressions with
    /// names of the form x@y
    fn from_tree_prob(
        top: &expression::Tree,
        allow_prob: bool,
    ) -> Result<(usize, Policy<Pk>), Error> {
        // When 'allow_prob' is true we parse '@' signs out of node names.
        let (frag_prob, frag_name) = if allow_prob {
            top.name_separated('@')
                .map_err(From::from)
                .map_err(Error::Parse)?
        } else {
            (None, top.name())
        };

        let frag_prob = match frag_prob {
            None => 1,
            Some(s) => expression::parse_num(s)
                .map_err(From::from)
                .map_err(Error::Parse)? as usize,
        };

        match frag_name {
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
                top.verify_n_children("and", 2..=2)
                    .map_err(From::from)
                    .map_err(Error::Parse)?;
                let subs = top
                    .children()
                    .map(|arg| Self::from_tree(arg).map(Arc::new))
                    .collect::<Result<_, Error>>()?;
                Ok(Policy::And(subs))
            }
            "or" => {
                top.verify_n_children("or", 2..=2)
                    .map_err(From::from)
                    .map_err(Error::Parse)?;
                let subs = top
                    .children()
                    .map(|arg| {
                        Self::from_tree_prob(arg, true).map(|(prob, sub)| (prob, Arc::new(sub)))
                    })
                    .collect::<Result<_, Error>>()?;
                Ok(Policy::Or(subs))
            }
            "thresh" => top
                .verify_threshold(|sub| Self::from_tree(sub).map(Arc::new))
                .map(Self::Thresh),
            x => Err(Error::Parse(crate::ParseError::Tree(crate::ParseTreeError::UnknownName {
                name: x.to_owned(),
            }))),
        }
        .map(|res| (frag_prob, res))
    }
}

impl<Pk: FromStrKey> expression::FromTree for Policy<Pk> {
    fn from_tree(top: &expression::Tree) -> Result<Policy<Pk>, Error> {
        Policy::from_tree_prob(top, false).map(|(_, result)| result)
    }
}

/// Creates a Huffman Tree from compiled [`Miniscript`] nodes.
#[cfg(feature = "compiler")]
fn with_huffman_tree<Pk: MiniscriptKey>(ms: Vec<(OrdF64, Miniscript<Pk, Tap>)>) -> TapTree<Pk> {
    let mut node_weights = BinaryHeap::<(Reverse<OrdF64>, TapTree<Pk>)>::new();
    for (prob, script) in ms {
        node_weights.push((Reverse(prob), TapTree::Leaf(Arc::new(script))));
    }
    assert_ne!(node_weights.len(), 0, "empty Miniscript compilation");
    while node_weights.len() > 1 {
        let (p1, s1) = node_weights.pop().expect("len must at least be two");
        let (p2, s2) = node_weights.pop().expect("len must at least be two");

        let p = (p1.0).0 + (p2.0).0;
        node_weights.push((Reverse(OrdF64(p)), TapTree::combine(s1, s2)));
    }

    debug_assert!(node_weights.len() == 1);
    node_weights
        .pop()
        .expect("huffman tree algorithm is broken")
        .1
}

/// Enumerates a [`Policy::Thresh(k, ..n..)`] into `n` different thresh's.
///
/// ## Strategy
///
/// `thresh(k, x_1...x_n) := thresh(1, thresh(k, x_2...x_n), thresh(k, x_1x_3...x_n), ...., thresh(k, x_1...x_{n-1}))`
/// by the simple argument that choosing `k` conditions from `n` available conditions might not contain
/// any one of the conditions exclusively.
#[cfg(feature = "compiler")]
fn generate_combination<Pk: MiniscriptKey>(
    thresh: &Threshold<Arc<Policy<Pk>>, 0>,
    prob: f64,
) -> Vec<(f64, Arc<Policy<Pk>>)> {
    debug_assert!(thresh.k() < thresh.n());

    let prob_over_n = prob / thresh.n() as f64;
    let mut ret: Vec<(f64, Arc<Policy<Pk>>)> = vec![];
    for i in 0..thresh.n() {
        let thresh_less_1 = Threshold::from_iter(
            thresh.k(),
            thresh
                .iter()
                .enumerate()
                .filter_map(|(j, sub)| if j != i { Some(Arc::clone(sub)) } else { None }),
        )
        .expect("k is strictly less than n, so (k, n-1) is a valid threshold");
        ret.push((prob_over_n, Arc::new(Policy::Thresh(thresh_less_1))));
    }
    ret
}

/// A type used within the iterator API to abstract over the two kinds
/// of n-ary nodes in a [`Policy`].
///
/// Generally speaking, users should never need to see or be aware of this
/// type. But when directly implementing iterators it may come in handy.
#[derive(Clone)]
pub enum TreeChildren<'a, Pk: MiniscriptKey> {
    /// A conjunction or threshold node's children.
    And(&'a [Arc<Policy<Pk>>]),
    /// A disjunction node's children.
    Or(&'a [(usize, Arc<Policy<Pk>>)]),
}

impl<'a, Pk: MiniscriptKey> TreeLike for &'a Policy<Pk> {
    type NaryChildren = TreeChildren<'a, Pk>;

    fn nary_len(tc: &Self::NaryChildren) -> usize {
        match tc {
            TreeChildren::And(sl) => sl.len(),
            TreeChildren::Or(sl) => sl.len(),
        }
    }
    fn nary_index(tc: Self::NaryChildren, idx: usize) -> Self {
        match tc {
            TreeChildren::And(sl) => &sl[idx],
            TreeChildren::Or(sl) => &sl[idx].1,
        }
    }

    fn as_node(&self) -> Tree<Self, Self::NaryChildren> {
        use Policy::*;

        match *self {
            Unsatisfiable | Trivial | Key(_) | After(_) | Older(_) | Sha256(_) | Hash256(_)
            | Ripemd160(_) | Hash160(_) => Tree::Nullary,
            And(ref subs) => Tree::Nary(TreeChildren::And(subs)),
            Or(ref v) => Tree::Nary(TreeChildren::Or(v)),
            Thresh(ref thresh) => Tree::Nary(TreeChildren::And(thresh.data())),
        }
    }
}

impl<'a, Pk: MiniscriptKey> TreeLike for &'a Arc<Policy<Pk>> {
    type NaryChildren = TreeChildren<'a, Pk>;

    fn nary_len(tc: &Self::NaryChildren) -> usize {
        match tc {
            TreeChildren::And(sl) => sl.len(),
            TreeChildren::Or(sl) => sl.len(),
        }
    }
    fn nary_index(tc: Self::NaryChildren, idx: usize) -> Self {
        match tc {
            TreeChildren::And(sl) => &sl[idx],
            TreeChildren::Or(sl) => &sl[idx].1,
        }
    }

    fn as_node(&self) -> Tree<Self, Self::NaryChildren> {
        use Policy::*;

        match ***self {
            Unsatisfiable | Trivial | Key(_) | After(_) | Older(_) | Sha256(_) | Hash256(_)
            | Ripemd160(_) | Hash160(_) => Tree::Nullary,
            And(ref subs) => Tree::Nary(TreeChildren::And(subs)),
            Or(ref v) => Tree::Nary(TreeChildren::Or(v)),
            Thresh(ref thresh) => Tree::Nary(TreeChildren::And(thresh.data())),
        }
    }
}

#[cfg(all(test, feature = "compiler"))]
mod compiler_tests {
    use core::str::FromStr;

    use super::*;
    use crate::policy::Concrete;

    #[test]
    fn test_gen_comb() {
        let policies: Vec<Arc<Concrete<String>>> = vec!["pk(A)", "pk(B)", "pk(C)", "pk(D)"]
            .into_iter()
            .map(|st| policy_str!("{}", st))
            .map(Arc::new)
            .collect();
        let thresh = Threshold::new(2, policies).unwrap();

        let combinations = generate_combination(&thresh, 1.0);

        let comb_a: Vec<Policy<String>> = vec![
            policy_str!("pk(B)"),
            policy_str!("pk(C)"),
            policy_str!("pk(D)"),
        ];
        let comb_b: Vec<Policy<String>> = vec![
            policy_str!("pk(A)"),
            policy_str!("pk(C)"),
            policy_str!("pk(D)"),
        ];
        let comb_c: Vec<Policy<String>> = vec![
            policy_str!("pk(A)"),
            policy_str!("pk(B)"),
            policy_str!("pk(D)"),
        ];
        let comb_d: Vec<Policy<String>> = vec![
            policy_str!("pk(A)"),
            policy_str!("pk(B)"),
            policy_str!("pk(C)"),
        ];
        let expected_comb = vec![comb_a, comb_b, comb_c, comb_d]
            .into_iter()
            .map(|sub_pol| {
                let expected_thresh =
                    Threshold::from_iter(2, sub_pol.into_iter().map(Arc::new)).unwrap();
                (0.25, Arc::new(Policy::Thresh(expected_thresh)))
            })
            .collect::<Vec<_>>();
        assert_eq!(combinations, expected_comb);
    }

    #[test]
    fn test_tr_pk_only() {
        let policy: Policy<String> = policy_str!("pk(A)");
        let desc = policy.compile_tr(None).unwrap();
        // pk(A) promoted to the internal key, leaving the script tree empty
        assert_eq!(desc.to_string(), "tr(A)#xyg3grex");
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn for_each_key_count_keys() {
        let liquid_pol = Policy::<String>::from_str(
            "or(and(older(4096),thresh(2,pk(A),pk(B),pk(C))),thresh(11,pk(F1),pk(F2),pk(F3),pk(F4),pk(F5),pk(F6),pk(F7),pk(F8),pk(F9),pk(F10),pk(F11),pk(F12),pk(F13),pk(F14)))").unwrap();
        let mut count = 0;
        assert!(liquid_pol.for_each_key(|_| {
            count += 1;
            true
        }));
        assert_eq!(count, 17);
    }

    #[test]
    fn for_each_key_fails_predicate() {
        let policy =
            Policy::<String>::from_str("or(and(pk(key0),pk(key1)),pk(oddnamedkey))").unwrap();
        assert!(!policy.for_each_key(|k| k.starts_with("key")));
    }

    #[test]
    fn tranaslate_pk() {
        pub struct TestTranslator;
        impl Translator<String> for TestTranslator {
            type TargetPk = String;
            type Error = core::convert::Infallible;

            fn pk(&mut self, pk: &String) -> Result<String, Self::Error> {
                let new = format!("NEW-{}", pk);
                Ok(new.to_string())
            }
            fn sha256(&mut self, hash: &String) -> Result<String, Self::Error> {
                Ok(hash.to_string())
            }
            fn hash256(&mut self, hash: &String) -> Result<String, Self::Error> {
                Ok(hash.to_string())
            }
            fn ripemd160(&mut self, hash: &String) -> Result<String, Self::Error> {
                Ok(hash.to_string())
            }
            fn hash160(&mut self, hash: &String) -> Result<String, Self::Error> {
                Ok(hash.to_string())
            }
        }
        let policy = Policy::<String>::from_str("or(and(pk(A),pk(B)),pk(C))").unwrap();
        let mut t = TestTranslator;

        let want = Policy::<String>::from_str("or(and(pk(NEW-A),pk(NEW-B)),pk(NEW-C))").unwrap();
        let got = policy
            .translate_pk(&mut t)
            .expect("failed to translate keys");

        assert_eq!(got, want);
    }

    #[test]
    fn translate_unsatisfiable_pk() {
        let policy = Policy::<String>::from_str("or(and(pk(A),pk(B)),pk(C))").unwrap();

        let want = Policy::<String>::from_str("or(and(pk(A),UNSATISFIABLE),pk(C))").unwrap();
        let got = policy.translate_unsatisfiable_pk(&"B".to_string());

        assert_eq!(got, want);
    }

    #[test]
    fn keys() {
        let policy = Policy::<String>::from_str("or(and(pk(A),pk(B)),pk(C))").unwrap();

        let want = vec!["A", "B", "C"];
        let got = policy.keys();

        assert_eq!(got, want);
    }

    #[test]
    #[cfg(feature = "compiler")]
    fn num_tap_leaves() {
        let policy = Policy::<String>::from_str("or(and(pk(A),pk(B)),pk(C))").unwrap();
        assert_eq!(policy.num_tap_leaves(), 2);
    }

    #[test]
    #[should_panic]
    fn check_timelocks() {
        // This implicitly tests the check_timelocks API (has height and time locks).
        let _ = Policy::<String>::from_str("and(after(10),after(500000000))").unwrap();
    }
}
