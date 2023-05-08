// Written in 2019 by Andrew Poelstra <apoelstra@wpsoftware.net>
// SPDX-License-Identifier: CC0-1.0

//! Concrete Policies
//!

use core::{fmt, str};
#[cfg(feature = "std")]
use std::error;

use bitcoin::{LockTime, PackedLockTime, Sequence};
#[cfg(feature = "compiler")]
use {
    crate::descriptor::TapTree,
    crate::miniscript::ScriptContext,
    crate::policy::compiler::CompilerError,
    crate::policy::compiler::OrdF64,
    crate::policy::{compiler, Concrete, Liftable, Semantic},
    crate::Descriptor,
    crate::Miniscript,
    crate::Tap,
    core::cmp::Reverse,
    sync::Arc,
};

use super::ENTAILMENT_MAX_TERMINALS;
use crate::expression::{self, FromTree};
use crate::miniscript::types::extra_props::TimelockInfo;
use crate::prelude::*;
#[cfg(all(doc, not(feature = "compiler")))]
use crate::Descriptor;
use crate::{errstr, Error, ForEachKey, MiniscriptKey, Translator};

/// Maximum TapLeafs allowed in a compiled TapTree
#[cfg(feature = "compiler")]
const MAX_COMPILATION_LEAVES: usize = 1024;

/// Concrete policy which corresponds directly to a Miniscript structure,
/// and whose disjunctions are annotated with satisfaction probabilities
/// to assist the compiler
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Policy<Pk: MiniscriptKey> {
    /// Unsatisfiable
    Unsatisfiable,
    /// Trivially satisfiable
    Trivial,
    /// A public key which must sign to satisfy the descriptor
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
    /// A list of sub-policies, all of which must be satisfied
    And(Vec<Policy<Pk>>),
    /// A list of sub-policies, one of which must be satisfied, along with
    /// relative probabilities for each one
    Or(Vec<(usize, Policy<Pk>)>),
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

/// Lightweight repr of Concrete policy which corresponds directly to a
/// Miniscript structure, and whose disjunctions are annotated with satisfaction
/// probabilities to assist the compiler
#[cfg(feature = "compiler")]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum PolicyArc<Pk: MiniscriptKey> {
    /// Unsatisfiable
    Unsatisfiable,
    /// Trivially satisfiable
    Trivial,
    /// A public key which must sign to satisfy the descriptor
    Key(Pk),
    /// An absolute locktime restriction
    After(u32),
    /// A relative locktime restriction
    Older(u32),
    /// A SHA256 whose preimage must be provided to satisfy the descriptor
    Sha256(Pk::Sha256),
    /// A SHA256d whose preimage must be provided to satisfy the descriptor
    Hash256(Pk::Hash256),
    /// A RIPEMD160 whose preimage must be provided to satisfy the descriptor
    Ripemd160(Pk::Ripemd160),
    /// A HASH160 whose preimage must be provided to satisfy the descriptor
    Hash160(Pk::Hash160),
    /// A list of sub-policies' references, all of which must be satisfied
    And(Vec<Arc<PolicyArc<Pk>>>),
    /// A list of sub-policies's references, one of which must be satisfied,
    /// along with relative probabilities for each one
    Or(Vec<(usize, Arc<PolicyArc<Pk>>)>),
    /// A set of descriptors' references, satisfactions must be provided for `k` of them
    Threshold(usize, Vec<Arc<PolicyArc<Pk>>>),
}

#[cfg(feature = "compiler")]
impl<Pk: MiniscriptKey> From<PolicyArc<Pk>> for Policy<Pk> {
    fn from(p: PolicyArc<Pk>) -> Self {
        match p {
            PolicyArc::Unsatisfiable => Policy::Unsatisfiable,
            PolicyArc::Trivial => Policy::Trivial,
            PolicyArc::Key(pk) => Policy::Key(pk),
            PolicyArc::After(t) => Policy::After(PackedLockTime::from(LockTime::from_consensus(t))),
            PolicyArc::Older(t) => Policy::Older(Sequence::from_consensus(t)),
            PolicyArc::Sha256(hash) => Policy::Sha256(hash),
            PolicyArc::Hash256(hash) => Policy::Hash256(hash),
            PolicyArc::Ripemd160(hash) => Policy::Ripemd160(hash),
            PolicyArc::Hash160(hash) => Policy::Hash160(hash),
            PolicyArc::And(subs) => Policy::And(
                subs.into_iter()
                    .map(|pol| Self::from((*pol).clone()))
                    .collect(),
            ),
            PolicyArc::Or(subs) => Policy::Or(
                subs.into_iter()
                    .map(|(odds, sub)| (odds, Self::from((*sub).clone())))
                    .collect(),
            ),
            PolicyArc::Threshold(k, subs) => Policy::Threshold(
                k,
                subs.into_iter()
                    .map(|pol| Self::from((*pol).clone()))
                    .collect(),
            ),
        }
    }
}

#[cfg(feature = "compiler")]
impl<Pk: MiniscriptKey> From<Policy<Pk>> for PolicyArc<Pk> {
    fn from(p: Policy<Pk>) -> Self {
        match p {
            Policy::Unsatisfiable => PolicyArc::Unsatisfiable,
            Policy::Trivial => PolicyArc::Trivial,
            Policy::Key(pk) => PolicyArc::Key(pk),
            Policy::After(PackedLockTime(t)) => PolicyArc::After(t),
            Policy::Older(Sequence(t)) => PolicyArc::Older(t),
            Policy::Sha256(hash) => PolicyArc::Sha256(hash),
            Policy::Hash256(hash) => PolicyArc::Hash256(hash),
            Policy::Ripemd160(hash) => PolicyArc::Ripemd160(hash),
            Policy::Hash160(hash) => PolicyArc::Hash160(hash),
            Policy::And(subs) => PolicyArc::And(
                subs.iter()
                    .map(|sub| Arc::new(Self::from(sub.clone())))
                    .collect(),
            ),
            Policy::Or(subs) => PolicyArc::Or(
                subs.iter()
                    .map(|(odds, sub)| (*odds, Arc::new(Self::from(sub.clone()))))
                    .collect(),
            ),
            Policy::Threshold(k, subs) => PolicyArc::Threshold(
                k,
                subs.iter()
                    .map(|sub| Arc::new(Self::from(sub.clone())))
                    .collect(),
            ),
        }
    }
}

/// Detailed Error type for Policies
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum PolicyError {
    /// `And` fragments only support two args
    NonBinaryArgAnd,
    /// `Or` fragments only support two args
    NonBinaryArgOr,
    /// `Thresh` fragment can only have `1<=k<=n`
    IncorrectThresh,
    /// `older` or `after` fragment can only have `n = 0`
    ZeroTime,
    /// `after` fragment can only have ` n < 2^31`
    TimeTooFar,
    /// Semantic Policy Error: `And` `Or` fragments must take args: k > 1
    InsufficientArgsforAnd,
    /// Semantic Policy Error: `And` `Or` fragments must take args: k > 1
    InsufficientArgsforOr,
    /// Entailment max terminals exceeded
    EntailmentMaxTerminals,
    /// lifting error: Cannot lift policies that have
    /// a combination of height and timelocks.
    HeightTimelockCombination,
    /// Duplicate Public Keys
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
            PolicyError::IncorrectThresh => {
                f.write_str("Threshold k must be greater than 0 and less than or equal to n 0<k<=n")
            }
            PolicyError::TimeTooFar => {
                f.write_str("Relative/Absolute time must be less than 2^31; n < 2^31")
            }
            PolicyError::ZeroTime => f.write_str("Time must be greater than 0; n > 0"),
            PolicyError::InsufficientArgsforAnd => {
                f.write_str("Semantic Policy 'And' fragment must have at least 2 args ")
            }
            PolicyError::InsufficientArgsforOr => {
                f.write_str("Semantic Policy 'Or' fragment must have at least 2 args ")
            }
            PolicyError::EntailmentMaxTerminals => write!(
                f,
                "Policy entailment only supports {} terminals",
                ENTAILMENT_MAX_TERMINALS
            ),
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
            NonBinaryArgAnd
            | NonBinaryArgOr
            | IncorrectThresh
            | ZeroTime
            | TimeTooFar
            | InsufficientArgsforAnd
            | InsufficientArgsforOr
            | EntailmentMaxTerminals
            | HeightTimelockCombination
            | DuplicatePubKeys => None,
        }
    }
}

impl<Pk: MiniscriptKey> Policy<Pk> {
    /// Flatten the [`Policy`] tree structure into a Vector of tuple `(leaf script, leaf probability)`
    /// with leaf probabilities corresponding to odds for sub-branch in the policy.
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
    /// Since this splitting might lead to exponential blow-up, we constraint the number of
    /// leaf-nodes to [`MAX_COMPILATION_LEAVES`].
    #[cfg(feature = "compiler")]
    fn to_tapleaf_prob_vec(&self, prob: f64) -> Vec<(f64, Policy<Pk>)> {
        match self {
            Policy::Or(ref subs) => {
                let total_odds: usize = subs.iter().map(|(ref k, _)| k).sum();
                subs.iter()
                    .map(|(k, ref policy)| {
                        policy.to_tapleaf_prob_vec(prob * *k as f64 / total_odds as f64)
                    })
                    .flatten()
                    .collect::<Vec<_>>()
            }
            Policy::Threshold(k, ref subs) if *k == 1 => {
                let total_odds = subs.len();
                subs.iter()
                    .map(|policy| policy.to_tapleaf_prob_vec(prob / total_odds as f64))
                    .flatten()
                    .collect::<Vec<_>>()
            }
            x => vec![(prob, x.clone())],
        }
    }

    /// Extract the internal_key from policy tree.
    #[cfg(feature = "compiler")]
    fn extract_key(self, unspendable_key: Option<Pk>) -> Result<(Pk, Policy<Pk>), Error> {
        let mut internal_key: Option<Pk> = None;
        {
            let mut prob = 0.;
            let semantic_policy = self.lift()?;
            let concrete_keys = self.keys();
            let key_prob_map: HashMap<_, _> = self
                .to_tapleaf_prob_vec(1.0)
                .into_iter()
                .filter(|(_, ref pol)| match *pol {
                    Concrete::Key(..) => true,
                    _ => false,
                })
                .map(|(prob, key)| (key, prob))
                .collect();

            for key in concrete_keys.into_iter() {
                if semantic_policy
                    .clone()
                    .satisfy_constraint(&Semantic::Key(key.clone()), true)
                    == Semantic::Trivial
                {
                    match key_prob_map.get(&Concrete::Key(key.clone())) {
                        Some(val) => {
                            if *val > prob {
                                prob = *val;
                                internal_key = Some(key.clone());
                            }
                        }
                        None => return Err(errstr("Key should have existed in the HashMap!")),
                    }
                }
            }
        }
        match (internal_key, unspendable_key) {
            (Some(ref key), _) => Ok((key.clone(), self.translate_unsatisfiable_pk(&key))),
            (_, Some(key)) => Ok((key, self)),
            _ => Err(errstr("No viable internal key found.")),
        }
    }

    /// Compile the [`Policy`] into a [`Descriptor::Tr`].
    ///
    /// ### TapTree compilation
    ///
    /// The policy tree constructed by root-level disjunctions over [`Or`][`Policy::Or`] and
    /// [`Thresh`][`Policy::Threshold`](1, ..) which is flattened into a vector (with respective
    /// probabilities derived from odds) of policies.
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
    pub fn compile_tr(&self, unspendable_key: Option<Pk>) -> Result<Descriptor<Pk>, Error> {
        self.is_valid()?; // Check for validity
        match self.is_safe_nonmalleable() {
            (false, _) => Err(Error::from(CompilerError::TopLevelNonSafe)),
            (_, false) => Err(Error::from(
                CompilerError::ImpossibleNonMalleableCompilation,
            )),
            _ => {
                let (internal_key, policy) = self.clone().extract_key(unspendable_key)?;
                policy.check_num_tapleaves()?;
                let tree = Descriptor::new_tr(
                    internal_key,
                    match policy {
                        Policy::Trivial => None,
                        policy => {
                            let vec_policies: Vec<_> = policy.to_tapleaf_prob_vec(1.0);
                            let mut leaf_compilations: Vec<(OrdF64, Miniscript<Pk, Tap>)> = vec![];
                            for (prob, pol) in vec_policies {
                                // policy corresponding to the key (replaced by unsatisfiable) is skipped
                                if pol == Policy::Unsatisfiable {
                                    continue;
                                }
                                let compilation = compiler::best_compilation::<Pk, Tap>(&pol)?;
                                compilation.sanity_check()?;
                                leaf_compilations.push((OrdF64(prob), compilation));
                            }
                            let taptree = with_huffman_tree::<Pk>(leaf_compilations)?;
                            Some(taptree)
                        }
                    },
                )?;
                Ok(tree)
            }
        }
    }

    /// Compiles the [`Policy`] into a [`Descriptor::Tr`].
    ///
    /// ### TapTree compilation
    ///
    /// The policy tree constructed by root-level disjunctions over [`Policy::Or`] and
    /// [`Policy::Threshold`] (k, ..n..) which is flattened into a vector (with respective
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
    ///
    /// [`Policy`]: crate::policy::concrete::Policy
    #[cfg(feature = "compiler")]
    pub fn compile_tr_private_experimental(
        &self,
        unspendable_key: Option<Pk>,
    ) -> Result<Descriptor<Pk>, Error> {
        self.is_valid()?; // Check for validity
        match self.is_safe_nonmalleable() {
            (false, _) => Err(Error::from(CompilerError::TopLevelNonSafe)),
            (_, false) => Err(Error::from(
                CompilerError::ImpossibleNonMalleableCompilation,
            )),
            _ => {
                let (internal_key, policy) = self.clone().extract_key(unspendable_key)?;
                let tree = Descriptor::new_tr(
                    internal_key,
                    match policy {
                        Policy::Trivial => None,
                        policy => {
                            let pol = PolicyArc::from(policy);
                            let leaf_compilations: Vec<_> = pol
                                .enumerate_policy_tree(1.0)
                                .into_iter()
                                .filter(|x| x.1 != Arc::new(PolicyArc::Unsatisfiable))
                                .map(|(prob, ref pol)| {
                                    let converted_pol = Policy::<Pk>::from((**pol).clone());
                                    (
                                        OrdF64(prob),
                                        compiler::best_compilation(&converted_pol).unwrap(),
                                    )
                                })
                                .collect();
                            let taptree = with_huffman_tree::<Pk>(leaf_compilations).unwrap();
                            Some(taptree)
                        }
                    },
                )?;
                Ok(tree)
            }
        }
    }

    /// Compile the [`Policy`] into desc_ctx [`Descriptor`]
    ///
    /// In case of [Tr][`DescriptorCtx::Tr`], `internal_key` is used for the Taproot comilation when
    /// no public key can be inferred from the given policy.
    ///
    /// # NOTE:
    ///
    /// It is **not recommended** to use policy as a stable identifier for a miniscript.
    /// You should use the policy compiler once, and then use the miniscript output as a stable identifier.
    /// See the compiler document in doc/compiler.md for more details.
    #[cfg(feature = "compiler")]
    pub fn compile_to_descriptor<Ctx: ScriptContext>(
        &self,
        desc_ctx: DescriptorCtx<Pk>,
    ) -> Result<Descriptor<Pk>, Error> {
        self.is_valid()?;
        match self.is_safe_nonmalleable() {
            (false, _) => Err(Error::from(CompilerError::TopLevelNonSafe)),
            (_, false) => Err(Error::from(
                CompilerError::ImpossibleNonMalleableCompilation,
            )),
            _ => match desc_ctx {
                DescriptorCtx::Bare => Descriptor::new_bare(compiler::best_compilation(self)?),
                DescriptorCtx::Sh => Descriptor::new_sh(compiler::best_compilation(self)?),
                DescriptorCtx::Wsh => Descriptor::new_wsh(compiler::best_compilation(self)?),
                DescriptorCtx::ShWsh => Descriptor::new_sh_wsh(compiler::best_compilation(self)?),
                DescriptorCtx::Tr(unspendable_key) => self.compile_tr(unspendable_key),
            },
        }
    }

    /// Compile the descriptor into an optimized `Miniscript` representation
    ///
    /// # NOTE:
    ///
    /// It is **not recommended** to use policy as a stable identifier for a miniscript.
    /// You should use the policy compiler once, and then use the miniscript output as a stable identifier.
    /// See the compiler document in doc/compiler.md for more details.
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
impl<Pk: MiniscriptKey> PolicyArc<Pk> {
    /// Given a [`Policy`], return a vector of policies whose disjunction is isomorphic to the initial one.
    /// This function is supposed to incrementally expand i.e. represent the policy as disjunction over
    /// sub-policies output by it. The probability calculations are similar as
    /// [to_tapleaf_prob_vec][`Policy::to_tapleaf_prob_vec`]
    #[cfg(feature = "compiler")]
    fn enumerate_pol(&self, prob: f64) -> Vec<(f64, Arc<Self>)> {
        match self {
            PolicyArc::Or(subs) => {
                let total_odds = subs.iter().fold(0, |acc, x| acc + x.0);
                subs.iter()
                    .map(|(odds, pol)| (prob * *odds as f64 / total_odds as f64, pol.clone()))
                    .collect::<Vec<_>>()
            }
            PolicyArc::Threshold(k, subs) if *k == 1 => {
                let total_odds = subs.len();
                subs.iter()
                    .map(|pol| (prob / total_odds as f64, pol.clone()))
                    .collect::<Vec<_>>()
            }
            PolicyArc::Threshold(k, subs) if *k != subs.len() => {
                generate_combination(subs, prob, *k)
            }
            pol => vec![(prob, Arc::new(pol.clone()))],
        }
    }

    /// Generates a root-level disjunctive tree over the given policy tree.
    ///
    /// Uses a fixed-point algorithm to enumerate the disjunctions until exhaustive root-level
    /// enumeration or limits exceed. For a given [`Policy`], we maintain an [ordered
    /// set](`BTreeSet`) of `(prob, policy)` (ordered by probability) to maintain the list of
    /// enumerated sub-policies whose disjunction is isomorphic to initial policy (*invariant*).
    ///
    /// [`Policy`]: crate::policy::concrete::Policy
    #[cfg(feature = "compiler")]
    fn enumerate_policy_tree(self, prob: f64) -> Vec<(f64, Arc<Self>)> {
        let mut tapleaf_prob_vec = BTreeSet::<(Reverse<OrdF64>, Arc<Self>)>::new();
        // Store probability corresponding to policy in the enumerated tree. This is required since
        // owing to the current [policy element enumeration algorithm][`Policy::enumerate_pol`],
        // two passes of the algorithm might result in same sub-policy showing up. Currently, we
        // merge the nodes by adding up the corresponding probabilities for the same policy.
        let mut pol_prob_map = HashMap::<Arc<Self>, OrdF64>::new();

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
            let mut curr_policy: Arc<Self> = Arc::new(PolicyArc::Unsatisfiable);
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
            Policy::Threshold(_, ref subs) | Policy::And(ref subs) => {
                subs.iter().all(|sub| sub.real_for_each_key(&mut *pred))
            }
            Policy::Or(ref subs) => subs.iter().all(|(_, sub)| sub.real_for_each_key(&mut *pred)),
        }
    }

    /// Convert a policy using one kind of public key to another
    /// type of public key
    ///
    /// # Example
    ///
    /// ```
    /// use miniscript::{bitcoin::PublicKey, policy::concrete::Policy, Translator, hash256};
    /// use std::str::FromStr;
    /// use miniscript::translate_hash_fail;
    /// use std::collections::HashMap;
    /// use miniscript::bitcoin::hashes::{sha256, hash160, ripemd160};
    /// let alice_key = "0270cf3c71f65a3d93d285d9149fddeeb638f87a2d4d8cf16c525f71c417439777";
    /// let bob_key = "02f43b15c50a436f5335dbea8a64dd3b4e63e34c3b50c42598acb5f4f336b5d2fb";
    /// let placeholder_policy = Policy::<String>::from_str("and(pk(alice_key),pk(bob_key))").unwrap();
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
    ///     // Provides the translation public keys P -> Q
    ///     fn pk(&mut self, pk: &String) -> Result<bitcoin::PublicKey, ()> {
    ///         self.pk_map.get(pk).copied().ok_or(()) // Dummy Err
    ///     }
    ///
    ///     // Fail for hash types
    ///     translate_hash_fail!(String, bitcoin::PublicKey, ());
    /// }
    ///
    /// let mut pk_map = HashMap::new();
    /// pk_map.insert(String::from("alice_key"), bitcoin::PublicKey::from_str(alice_key).unwrap());
    /// pk_map.insert(String::from("bob_key"), bitcoin::PublicKey::from_str(bob_key).unwrap());
    /// let mut t = StrPkTranslator { pk_map: pk_map };
    ///
    /// let real_policy = placeholder_policy.translate_pk(&mut t).unwrap();
    ///
    /// let expected_policy = Policy::from_str(&format!("and(pk({}),pk({}))", alice_key, bob_key)).unwrap();
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
            Policy::Older(n) => Ok(Policy::Older(n)),
            Policy::After(n) => Ok(Policy::After(n)),
            Policy::Threshold(k, ref subs) => {
                let new_subs: Result<Vec<Policy<Q>>, _> =
                    subs.iter().map(|sub| sub._translate_pk(t)).collect();
                new_subs.map(|ok| Policy::Threshold(k, ok))
            }
            Policy::And(ref subs) => Ok(Policy::And(
                subs.iter()
                    .map(|sub| sub._translate_pk(t))
                    .collect::<Result<Vec<Policy<Q>>, E>>()?,
            )),
            Policy::Or(ref subs) => Ok(Policy::Or(
                subs.iter()
                    .map(|&(ref prob, ref sub)| Ok((*prob, sub._translate_pk(t)?)))
                    .collect::<Result<Vec<(usize, Policy<Q>)>, E>>()?,
            )),
        }
    }

    /// Translate `Concrete::Key(key)` to `Concrete::Unsatisfiable` when extracting TapKey
    pub fn translate_unsatisfiable_pk(self, key: &Pk) -> Policy<Pk> {
        match self {
            Policy::Key(ref k) if k.clone() == *key => Policy::Unsatisfiable,
            Policy::And(subs) => Policy::And(
                subs.into_iter()
                    .map(|sub| sub.translate_unsatisfiable_pk(key))
                    .collect::<Vec<_>>(),
            ),
            Policy::Or(subs) => Policy::Or(
                subs.into_iter()
                    .map(|(k, sub)| (k, sub.translate_unsatisfiable_pk(key)))
                    .collect::<Vec<_>>(),
            ),
            Policy::Threshold(k, subs) => Policy::Threshold(
                k,
                subs.into_iter()
                    .map(|sub| sub.translate_unsatisfiable_pk(key))
                    .collect::<Vec<_>>(),
            ),
            x => x,
        }
    }

    /// Get all keys in the policy
    pub fn keys(&self) -> Vec<&Pk> {
        match *self {
            Policy::Key(ref pk) => vec![pk],
            Policy::Threshold(_k, ref subs) => {
                subs.iter().flat_map(|sub| sub.keys()).collect::<Vec<_>>()
            }
            Policy::And(ref subs) => subs.iter().flat_map(|sub| sub.keys()).collect::<Vec<_>>(),
            Policy::Or(ref subs) => subs
                .iter()
                .flat_map(|(ref _k, ref sub)| sub.keys())
                .collect::<Vec<_>>(),
            // map all hashes and time
            _ => vec![],
        }
    }

    /// Get the number of [TapLeaf][`TapTree::Leaf`] considering exhaustive root-level [OR][`Policy::Or`]
    /// and [Thresh][`Policy::Threshold`] disjunctions for the TapTree.
    #[cfg(feature = "compiler")]
    fn num_tap_leaves(&self) -> usize {
        match self {
            Policy::Or(subs) => subs.iter().map(|(_prob, pol)| pol.num_tap_leaves()).sum(),
            Policy::Threshold(k, subs) if *k == 1 => {
                subs.iter().map(|pol| pol.num_tap_leaves()).sum()
            }
            _ => 1,
        }
    }

    /// Check on the number of TapLeaves
    #[cfg(feature = "compiler")]
    fn check_num_tapleaves(&self) -> Result<(), Error> {
        if self.num_tap_leaves() > MAX_COMPILATION_LEAVES {
            return Err(errstr("Too many Tapleaves"));
        }
        Ok(())
    }

    /// Check whether the policy contains duplicate public keys
    pub fn check_duplicate_keys(&self) -> Result<(), PolicyError> {
        let pks = self.keys();
        let pks_len = pks.len();
        let unique_pks_len = pks.into_iter().collect::<HashSet<_>>().len();

        if pks_len > unique_pks_len {
            Err(PolicyError::DuplicatePubKeys)
        } else {
            Ok(())
        }
    }

    /// Checks whether the given concrete policy contains a combination of
    /// timelocks and heightlocks.
    /// Returns an error if there is at least one satisfaction that contains
    /// a combination of hieghtlock and timelock.
    pub fn check_timelocks(&self) -> Result<(), PolicyError> {
        let timelocks = self.check_timelocks_helper();
        if timelocks.contains_combination {
            Err(PolicyError::HeightTimelockCombination)
        } else {
            Ok(())
        }
    }

    // Checks whether the given concrete policy contains a combination of
    // timelocks and heightlocks
    fn check_timelocks_helper(&self) -> TimelockInfo {
        // timelocks[csv_h, csv_t, cltv_h, cltv_t, combination]
        match *self {
            Policy::Unsatisfiable
            | Policy::Trivial
            | Policy::Key(_)
            | Policy::Sha256(_)
            | Policy::Hash256(_)
            | Policy::Ripemd160(_)
            | Policy::Hash160(_) => TimelockInfo::default(),
            Policy::After(t) => TimelockInfo {
                csv_with_height: false,
                csv_with_time: false,
                cltv_with_height: LockTime::from(t).is_block_height(),
                cltv_with_time: LockTime::from(t).is_block_time(),
                contains_combination: false,
            },
            Policy::Older(t) => TimelockInfo {
                csv_with_height: t.is_height_locked(),
                csv_with_time: t.is_time_locked(),
                cltv_with_height: false,
                cltv_with_time: false,
                contains_combination: false,
            },
            Policy::Threshold(k, ref subs) => {
                let iter = subs.iter().map(|sub| sub.check_timelocks_helper());
                TimelockInfo::combine_threshold(k, iter)
            }
            Policy::And(ref subs) => {
                let iter = subs.iter().map(|sub| sub.check_timelocks_helper());
                TimelockInfo::combine_threshold(subs.len(), iter)
            }
            Policy::Or(ref subs) => {
                let iter = subs
                    .iter()
                    .map(|&(ref _p, ref sub)| sub.check_timelocks_helper());
                TimelockInfo::combine_threshold(1, iter)
            }
        }
    }

    /// This returns whether the given policy is valid or not. It maybe possible that the policy
    /// contains Non-two argument `and`, `or` or a `0` arg thresh.
    /// Validity condition also checks whether there is a possible satisfaction
    /// combination of timelocks and heightlocks
    pub fn is_valid(&self) -> Result<(), PolicyError> {
        self.check_timelocks()?;
        self.check_duplicate_keys()?;
        match *self {
            Policy::And(ref subs) => {
                if subs.len() != 2 {
                    Err(PolicyError::NonBinaryArgAnd)
                } else {
                    subs.iter()
                        .map(|sub| sub.is_valid())
                        .collect::<Result<Vec<()>, PolicyError>>()?;
                    Ok(())
                }
            }
            Policy::Or(ref subs) => {
                if subs.len() != 2 {
                    Err(PolicyError::NonBinaryArgOr)
                } else {
                    subs.iter()
                        .map(|&(ref _prob, ref sub)| sub.is_valid())
                        .collect::<Result<Vec<()>, PolicyError>>()?;
                    Ok(())
                }
            }
            Policy::Threshold(k, ref subs) => {
                if k == 0 || k > subs.len() {
                    Err(PolicyError::IncorrectThresh)
                } else {
                    subs.iter()
                        .map(|sub| sub.is_valid())
                        .collect::<Result<Vec<()>, PolicyError>>()?;
                    Ok(())
                }
            }
            Policy::After(n) => {
                if n == PackedLockTime::ZERO {
                    Err(PolicyError::ZeroTime)
                } else if n.to_u32() > 2u32.pow(31) {
                    Err(PolicyError::TimeTooFar)
                } else {
                    Ok(())
                }
            }
            Policy::Older(n) => {
                if n == Sequence::ZERO {
                    Err(PolicyError::ZeroTime)
                } else if n.to_consensus_u32() > 2u32.pow(31) {
                    Err(PolicyError::TimeTooFar)
                } else {
                    Ok(())
                }
            }
            _ => Ok(()),
        }
    }
    /// This returns whether any possible compilation of the policy could be
    /// compiled as non-malleable and safe. Note that this returns a tuple
    /// (safe, non-malleable) to avoid because the non-malleability depends on
    /// safety and we would like to cache results.
    ///
    pub fn is_safe_nonmalleable(&self) -> (bool, bool) {
        match *self {
            Policy::Unsatisfiable | Policy::Trivial => (true, true),
            Policy::Key(_) => (true, true),
            Policy::Sha256(_)
            | Policy::Hash256(_)
            | Policy::Ripemd160(_)
            | Policy::Hash160(_)
            | Policy::After(_)
            | Policy::Older(_) => (false, true),
            Policy::Threshold(k, ref subs) => {
                let (safe_count, non_mall_count) = subs
                    .iter()
                    .map(|sub| sub.is_safe_nonmalleable())
                    .fold((0, 0), |(safe_count, non_mall_count), (safe, non_mall)| {
                        (
                            safe_count + safe as usize,
                            non_mall_count + non_mall as usize,
                        )
                    });
                (
                    safe_count >= (subs.len() - k + 1),
                    non_mall_count == subs.len() && safe_count >= (subs.len() - k),
                )
            }
            Policy::And(ref subs) => {
                let (atleast_one_safe, all_non_mall) = subs
                    .iter()
                    .map(|sub| sub.is_safe_nonmalleable())
                    .fold((false, true), |acc, x| (acc.0 || x.0, acc.1 && x.1));
                (atleast_one_safe, all_non_mall)
            }

            Policy::Or(ref subs) => {
                let (all_safe, atleast_one_safe, all_non_mall) = subs
                    .iter()
                    .map(|&(_, ref sub)| sub.is_safe_nonmalleable())
                    .fold((true, false, true), |acc, x| {
                        (acc.0 && x.0, acc.1 || x.0, acc.2 && x.1)
                    });
                (all_safe, atleast_one_safe && all_non_mall)
            }
        }
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
            Policy::Threshold(k, ref subs) => {
                write!(f, "thresh({}", k)?;
                for sub in subs {
                    write!(f, ",{:?}", sub)?;
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
            Policy::Threshold(k, ref subs) => {
                write!(f, "thresh({}", k)?;
                for sub in subs {
                    write!(f, ",{}", sub)?;
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
        let policy: Policy<Pk> = FromTree::from_tree(&tree)?;
        policy.check_timelocks()?;
        Ok(policy)
    }
);

serde_string_impl_pk!(Policy, "a miniscript concrete policy");

#[rustfmt::skip]
impl_block_str!(
    Policy<Pk>,
    /// Helper function for `from_tree` to parse subexpressions with
    /// names of the form x@y
    fn from_tree_prob(top: &expression::Tree, allow_prob: bool,)
        -> Result<(usize, Policy<Pk>), Error>
    {
        let frag_prob;
        let frag_name;
        let mut name_split = top.name.split('@');
        match (name_split.next(), name_split.next(), name_split.next()) {
            (None, _, _) => {
                frag_prob = 1;
                frag_name = "";
            }
            (Some(name), None, _) => {
                frag_prob = 1;
                frag_name = name;
            }
            (Some(prob), Some(name), None) => {
                if !allow_prob {
                    return Err(Error::AtOutsideOr(top.name.to_owned()));
                }
                frag_prob = expression::parse_num(prob)? as usize;
                frag_name = name;
            }
            (Some(_), Some(_), Some(_)) => {
                return Err(Error::MultiColon(top.name.to_owned()));
            }
        }
        match (frag_name, top.args.len() as u32) {
            ("UNSATISFIABLE", 0) => Ok(Policy::Unsatisfiable),
            ("TRIVIAL", 0) => Ok(Policy::Trivial),
            ("pk", 1) => expression::terminal(&top.args[0], |pk| Pk::from_str(pk).map(Policy::Key)),
            ("after", 1) => {
                let num = expression::terminal(&top.args[0], expression::parse_num)?;
                if num > 2u32.pow(31) {
                    return Err(Error::PolicyError(PolicyError::TimeTooFar));
                } else if num == 0 {
                    return Err(Error::PolicyError(PolicyError::ZeroTime));
                }
                Ok(Policy::after(num))
            }
            ("older", 1) => {
                let num = expression::terminal(&top.args[0], expression::parse_num)?;
                if num > 2u32.pow(31) {
                    return Err(Error::PolicyError(PolicyError::TimeTooFar));
                } else if num == 0 {
                    return Err(Error::PolicyError(PolicyError::ZeroTime));
                }
                Ok(Policy::older(num))
            }
            ("sha256", 1) => expression::terminal(&top.args[0], |x| {
                <Pk::Sha256 as core::str::FromStr>::from_str(x).map(Policy::Sha256)
            }),
            ("hash256", 1) => expression::terminal(&top.args[0], |x| {
                <Pk::Hash256 as core::str::FromStr>::from_str(x).map(Policy::Hash256)
            }),
            ("ripemd160", 1) => expression::terminal(&top.args[0], |x| {
                <Pk::Ripemd160 as core::str::FromStr>::from_str(x).map(Policy::Ripemd160)
            }),
            ("hash160", 1) => expression::terminal(&top.args[0], |x| {
                <Pk::Hash160 as core::str::FromStr>::from_str(x).map(Policy::Hash160)
            }),
            ("and", _) => {
                if top.args.len() != 2 {
                    return Err(Error::PolicyError(PolicyError::NonBinaryArgAnd));
                }
                let mut subs = Vec::with_capacity(top.args.len());
                for arg in &top.args {
                    subs.push(Policy::from_tree(arg)?);
                }
                Ok(Policy::And(subs))
            }
            ("or", _) => {
                if top.args.len() != 2 {
                    return Err(Error::PolicyError(PolicyError::NonBinaryArgOr));
                }
                let mut subs = Vec::with_capacity(top.args.len());
                for arg in &top.args {
                    subs.push(Policy::from_tree_prob(arg, true)?);
                }
                Ok(Policy::Or(subs))
            }
            ("thresh", nsubs) => {
                if top.args.is_empty() || !top.args[0].args.is_empty() {
                    return Err(Error::PolicyError(PolicyError::IncorrectThresh));
                }

                let thresh = expression::parse_num(top.args[0].name)?;
                if thresh >= nsubs || thresh == 0 {
                    return Err(Error::PolicyError(PolicyError::IncorrectThresh));
                }

                let mut subs = Vec::with_capacity(top.args.len() - 1);
                for arg in &top.args[1..] {
                    subs.push(Policy::from_tree(arg)?);
                }
                Ok(Policy::Threshold(thresh as usize, subs))
            }
            _ => Err(errstr(top.name)),
        }
        .map(|res| (frag_prob, res))
    }
);

impl_from_tree!(
    Policy<Pk>,
    fn from_tree(top: &expression::Tree) -> Result<Policy<Pk>, Error> {
        Policy::from_tree_prob(top, false).map(|(_, result)| result)
    }
);

/// Create a Huffman Tree from compiled [Miniscript] nodes
#[cfg(feature = "compiler")]
fn with_huffman_tree<Pk: MiniscriptKey>(
    ms: Vec<(OrdF64, Miniscript<Pk, Tap>)>,
) -> Result<TapTree<Pk>, Error> {
    let mut node_weights = BinaryHeap::<(Reverse<OrdF64>, TapTree<Pk>)>::new();
    for (prob, script) in ms {
        node_weights.push((Reverse(prob), TapTree::Leaf(Arc::new(script))));
    }
    if node_weights.is_empty() {
        return Err(errstr("Empty Miniscript compilation"));
    }
    while node_weights.len() > 1 {
        let (p1, s1) = node_weights.pop().expect("len must atleast be two");
        let (p2, s2) = node_weights.pop().expect("len must atleast be two");

        let p = (p1.0).0 + (p2.0).0;
        node_weights.push((
            Reverse(OrdF64(p)),
            TapTree::Tree(Arc::from(s1), Arc::from(s2)),
        ));
    }

    debug_assert!(node_weights.len() == 1);
    let node = node_weights
        .pop()
        .expect("huffman tree algorithm is broken")
        .1;
    Ok(node)
}

/// Enumerate a [Thresh][`Policy::Threshold`](k, ..n..) into `n` different thresh.
///
/// ## Strategy
///
/// `thresh(k, x_1...x_n) := thresh(1, thresh(k, x_2...x_n), thresh(k, x_1x_3...x_n), ...., thresh(k, x_1...x_{n-1}))`
/// by the simple argument that choosing `k` conditions from `n` available conditions might not contain
/// any one of the conditions exclusively.
#[cfg(feature = "compiler")]
fn generate_combination<Pk: MiniscriptKey>(
    policy_vec: &Vec<Arc<PolicyArc<Pk>>>,
    prob: f64,
    k: usize,
) -> Vec<(f64, Arc<PolicyArc<Pk>>)> {
    debug_assert!(k <= policy_vec.len());

    let mut ret: Vec<(f64, Arc<PolicyArc<Pk>>)> = vec![];
    for i in 0..policy_vec.len() {
        let policies: Vec<Arc<PolicyArc<Pk>>> = policy_vec
            .iter()
            .enumerate()
            .filter_map(|(j, sub)| if j != i { Some(Arc::clone(sub)) } else { None })
            .collect();
        ret.push((
            prob / policy_vec.len() as f64,
            Arc::new(PolicyArc::Threshold(k, policies)),
        ));
    }
    ret
}

#[cfg(all(test, feature = "compiler"))]
mod compiler_tests {
    use core::str::FromStr;

    use sync::Arc;

    use super::Concrete;
    use crate::policy::concrete::{generate_combination, PolicyArc};
    use crate::prelude::*;

    #[test]
    fn test_gen_comb() {
        let policies: Vec<Concrete<String>> = vec!["pk(A)", "pk(B)", "pk(C)", "pk(D)"]
            .into_iter()
            .map(|st| policy_str!("{}", st))
            .collect();
        let policy_vec = policies
            .into_iter()
            .map(|pol| Arc::new(PolicyArc::from(pol)))
            .collect::<Vec<_>>();

        let combinations = generate_combination(&policy_vec, 1.0, 2);

        let comb_a: Vec<Arc<PolicyArc<String>>> = vec![
            policy_str!("pk(B)"),
            policy_str!("pk(C)"),
            policy_str!("pk(D)"),
        ]
        .into_iter()
        .map(|pol| Arc::new(PolicyArc::from(pol)))
        .collect();
        let comb_b: Vec<Arc<PolicyArc<String>>> = vec![
            policy_str!("pk(A)"),
            policy_str!("pk(C)"),
            policy_str!("pk(D)"),
        ]
        .into_iter()
        .map(|pol| Arc::new(PolicyArc::from(pol)))
        .collect();
        let comb_c: Vec<Arc<PolicyArc<String>>> = vec![
            policy_str!("pk(A)"),
            policy_str!("pk(B)"),
            policy_str!("pk(D)"),
        ]
        .into_iter()
        .map(|pol| Arc::new(PolicyArc::from(pol)))
        .collect();
        let comb_d: Vec<Arc<PolicyArc<String>>> = vec![
            policy_str!("pk(A)"),
            policy_str!("pk(B)"),
            policy_str!("pk(C)"),
        ]
        .into_iter()
        .map(|pol| Arc::new(PolicyArc::from(pol)))
        .collect();
        let expected_comb = vec![comb_a, comb_b, comb_c, comb_d]
            .into_iter()
            .map(|sub_pol| (0.25, Arc::new(PolicyArc::Threshold(2, sub_pol))))
            .collect::<Vec<_>>();
        assert_eq!(combinations, expected_comb);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn for_each_key() {
        let liquid_pol = Policy::<String>::from_str(
            "or(and(older(4096),thresh(2,pk(A),pk(B),pk(C))),thresh(11,pk(F1),pk(F2),pk(F3),pk(F4),pk(F5),pk(F6),pk(F7),pk(F8),pk(F9),pk(F10),pk(F11),pk(F12),pk(F13),pk(F14)))").unwrap();
        let mut count = 0;
        assert!(liquid_pol.for_each_key(|_| { count +=1; true }));
        assert_eq!(count, 17);
    }
}
