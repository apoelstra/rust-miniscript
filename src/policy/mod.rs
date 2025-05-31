// SPDX-License-Identifier: CC0-1.0

//!  Script Policies
//!
//! Tools for representing Bitcoin scriptpubkeys as abstract spending policies.
//! These may be compiled to Miniscript, which contains extra information to
//! describe the exact representation as Bitcoin script.
//!
//! The format represents EC public keys abstractly to allow wallets to replace
//! these with BIP32 paths, pay-to-contract instructions, etc.
//!

#[cfg(feature = "compiler")]
pub mod compiler;
pub mod concrete;
pub mod semantic;

pub use self::concrete::Policy as Concrete;
pub use self::semantic::Policy as Semantic;
use crate::descriptor::Descriptor;
use crate::iter::TreeLike as _;
use crate::miniscript::{Miniscript, ScriptContext};
use crate::sync::Arc;
#[cfg(all(not(feature = "std"), not(test)))]
use crate::Vec;
use crate::{MiniscriptKey, Terminal, Threshold, ValidationError, ValidationParams};

/// Policy entailment algorithm maximum number of terminals allowed.
const ENTAILMENT_MAX_TERMINALS: usize = 20;

/// Trait describing script representations which can be lifted into
/// an abstract policy, by discarding information.
///
/// After Lifting all policies are converted into `KeyHash(Pk::HasH)` to
/// maintain the following invariant(modulo resource limits):
/// `Lift(Concrete) == Concrete -> Miniscript -> Script -> Miniscript -> Semantic`
///
/// Lifting from [`Miniscript`] or [`Descriptor`] can fail if the miniscript
/// contains a timelock combination or if it contains a branch that exceeds
/// resource limits.
///
/// Lifting from concrete policies can fail if the policy contains a timelock
/// combination. It is possible that a concrete policy has some branches that
/// exceed resource limits for any compilation but cannot detect such policies
/// while lifting. Note that our compiler would not succeed for any such
/// policies.
pub trait Liftable<Pk: MiniscriptKey> {
    /// Converts this object into an abstract policy.
    fn lift(&self) -> Result<Semantic<Pk>, ValidationError>;
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Liftable<Pk> for Miniscript<Pk, Ctx> {
    fn lift(&self) -> Result<Semantic<Pk>, ValidationError> {
        // The "sane" rules are pretty-much defined as "the rules that must be followed
        // for lifting to work and analysis to make sense"
        self.validate_once(&ValidationParams::SANE)?;

        let mut stack = vec![];
        for item in self.rtl_post_order_iter() {
            let new_term = match item.node.node {
                Terminal::PkK(ref pk) | Terminal::PkH(ref pk) => {
                    Arc::new(Semantic::Key(pk.clone()))
                }
                Terminal::RawPkH(ref _pkh) => unreachable!("checked by self.validate above"),
                Terminal::After(t) => Arc::new(Semantic::After(t)),
                Terminal::Older(t) => Arc::new(Semantic::Older(t)),
                Terminal::Sha256(ref h) => Arc::new(Semantic::Sha256(h.clone())),
                Terminal::Hash256(ref h) => Arc::new(Semantic::Hash256(h.clone())),
                Terminal::Ripemd160(ref h) => Arc::new(Semantic::Ripemd160(h.clone())),
                Terminal::Hash160(ref h) => Arc::new(Semantic::Hash160(h.clone())),
                Terminal::False => Arc::new(Semantic::Unsatisfiable),
                Terminal::True => Arc::new(Semantic::Trivial),
                Terminal::Alt(..)
                | Terminal::Swap(..)
                | Terminal::Check(..)
                | Terminal::DupIf(..)
                | Terminal::Verify(..)
                | Terminal::NonZero(..)
                | Terminal::ZeroNotEqual(..) => stack.pop().unwrap(),
                Terminal::AndV(..) | Terminal::AndB(..) => Arc::new(Semantic::Thresh(
                    Threshold::and(stack.pop().unwrap(), stack.pop().unwrap()),
                )),
                Terminal::AndOr(..) => Arc::new(Semantic::Thresh(Threshold::or(
                    Arc::new(Semantic::Thresh(Threshold::and(
                        stack.pop().unwrap(),
                        stack.pop().unwrap(),
                    ))),
                    stack.pop().unwrap(),
                ))),
                Terminal::OrB(..) | Terminal::OrD(..) | Terminal::OrC(..) | Terminal::OrI(..) => {
                    Arc::new(Semantic::Thresh(Threshold::or(
                        stack.pop().unwrap(),
                        stack.pop().unwrap(),
                    )))
                }
                Terminal::Thresh(ref thresh) => {
                    Arc::new(Semantic::Thresh(thresh.map_ref(|_| stack.pop().unwrap())))
                }
                Terminal::Multi(ref thresh) => Arc::new(Semantic::Thresh(
                    thresh
                        .map_ref(|key| Arc::new(Semantic::Key(key.clone())))
                        .forget_maximum(),
                )),
                Terminal::MultiA(ref thresh) => Arc::new(Semantic::Thresh(
                    thresh
                        .map_ref(|key| Arc::new(Semantic::Key(key.clone())))
                        .forget_maximum(),
                )),
            };
            stack.push(new_term)
        }
        Ok(Arc::try_unwrap(stack.pop().unwrap()).unwrap().normalized())
    }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Descriptor<Pk> {
    fn lift(&self) -> Result<Semantic<Pk>, ValidationError> {
        match *self {
            Self::Bare(ref bare) => bare.lift(),
            Self::Pkh(ref pkh) => pkh.lift(),
            Self::Wpkh(ref wpkh) => wpkh.lift(),
            Self::Wsh(ref wsh) => wsh.lift(),
            Self::Sh(ref sh) => sh.lift(),
            Self::Tr(ref tr) => tr.lift(),
        }
    }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Semantic<Pk> {
    fn lift(&self) -> Result<Semantic<Pk>, ValidationError> { Ok(self.clone()) }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Concrete<Pk> {
    fn lift(&self) -> Result<Semantic<Pk>, ValidationError> {
        self.validate(&ValidationParams::SANE)?;
        let ret = match *self {
            Self::Unsatisfiable => Semantic::Unsatisfiable,
            Self::Trivial => Semantic::Trivial,
            Self::Key(ref pk) => Semantic::Key(pk.clone()),
            Self::After(t) => Semantic::After(t),
            Self::Older(t) => Semantic::Older(t),
            Self::Sha256(ref h) => Semantic::Sha256(h.clone()),
            Self::Hash256(ref h) => Semantic::Hash256(h.clone()),
            Self::Ripemd160(ref h) => Semantic::Ripemd160(h.clone()),
            Self::Hash160(ref h) => Semantic::Hash160(h.clone()),
            Self::And(ref subs) => {
                let semantic_subs: Result<Vec<Semantic<Pk>>, ValidationError> =
                    subs.iter().map(Liftable::lift).collect();
                let semantic_subs = semantic_subs?.into_iter().map(Arc::new).collect();
                Semantic::Thresh(Threshold::new(2, semantic_subs).unwrap())
            }
            Self::Or(ref subs) => {
                let semantic_subs: Result<Vec<Semantic<Pk>>, ValidationError> =
                    subs.iter().map(|(_p, sub)| sub.lift()).collect();
                let semantic_subs = semantic_subs?.into_iter().map(Arc::new).collect();
                Semantic::Thresh(Threshold::new(1, semantic_subs).unwrap())
            }
            Self::Thresh(ref thresh) => {
                Semantic::Thresh(thresh.translate_ref(|sub| Liftable::lift(sub).map(Arc::new))?)
            }
        }
        .normalized();
        Ok(ret)
    }
}
impl<Pk: MiniscriptKey> Liftable<Pk> for Arc<Concrete<Pk>> {
    fn lift(&self) -> Result<Semantic<Pk>, ValidationError> { self.as_ref().lift() }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::*;
    #[cfg(feature = "compiler")]
    use crate::descriptor::Tr;
    use crate::miniscript::context::Segwitv0;
    use crate::prelude::*;
    use crate::RelLockTime;
    #[cfg(feature = "compiler")]
    use crate::{descriptor::TapTree, Tap};

    type ConcretePol = Concrete<String>;
    type SemanticPol = Semantic<String>;

    fn concrete_policy_rtt(s: &str) {
        let conc = ConcretePol::from_str(s).unwrap();
        let output = conc.to_string();
        assert_eq!(s.to_lowercase(), output.to_lowercase());
    }

    fn semantic_policy_rtt(s: &str) {
        let sem = SemanticPol::from_str(s).unwrap();
        let output = sem.normalized().to_string();
        assert_eq!(s.to_lowercase(), output.to_lowercase());
    }

    #[test]
    fn test_timelock_validity() {
        // only height
        assert!(ConcretePol::from_str("after(100)").is_ok());
        // only time
        assert!(ConcretePol::from_str("after(1000000000)").is_ok());
        // disjunction
        assert!(ConcretePol::from_str("or(after(1000000000),after(100))").is_ok());
        // conjunction
        assert!(ConcretePol::from_str("and(after(1000000000),after(100))").is_err());
        // thresh with k = 1
        assert!(ConcretePol::from_str("thresh(1,pk(),after(1000000000),after(100))").is_ok());
        // thresh with k = 2
        assert!(ConcretePol::from_str("thresh(2,after(1000000000),after(100),pk())").is_err());
    }

    #[test]
    fn parse_duplicate_pubkeys() {
        assert!(ConcretePol::from_str("or(and(pk(A),pk(B)),and(pk(A),pk(D)))").is_err());
    }

    #[test]
    fn policy_rtt_tests() {
        concrete_policy_rtt("pk()");
        concrete_policy_rtt("or(1@pk(X),1@pk(Y))");
        concrete_policy_rtt("or(99@pk(X),1@pk(Y))");
        concrete_policy_rtt("and(pk(X),or(99@pk(Y),1@older(12960)))");

        semantic_policy_rtt("pk()");
        semantic_policy_rtt("or(pk(X),pk(Y))");
        semantic_policy_rtt("and(pk(X),pk(Y))");

        //fuzzer crashes
        assert!(ConcretePol::from_str("thresh()").is_err());
        assert!(SemanticPol::from_str("thresh(0)").is_err());
        assert!(SemanticPol::from_str("thresh()").is_err());
        concrete_policy_rtt("ripemd160()");
    }

    #[test]
    fn compile_invalid() {
        // Since the root Error does not support Eq type, we have to
        // compare the string representations of the error
        assert_eq!(
            ConcretePol::from_str("thresh(2,pk(),thresh(0))")
                .unwrap_err()
                .to_string(),
            "thresholds in Miniscript must be nonempty",
        );
        assert_eq!(
            ConcretePol::from_str("thresh(2,pk(),thresh(0,pk()))")
                .unwrap_err()
                .to_string(),
            "thresholds in Miniscript must have k > 0",
        );
        assert_eq!(
            ConcretePol::from_str("and(pk())").unwrap_err().to_string(),
            "and must have 2 children, but found 1"
        );
        assert_eq!(
            ConcretePol::from_str("or(pk())").unwrap_err().to_string(),
            "or must have 2 children, but found 1"
        );
        // these weird "unexpected" wrapping of errors will go away in a later PR
        // which rewrites the expression parser
        assert_eq!(
            ConcretePol::from_str("thresh(3,after(0),pk(),pk())")
                .unwrap_err()
                .to_string(),
            "absolute locktimes in Miniscript have a minimum value of 1",
        );

        assert_eq!(
            ConcretePol::from_str("thresh(2,older(2147483650),pk(),pk())")
                .unwrap_err()
                .to_string(),
            "locktime value 2147483650 is not a valid BIP68 relative locktime"
        );
    }

    //https://github.com/apoelstra/rust-miniscript/issues/41
    #[test]
    fn heavy_nest() {
        let policy_string = "thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))";
        ConcretePol::from_str(policy_string).unwrap_err();
    }

    #[test]
    fn lift_andor() {
        let key_a: bitcoin::PublicKey =
            "02d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e"
                .parse()
                .unwrap();
        let key_b: bitcoin::PublicKey =
            "03b506a1dbe57b4bf48c95e0c7d417b87dd3b4349d290d2e7e9ba72c912652d80a"
                .parse()
                .unwrap();

        let ms_str: Miniscript<bitcoin::PublicKey, Segwitv0> =
            format!("andor(multi(1,{}),older(42),c:pk_k({}))", key_a.inner, key_b.inner)
                .parse()
                .unwrap();
        assert_eq!(
            Semantic::Thresh(Threshold::or(
                Arc::new(Semantic::Thresh(Threshold::and(
                    Arc::new(Semantic::Key(key_a)),
                    Arc::new(Semantic::Older(RelLockTime::from_height(42)))
                ))),
                Arc::new(Semantic::Key(key_b))
            )),
            ms_str.lift().unwrap()
        );
    }

    #[test]
    #[cfg(feature = "compiler")]
    fn taproot_compile() {
        // Trivial single-node compilation
        let unspendable_key: String = "UNSPENDABLE".to_string();
        {
            let policy: Concrete<String> = policy_str!("thresh(2,pk(A),pk(B),pk(C),pk(D))");
            let descriptor = policy.compile_tr(Some(unspendable_key.clone())).unwrap();

            let ms_compilation: Miniscript<String, Tap> = ms_str!("multi_a(2,A,B,C,D)");
            let tree: TapTree<String> = TapTree::leaf(ms_compilation);
            let expected_descriptor =
                Descriptor::new_tr(unspendable_key.clone(), Some(tree)).unwrap();
            assert_eq!(descriptor, expected_descriptor);
        }

        // Trivial multi-node compilation
        {
            let policy: Concrete<String> = policy_str!("or(and(pk(A),pk(B)),and(pk(C),pk(D)))");
            let descriptor = policy.compile_tr(Some(unspendable_key.clone())).unwrap();

            let left_ms_compilation: Miniscript<String, Tap> = ms_str!("and_v(v:pk(C),pk(D))");
            let right_ms_compilation: Miniscript<String, Tap> = ms_str!("and_v(v:pk(A),pk(B))");

            let left = TapTree::leaf(left_ms_compilation);
            let right = TapTree::leaf(right_ms_compilation);
            let tree = TapTree::combine(left, right).unwrap();

            let expected_descriptor =
                Descriptor::new_tr(unspendable_key.clone(), Some(tree)).unwrap();
            assert_eq!(descriptor, expected_descriptor);
        }

        // Non-trivial multi-node compilation
        {
            let node_policies = [
                "and(pk(A),pk(B))",
                "and(pk(C),older(12960))",
                "pk(D)",
                "pk(E)",
                "thresh(3,pk(F),pk(G),pk(H))",
                "and(and(or(2@pk(I),1@pk(J)),or(1@pk(K),20@pk(L))),pk(M))",
                "pk(N)",
            ];

            // Floating-point precision errors cause the minor errors
            let node_probabilities: [f64; 7] =
                [0.12000002, 0.28, 0.08, 0.12, 0.19, 0.18999998, 0.02];

            let policy: Concrete<String> = policy_str!(
                "{}",
                &format!(
                    "or(4@or(3@{},7@{}),6@thresh(1,or(4@{},6@{}),{},or(9@{},1@{})))",
                    node_policies[0],
                    node_policies[1],
                    node_policies[2],
                    node_policies[3],
                    node_policies[4],
                    node_policies[5],
                    node_policies[6]
                )
            );
            let descriptor = policy.compile_tr(Some(unspendable_key.clone())).unwrap();

            let mut sorted_policy_prob = node_policies
                .iter()
                .zip(node_probabilities.iter())
                .collect::<Vec<_>>();
            sorted_policy_prob.sort_by(|a, b| (a.1).partial_cmp(b.1).unwrap());
            let sorted_policies = sorted_policy_prob
                .into_iter()
                .map(|(x, _prob)| x)
                .collect::<Vec<_>>();

            // Generate TapTree leaves compilations from the given sub-policies
            let node_compilations = sorted_policies
                .into_iter()
                .map(|x| {
                    let leaf_policy: Concrete<String> = policy_str!("{}", x);
                    TapTree::leaf(leaf_policy.compile::<Tap>().unwrap())
                })
                .collect::<Vec<_>>();

            // Arrange leaf compilations (acc. to probabilities) using huffman encoding into a TapTree
            let tree = TapTree::combine(
                TapTree::combine(node_compilations[4].clone(), node_compilations[5].clone())
                    .unwrap(),
                TapTree::combine(
                    TapTree::combine(
                        TapTree::combine(
                            node_compilations[0].clone(),
                            node_compilations[1].clone(),
                        )
                        .unwrap(),
                        node_compilations[3].clone(),
                    )
                    .unwrap(),
                    node_compilations[6].clone(),
                )
                .unwrap(),
            )
            .unwrap();

            let expected_descriptor = Descriptor::new_tr("E".to_string(), Some(tree)).unwrap();
            assert_eq!(descriptor, expected_descriptor);
        }
    }

    #[test]
    #[cfg(feature = "compiler")]
    fn experimental_taproot_compile() {
        let unspendable_key = "UNSPEND".to_string();

        {
            let pol = Concrete::<String>::from_str(
                "thresh(7,pk(A),pk(B),pk(C),pk(D),pk(E),pk(F),pk(G),pk(H))",
            )
            .unwrap();
            let desc = pol
                .compile_tr_private_experimental(Some(unspendable_key.clone()))
                .unwrap();
            let expected_desc = Descriptor::Tr(
                Tr::<String>::from_str(
                    "tr(UNSPEND ,{
                {
                    {and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:pk(B),pk(C)),pk(D)),pk(E)),pk(F)),pk(G)),pk(H)),and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:pk(A),pk(C)),pk(D)),pk(E)),pk(F)),pk(G)),pk(H))},
                    {and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:pk(A),pk(B)),pk(D)),pk(E)),pk(F)),pk(G)),pk(H)),and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:pk(A),pk(B)),pk(C)),pk(E)),pk(F)),pk(G)),pk(H))}
                },
                {
                    {and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:pk(A),pk(B)),pk(C)),pk(D)),pk(F)),pk(G)),pk(H)),and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:pk(A),pk(B)),pk(C)),pk(D)),pk(E)),pk(G)),pk(H))},
                    {and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:pk(A),pk(B)),pk(C)),pk(D)),pk(E)),pk(F)),pk(H)),and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:and_v(v:pk(A),pk(B)),pk(C)),pk(D)),pk(E)),pk(F)),pk(G))}
                }})"
                    .replace(&['\t', ' ', '\n'][..], "")
                    .as_str(),
                )
                .unwrap(),
            );
            assert_eq!(desc, expected_desc);
        }

        {
            let pol =
                Concrete::<String>::from_str("thresh(3,pk(A),pk(B),pk(C),pk(D),pk(E))").unwrap();
            let desc = pol
                .compile_tr_private_experimental(Some(unspendable_key.clone()))
                .unwrap();
            println!("{}", desc);
            let expected_desc = Descriptor::Tr(
                Tr::<String>::from_str(
                    "tr(UNSPEND,
                    {{
                        {and_v(v:and_v(v:pk(A),pk(D)),pk(E)),and_v(v:and_v(v:pk(A),pk(C)),pk(E))},
                        {and_v(v:and_v(v:pk(A),pk(C)),pk(D)),and_v(v:and_v(v:pk(A),pk(B)),pk(E))}
                    },
                    {
                        {and_v(v:and_v(v:pk(A),pk(B)),pk(D)),and_v(v:and_v(v:pk(A),pk(B)),pk(C))},
                        {
                            {and_v(v:and_v(v:pk(C),pk(D)),pk(E)),and_v(v:and_v(v:pk(B),pk(D)),pk(E))},
                            {and_v(v:and_v(v:pk(B),pk(C)),pk(E)),and_v(v:and_v(v:pk(B),pk(C)),pk(D))}
                    }}})"
                        .replace(&['\t', ' ', '\n'][..], "")
                        .as_str(),
                )
                .unwrap(),
            );
            assert_eq!(desc, expected_desc);
        }
    }
}
