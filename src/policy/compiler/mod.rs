// SPDX-License-Identifier: CC0-1.0

//! # Policy Compiler
//!
//! Optimizing compiler from concrete policies to Miniscript
//!

use core::num::NonZeroU32;
use core::{fmt, mem};
#[cfg(feature = "std")]
use std::error;

use sync::Arc;

use crate::miniscript::context::SigType;
use crate::miniscript::limits::{MAX_PUBKEYS_IN_CHECKSIGADD, MAX_PUBKEYS_PER_MULTISIG};
use crate::miniscript::types::{self, ErrorKind, Type};
use crate::miniscript::ScriptContext;
use crate::policy::Concrete;
use crate::prelude::*;
use crate::{policy, Miniscript, MiniscriptKey, PositiveF64, Terminal};

type PolicyCache<Pk, Ctx> = BTreeMap<
    (Concrete<Pk>, PositiveF64, Option<PositiveF64>),
    BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
>;
/// Detailed error type for compiler.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum CompilerError {
    /// `And` fragments only support two args.
    NonBinaryArgAnd,
    /// `Or` fragments only support two args.
    NonBinaryArgOr,
    /// Compiler has a top-level spend path that does not require a signature.
    TopLevelSigless,
    /// Non-Malleable compilation  does exists for the given sub-policy.
    ImpossibleNonMalleableCompilation,
    /// At least one satisfaction path in the optimal Miniscript has exceeded
    /// the consensus or standardness limits.
    /// There may exist other miniscripts which are under these limits but the
    /// compiler currently does not find them.
    LimitsExceeded,
    /// In a Taproot compilation, no "unspendable key" was provided and no in-policy
    /// key could be used as an internal key.
    NoInternalKey,
    /// The selected Taproot internal key is uncompressed.
    UncompressedTaprootInternalKey,
    /// A Huffman merge during Taproot compilation would place a leaf beyond
    /// Taproot's maximum tree depth.
    HuffmanTreeDepthExceeded,
    /// When compiling to Taproot, policy had too many Tapleaves
    TooManyTapleaves {
        /// Number of Tapleaves inferred from the policy.
        n: usize,
        /// Maximum allowed number of Tapleaves.
        max: usize,
    },
    /// Native Taproot compilation produced a leaf containing OP_IF/NOTIF.
    IfFragmentInNativeLeaf {
        /// Index of the leaf that contains branching fragments.
        leaf_index: usize,
    },
    ///Policy related errors
    PolicyError(policy::concrete::PolicyError),
}

impl fmt::Display for CompilerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::NonBinaryArgAnd => f.write_str("And policy fragment must take 2 arguments"),
            Self::NonBinaryArgOr => f.write_str("Or policy fragment must take 2 arguments"),
            Self::TopLevelSigless => {
                f.write_str("top-level script has a spend path without signatures")
            }
            Self::ImpossibleNonMalleableCompilation => {
                f.write_str("The compiler could not find any non-malleable compilation")
            }
            Self::LimitsExceeded => f.write_str(
                "At least one spending path has exceeded the standardness or consensus limits",
            ),
            Self::NoInternalKey => f.write_str("Taproot compilation had no internal key available"),
            Self::UncompressedTaprootInternalKey => {
                f.write_str("Taproot compilation selected an uncompressed internal key")
            }
            Self::HuffmanTreeDepthExceeded => {
                f.write_str("Taproot Huffman tree construction would exceed maximum depth 128")
            }
            Self::TooManyTapleaves { n, max } => {
                write!(f, "Policy had too many Tapleaves (found {}, maximum {})", n, max)
            }
            Self::IfFragmentInNativeLeaf { leaf_index } => {
                write!(
                    f,
                    "native Taproot compilation produced a leaf with OP_IF/NOTIF at leaf index {}; \
                     try increasing max_leaves",
                    leaf_index
                )
            }
            Self::PolicyError(ref e) => fmt::Display::fmt(e, f),
        }
    }
}

fn best_compilations_or<Pk: MiniscriptKey, Ctx: ScriptContext>(
    ret: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    policy_cache: &mut PolicyCache<Pk, Ctx>,
    policy: &Concrete<Pk>,
    subs: &[(NonZeroU32, Arc<Concrete<Pk>>)],
    sat_prob: PositiveF64,
    dissat_prob: Option<PositiveF64>,
) -> Result<(), CompilerError> {
    let total = PositiveF64::from(subs[0].0) + PositiveF64::from(subs[1].0);
    let lw = PositiveF64::from(subs[0].0) / total;
    let rw = PositiveF64::from(subs[1].0) / total;

    //and-or
    let mut insert_ternary = |policy_cache: &mut _,
                              a: &BTreeMap<_, _>,
                              b: &BTreeMap<_, _>,
                              c: &BTreeMap<_, _>,
                              lw: PositiveF64,
                              rw: PositiveF64|
     -> Result<(), CompilerError> {
        for a in a.values() {
            for b in b.values() {
                for c in c.values() {
                    if let Ok(new_ext) = AstElemExt::and_or(a, b, c, lw, rw) {
                        insert_best_wrapped(
                            policy_cache,
                            policy,
                            ret,
                            new_ext,
                            sat_prob,
                            dissat_prob,
                        )?;
                    }
                }
            }
        }
        Ok(())
    };

    if let (Concrete::And(x), _) = (subs[0].1.as_ref(), subs[1].1.as_ref()) {
        let a1 = best_compilations(
            policy_cache,
            x[0].as_ref(),
            lw * sat_prob,
            Some((rw * sat_prob).conditional_add(dissat_prob)),
        )?;
        let a2 = best_compilations(policy_cache, x[0].as_ref(), lw * sat_prob, None)?;

        let b1 = best_compilations(
            policy_cache,
            x[1].as_ref(),
            lw * sat_prob,
            Some((rw * sat_prob).conditional_add(dissat_prob)),
        )?;
        let b2 = best_compilations(policy_cache, x[1].as_ref(), lw * sat_prob, None)?;

        let c = best_compilations(policy_cache, subs[1].1.as_ref(), rw * sat_prob, dissat_prob)?;

        insert_ternary(policy_cache, &a1, &b2, &c, lw, rw)?;
        insert_ternary(policy_cache, &b1, &a2, &c, lw, rw)?;
    };
    if let (_, Concrete::And(x)) = (&subs[0].1.as_ref(), subs[1].1.as_ref()) {
        let a1 = best_compilations(
            policy_cache,
            x[0].as_ref(),
            rw * sat_prob,
            Some((lw * sat_prob).conditional_add(dissat_prob)),
        )?;
        let a2 = best_compilations(policy_cache, x[0].as_ref(), rw * sat_prob, None)?;

        let b1 = best_compilations(
            policy_cache,
            x[1].as_ref(),
            rw * sat_prob,
            Some((lw * sat_prob).conditional_add(dissat_prob)),
        )?;
        let b2 = best_compilations(policy_cache, x[1].as_ref(), rw * sat_prob, None)?;

        let c = best_compilations(policy_cache, subs[0].1.as_ref(), lw * sat_prob, dissat_prob)?;

        insert_ternary(policy_cache, &a1, &b2, &c, rw, lw)?;
        insert_ternary(policy_cache, &b1, &a2, &c, rw, lw)?;
    };

    let dissat_probs = |w: PositiveF64| -> Vec<Option<PositiveF64>> {
        vec![
            Some((w * sat_prob).conditional_add(dissat_prob)),
            Some(w * sat_prob),
            dissat_prob,
            None,
        ]
    };

    let mut l_comp = vec![];
    let mut r_comp = vec![];

    for dissat_prob in dissat_probs(rw).iter() {
        let l = best_compilations(policy_cache, subs[0].1.as_ref(), lw * sat_prob, *dissat_prob)?;
        l_comp.push(l);
    }

    for dissat_prob in dissat_probs(lw).iter() {
        let r = best_compilations(policy_cache, subs[1].1.as_ref(), rw * sat_prob, *dissat_prob)?;
        r_comp.push(r);
    }

    let mut insert_binary = |left: &BTreeMap<_, _>,
                             right: &BTreeMap<_, _>,
                             lw: PositiveF64,
                             rw: PositiveF64,
                             combinator: fn(&_, &_, _, _) -> Result<_, _>|
     -> Result<(), CompilerError> {
        for l in left.values() {
            for r in right.values() {
                if let Ok(new_ext) = combinator(l, r, lw, rw) {
                    insert_best_wrapped(policy_cache, policy, ret, new_ext, sat_prob, dissat_prob)?;
                }
            }
        }
        Ok(())
    };

    insert_binary(&l_comp[0], &r_comp[0], lw, rw, AstElemExt::or_b)?;
    insert_binary(&r_comp[0], &l_comp[0], rw, lw, AstElemExt::or_b)?;
    insert_binary(&l_comp[0], &r_comp[2], lw, rw, AstElemExt::or_d)?;
    insert_binary(&r_comp[0], &l_comp[2], rw, lw, AstElemExt::or_d)?;
    insert_binary(&l_comp[1], &r_comp[3], lw, rw, AstElemExt::or_c)?;
    insert_binary(&r_comp[1], &l_comp[3], rw, lw, AstElemExt::or_c)?;
    insert_binary(&l_comp[2], &r_comp[3], lw, rw, AstElemExt::or_i)?;
    insert_binary(&r_comp[2], &l_comp[3], rw, lw, AstElemExt::or_i)?;
    insert_binary(&l_comp[3], &r_comp[2], lw, rw, AstElemExt::or_i)?;
    insert_binary(&r_comp[3], &l_comp[2], rw, lw, AstElemExt::or_i)?;

    Ok(())
}

#[cfg(feature = "std")]
impl error::Error for CompilerError {
    fn cause(&self) -> Option<&dyn error::Error> {
        use self::CompilerError::*;

        match self {
            NonBinaryArgAnd
            | NonBinaryArgOr
            | TopLevelSigless
            | ImpossibleNonMalleableCompilation
            | LimitsExceeded
            | NoInternalKey
            | UncompressedTaprootInternalKey
            | HuffmanTreeDepthExceeded
            | TooManyTapleaves { .. }
            | IfFragmentInNativeLeaf { .. } => None,
            PolicyError(e) => Some(e),
        }
    }
}

#[doc(hidden)]
impl From<policy::concrete::PolicyError> for CompilerError {
    fn from(e: policy::concrete::PolicyError) -> Self { Self::PolicyError(e) }
}

/// Compilation key: This represents the state of the best possible compilation
/// of a given policy(implicitly keyed).
#[derive(Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
struct CompilationKey {
    /// The type of the compilation result
    ty: Type,

    /// Whether that result cannot be easily converted into verify form.
    /// This is exactly the opposite of has_free_verify in the data-types.
    /// This is required in cases where it is important to distinguish between
    /// two Compilation of the same-type: one of which is expensive to verify
    /// and the other is not.
    expensive_verify: bool,

    /// The probability of dissatisfaction of the compilation of the policy. Note
    /// that all possible compilations of a (sub)policy have the same sat-prob
    /// and only differ in dissat_prob.
    dissat_prob: Option<PositiveF64>,
}

impl CompilationKey {
    /// A Compilation key subtype of another if the type if subtype and other
    /// attributes are equal
    fn is_subtype(self, other: Self) -> bool {
        self.ty.is_subtype(other.ty)
            && self.expensive_verify == other.expensive_verify
            && self.dissat_prob == other.dissat_prob
    }

    /// Helper to create compilation key from components
    fn from_type(ty: Type, expensive_verify: bool, dissat_prob: Option<PositiveF64>) -> Self {
        Self { ty, expensive_verify, dissat_prob }
    }
}

#[derive(Copy, Clone, Debug)]
struct CompilerExtData {
    /// The number of bytes needed to satisfy the fragment in segwit format
    /// (total length of all witness pushes, plus their own length prefixes)
    sat_cost: f64,
    /// The number of bytes needed to dissatisfy the fragment in segwit format
    /// (total length of all witness pushes, plus their own length prefixes)
    /// for fragments that can be dissatisfied without failing the script.
    dissat_cost: Option<f64>,
}

impl CompilerExtData {
    const TRUE: Self = Self { sat_cost: 0.0, dissat_cost: None };

    const FALSE: Self = Self { sat_cost: f64::MAX, dissat_cost: Some(0.0) };

    fn pk_k<Ctx: ScriptContext>() -> Self {
        Self {
            sat_cost: match Ctx::sig_type() {
                SigType::Ecdsa => 73.0,
                SigType::Schnorr => 1.0 /* <var_int> */ + 64.0 /* sig */ + 1.0, /* <sighash_type> */
            },
            dissat_cost: Some(1.0),
        }
    }

    fn pk_h<Ctx: ScriptContext>() -> Self {
        Self {
            sat_cost: match Ctx::sig_type() {
                SigType::Ecdsa => 73.0 + 34.0,
                SigType::Schnorr => 66.0 + 33.0,
            },
            dissat_cost: Some(
                1.0 + match Ctx::sig_type() {
                    SigType::Ecdsa => 34.0,
                    SigType::Schnorr => 33.0,
                },
            ),
        }
    }

    fn multi(k: usize) -> Self {
        Self { sat_cost: 1.0 + 73.0 * k as f64, dissat_cost: Some(1.0 * (k + 1) as f64) }
    }

    fn multi_a(k: usize, n: usize) -> Self {
        Self {
            sat_cost: 66.0 * k as f64 + (n - k) as f64,
            dissat_cost: Some(n as f64), /* <w_n> ... <w_1> := 0x00 ... 0x00 (n times) */
        }
    }

    fn hash() -> Self { Self { sat_cost: 33.0, dissat_cost: Some(33.0) } }

    fn time() -> Self { Self { sat_cost: 0.0, dissat_cost: None } }

    fn cast_alt(self) -> Self { Self { sat_cost: self.sat_cost, dissat_cost: self.dissat_cost } }

    fn cast_swap(self) -> Self { Self { sat_cost: self.sat_cost, dissat_cost: self.dissat_cost } }

    fn cast_check(self) -> Self { Self { sat_cost: self.sat_cost, dissat_cost: self.dissat_cost } }

    fn cast_dupif(self) -> Self { Self { sat_cost: 2.0 + self.sat_cost, dissat_cost: Some(1.0) } }

    fn cast_verify(self) -> Self { Self { sat_cost: self.sat_cost, dissat_cost: None } }

    fn cast_nonzero(self) -> Self { Self { sat_cost: self.sat_cost, dissat_cost: Some(1.0) } }

    fn cast_zeronotequal(self) -> Self {
        Self { sat_cost: self.sat_cost, dissat_cost: self.dissat_cost }
    }

    fn cast_true(self) -> Self { Self { sat_cost: self.sat_cost, dissat_cost: None } }

    fn cast_unlikely(self) -> Self {
        Self { sat_cost: 2.0 + self.sat_cost, dissat_cost: Some(1.0) }
    }

    fn cast_likely(self) -> Self { Self { sat_cost: 1.0 + self.sat_cost, dissat_cost: Some(2.0) } }

    fn and_b(left: Self, right: Self) -> Self {
        Self {
            sat_cost: left.sat_cost + right.sat_cost,
            dissat_cost: match (left.dissat_cost, right.dissat_cost) {
                (Some(l), Some(r)) => Some(l + r),
                _ => None,
            },
        }
    }

    fn and_v(left: Self, right: Self) -> Self {
        Self { sat_cost: left.sat_cost + right.sat_cost, dissat_cost: None }
    }

    fn and_n(left: Self, right: Self) -> Self {
        Self { sat_cost: left.sat_cost + right.sat_cost, dissat_cost: left.dissat_cost }
    }

    fn or_b(l: Self, r: Self, lprob: PositiveF64, rprob: PositiveF64) -> Self {
        Self {
            sat_cost: f64::from(lprob) * (l.sat_cost + r.dissat_cost.unwrap())
                + f64::from(rprob) * (r.sat_cost + l.dissat_cost.unwrap()),
            dissat_cost: Some(l.dissat_cost.unwrap() + r.dissat_cost.unwrap()),
        }
    }

    fn or_d(l: Self, r: Self, lprob: PositiveF64, rprob: PositiveF64) -> Self {
        Self {
            sat_cost: f64::from(lprob) * l.sat_cost
                + f64::from(rprob) * (r.sat_cost + l.dissat_cost.unwrap()),
            dissat_cost: r.dissat_cost.map(|rd| l.dissat_cost.unwrap() + rd),
        }
    }

    fn or_c(l: Self, r: Self, lprob: PositiveF64, rprob: PositiveF64) -> Self {
        Self {
            sat_cost: f64::from(lprob) * l.sat_cost
                + f64::from(rprob) * (r.sat_cost + l.dissat_cost.unwrap()),
            dissat_cost: None,
        }
    }

    #[allow(clippy::manual_map)] // Complex if/let is better as is.
    fn or_i(l: Self, r: Self, lprob: PositiveF64, rprob: PositiveF64) -> Self {
        Self {
            sat_cost: f64::from(lprob) * (2.0 + l.sat_cost) + f64::from(rprob) * (1.0 + r.sat_cost),
            dissat_cost: if let (Some(ldis), Some(rdis)) = (l.dissat_cost, r.dissat_cost) {
                if (2.0 + ldis) > (1.0 + rdis) {
                    Some(1.0 + rdis)
                } else {
                    Some(2.0 + ldis)
                }
            } else if let Some(ldis) = l.dissat_cost {
                Some(2.0 + ldis)
            } else if let Some(rdis) = r.dissat_cost {
                Some(1.0 + rdis)
            } else {
                None
            },
        }
    }

    fn and_or(a: Self, b: Self, c: Self, lprob: PositiveF64, rprob: PositiveF64) -> Self {
        let adis = a
            .dissat_cost
            .expect("BUG: and_or first arg(a) must be dissatisfiable");
        Self {
            sat_cost: f64::from(lprob) * (a.sat_cost + b.sat_cost)
                + f64::from(rprob) * (adis + c.sat_cost),
            dissat_cost: c.dissat_cost.map(|cdis| adis + cdis),
        }
    }

    fn threshold<const N: usize, Pk, S>(thresh: &crate::Threshold<Pk, N>, mut sub_ck: S) -> Self
    where
        S: FnMut(usize) -> Self,
    {
        let k_over_n = f64::from(PositiveF64::k_over_n(thresh));
        let mut sat_cost = 0.0;
        let mut dissat_cost = 0.0;
        for i in 0..thresh.n() {
            let sub = sub_ck(i);
            sat_cost += sub.sat_cost;
            dissat_cost += sub.dissat_cost.unwrap();
        }
        Self {
            sat_cost: sat_cost * k_over_n + dissat_cost * (1.0 - k_over_n),
            dissat_cost: Some(dissat_cost),
        }
    }
}

/// Miniscript AST fragment with additional data needed by the compiler
#[derive(Clone, Debug)]
struct AstElemExt<Pk: MiniscriptKey, Ctx: ScriptContext> {
    /// The actual Miniscript fragment with type information
    ms: Arc<Miniscript<Pk, Ctx>>,
    /// Its "type" in terms of compiler data
    comp_ext_data: CompilerExtData,
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> AstElemExt<Pk, Ctx> {
    /// Compute a 1-dimensional cost, given a probability of satisfaction
    /// and a probability of dissatisfaction; if `dissat_prob` is `None`
    /// then it is assumed that dissatisfaction never occurs
    fn cost_1d(&self, sat_prob: PositiveF64, dissat_prob: Option<PositiveF64>) -> f64 {
        self.ms.ext.pk_cost as f64
            + self.comp_ext_data.sat_cost * f64::from(sat_prob)
            + match (dissat_prob, self.comp_ext_data.dissat_cost) {
                (Some(prob), Some(cost)) => f64::from(prob) * cost,
                (Some(_), None) => f64::INFINITY,
                (None, Some(_)) => 0.0,
                (None, None) => 0.0,
            }
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> AstElemExt<Pk, Ctx> {
    fn unsatisfiable() -> Self {
        Self { ms: Arc::new(Miniscript::FALSE), comp_ext_data: CompilerExtData::FALSE }
    }

    fn trivial() -> Self {
        Self { ms: Arc::new(Miniscript::TRUE), comp_ext_data: CompilerExtData::TRUE }
    }

    fn pk_h(key: Pk) -> Self {
        Self {
            ms: Arc::new(Miniscript::pk_h(key)),
            comp_ext_data: CompilerExtData::pk_h::<Ctx>(),
        }
    }

    fn pk_k(key: Pk) -> Self {
        Self {
            ms: Arc::new(Miniscript::pk_k(key)),
            comp_ext_data: CompilerExtData::pk_k::<Ctx>(),
        }
    }

    fn after(t: crate::AbsLockTime) -> Self {
        Self { ms: Arc::new(Miniscript::after(t)), comp_ext_data: CompilerExtData::time() }
    }

    fn older(t: crate::RelLockTime) -> Self {
        Self { ms: Arc::new(Miniscript::older(t)), comp_ext_data: CompilerExtData::time() }
    }

    fn sha256(h: Pk::Sha256) -> Self {
        Self { ms: Arc::new(Miniscript::sha256(h)), comp_ext_data: CompilerExtData::hash() }
    }

    fn hash256(h: Pk::Hash256) -> Self {
        Self { ms: Arc::new(Miniscript::hash256(h)), comp_ext_data: CompilerExtData::hash() }
    }

    fn ripemd160(h: Pk::Ripemd160) -> Self {
        Self { ms: Arc::new(Miniscript::ripemd160(h)), comp_ext_data: CompilerExtData::hash() }
    }

    fn hash160(h: Pk::Hash160) -> Self {
        Self { ms: Arc::new(Miniscript::hash160(h)), comp_ext_data: CompilerExtData::hash() }
    }

    fn multi(thresh: crate::Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>) -> Self {
        let k = thresh.k();
        Self {
            ms: Arc::new(Miniscript::multi(thresh)),
            comp_ext_data: CompilerExtData::multi(k),
        }
    }

    fn multi_a(thresh: crate::Threshold<Pk, MAX_PUBKEYS_IN_CHECKSIGADD>) -> Self {
        let k = thresh.k();
        let n = thresh.n();
        Self {
            ms: Arc::new(Miniscript::multi_a(thresh)),
            comp_ext_data: CompilerExtData::multi_a(k, n),
        }
    }

    /// Helper functions to compose two Miniscript fragments, where we assume
    /// by construction that all validation parameters are upheld.
    fn compose_typeck_only(
        term: Terminal<Pk, Ctx>,
    ) -> Result<Arc<Miniscript<Pk, Ctx>>, types::Error> {
        let ty = types::Type::type_check(&term)?;
        let ext = types::ExtData::type_check(&term);
        Ok(Arc::new(Miniscript::from_components_unchecked(term, ty, ext)))
    }

    fn and_b(left: &Self, right: &Self) -> Result<Self, types::Error> {
        Ok(Self {
            ms: Self::compose_typeck_only(Terminal::AndB(
                Arc::clone(&left.ms),
                Arc::clone(&right.ms),
            ))?,
            comp_ext_data: CompilerExtData::and_b(left.comp_ext_data, right.comp_ext_data),
        })
    }

    fn and_v(left: &Self, right: &Self) -> Result<Self, types::Error> {
        Ok(Self {
            ms: Self::compose_typeck_only(Terminal::AndV(
                Arc::clone(&left.ms),
                Arc::clone(&right.ms),
            ))?,
            comp_ext_data: CompilerExtData::and_v(left.comp_ext_data, right.comp_ext_data),
        })
    }

    /// and_n(a,b) == andor(a,b,0) is a conjunction of a and b
    fn and_n(left: &Self, right: &Self) -> Result<Self, types::Error> {
        Ok(Self {
            ms: Self::compose_typeck_only(Terminal::AndOr(
                Arc::clone(&left.ms),
                Arc::clone(&right.ms),
                Arc::new(Miniscript::FALSE),
            ))?,
            comp_ext_data: CompilerExtData::and_n(left.comp_ext_data, right.comp_ext_data),
        })
    }

    fn and_or(
        a: &Self,
        b: &Self,
        c: &Self,
        l_weight: PositiveF64,
        r_weight: PositiveF64,
    ) -> Result<Self, types::Error> {
        Ok(Self {
            ms: Self::compose_typeck_only(Terminal::AndOr(
                Arc::clone(&a.ms),
                Arc::clone(&b.ms),
                Arc::clone(&c.ms),
            ))?,
            comp_ext_data: CompilerExtData::and_or(
                a.comp_ext_data,
                b.comp_ext_data,
                c.comp_ext_data,
                l_weight,
                r_weight,
            ),
        })
    }

    fn or_b(
        left: &Self,
        right: &Self,
        l_weight: PositiveF64,
        r_weight: PositiveF64,
    ) -> Result<Self, types::Error> {
        Ok(Self {
            ms: Self::compose_typeck_only(Terminal::OrB(
                Arc::clone(&left.ms),
                Arc::clone(&right.ms),
            ))?,
            comp_ext_data: CompilerExtData::or_b(
                left.comp_ext_data,
                right.comp_ext_data,
                l_weight,
                r_weight,
            ),
        })
    }

    fn or_d(
        left: &Self,
        right: &Self,
        l_weight: PositiveF64,
        r_weight: PositiveF64,
    ) -> Result<Self, types::Error> {
        Ok(Self {
            ms: Self::compose_typeck_only(Terminal::OrD(
                Arc::clone(&left.ms),
                Arc::clone(&right.ms),
            ))?,
            comp_ext_data: CompilerExtData::or_d(
                left.comp_ext_data,
                right.comp_ext_data,
                l_weight,
                r_weight,
            ),
        })
    }

    fn or_c(
        left: &Self,
        right: &Self,
        l_weight: PositiveF64,
        r_weight: PositiveF64,
    ) -> Result<Self, types::Error> {
        Ok(Self {
            ms: Self::compose_typeck_only(Terminal::OrC(
                Arc::clone(&left.ms),
                Arc::clone(&right.ms),
            ))?,
            comp_ext_data: CompilerExtData::or_c(
                left.comp_ext_data,
                right.comp_ext_data,
                l_weight,
                r_weight,
            ),
        })
    }

    fn or_i(
        left: &Self,
        right: &Self,
        l_weight: PositiveF64,
        r_weight: PositiveF64,
    ) -> Result<Self, types::Error> {
        Ok(Self {
            ms: Self::compose_typeck_only(Terminal::OrI(
                Arc::clone(&left.ms),
                Arc::clone(&right.ms),
            ))?,
            comp_ext_data: CompilerExtData::or_i(
                left.comp_ext_data,
                right.comp_ext_data,
                l_weight,
                r_weight,
            ),
        })
    }
}

/// Different types of casts possible for each node.
#[allow(clippy::type_complexity)]
#[derive(Copy, Clone)]
struct Cast<Pk: MiniscriptKey, Ctx: ScriptContext> {
    node: fn(Arc<Miniscript<Pk, Ctx>>) -> Terminal<Pk, Ctx>,
    ast_type: fn(types::Type) -> Result<types::Type, ErrorKind>,
    ext_data: fn(types::ExtData) -> types::ExtData,
    comp_ext_data: fn(CompilerExtData) -> CompilerExtData,
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Cast<Pk, Ctx> {
    fn cast(&self, ast: &AstElemExt<Pk, Ctx>) -> Result<AstElemExt<Pk, Ctx>, ErrorKind> {
        Ok(AstElemExt {
            ms: Arc::new(Miniscript::from_components_unchecked(
                (self.node)(Arc::clone(&ast.ms)),
                (self.ast_type)(ast.ms.ty)?,
                (self.ext_data)(ast.ms.ext),
            )),
            comp_ext_data: (self.comp_ext_data)(ast.comp_ext_data),
        })
    }
}

fn all_casts<Pk: MiniscriptKey, Ctx: ScriptContext>() -> [Cast<Pk, Ctx>; 10] {
    [
        Cast {
            ext_data: types::ExtData::cast_check,
            node: Terminal::Check,
            ast_type: types::Type::cast_check,
            comp_ext_data: CompilerExtData::cast_check,
        },
        Cast {
            ext_data: types::ExtData::cast_dupif,
            node: Terminal::DupIf,
            ast_type: types::Type::cast_dupif,
            comp_ext_data: CompilerExtData::cast_dupif,
        },
        Cast {
            ext_data: types::ExtData::cast_likely,
            node: |ms| Terminal::OrI(Arc::new(Miniscript::FALSE), ms),
            ast_type: types::Type::cast_likely,
            comp_ext_data: CompilerExtData::cast_likely,
        },
        Cast {
            ext_data: types::ExtData::cast_unlikely,
            node: |ms| Terminal::OrI(ms, Arc::new(Miniscript::FALSE)),
            ast_type: types::Type::cast_unlikely,
            comp_ext_data: CompilerExtData::cast_unlikely,
        },
        Cast {
            ext_data: types::ExtData::cast_verify,
            node: Terminal::Verify,
            ast_type: types::Type::cast_verify,
            comp_ext_data: CompilerExtData::cast_verify,
        },
        Cast {
            ext_data: types::ExtData::cast_nonzero,
            node: Terminal::NonZero,
            ast_type: types::Type::cast_nonzero,
            comp_ext_data: CompilerExtData::cast_nonzero,
        },
        Cast {
            ext_data: types::ExtData::cast_true,
            node: |ms| Terminal::AndV(ms, Arc::new(Miniscript::TRUE)),
            ast_type: types::Type::cast_true,
            comp_ext_data: CompilerExtData::cast_true,
        },
        Cast {
            ext_data: types::ExtData::cast_swap,
            node: Terminal::Swap,
            ast_type: types::Type::cast_swap,
            comp_ext_data: CompilerExtData::cast_swap,
        },
        Cast {
            node: Terminal::Alt,
            ast_type: types::Type::cast_alt,
            ext_data: types::ExtData::cast_alt,
            comp_ext_data: CompilerExtData::cast_alt,
        },
        Cast {
            ext_data: types::ExtData::cast_zeronotequal,
            node: Terminal::ZeroNotEqual,
            ast_type: types::Type::cast_zeronotequal,
            comp_ext_data: CompilerExtData::cast_zeronotequal,
        },
    ]
}

/// Insert an element into the global map and return whether it got inserted
/// If there is any element which is already better than current element
/// (by subtyping rules), then don't process the element and return `False`.
/// Otherwise, if the element got inserted into the map, return `True` to inform
/// the caller that the cast closure of this element must also be inserted into
/// the map.
/// In general, we maintain the invariant that if anything is inserted into the
/// map, it's cast closure must also be considered for best compilations.
fn insert_elem<Pk: MiniscriptKey, Ctx: ScriptContext>(
    map: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    elem: AstElemExt<Pk, Ctx>,
    sat_prob: PositiveF64,
    dissat_prob: Option<PositiveF64>,
) -> bool {
    // We check before compiling that non-malleable satisfactions exist, and it appears that
    // there are no cases when malleable satisfactions beat non-malleable ones (and if there
    // are, we don't want to use them). Anyway, detect these and early return.
    if !elem.ms.ty.mall.is_non_malleable() {
        return false;
    }

    if Ctx::check_local_validity(&elem.ms).is_err() {
        return false;
    }

    let elem_cost = elem.cost_1d(sat_prob, dissat_prob);

    let elem_key = CompilationKey::from_type(elem.ms.ty, elem.ms.ext.has_free_verify, dissat_prob);

    // Check whether the new element is worse than any existing element. If there
    // is an element which is a subtype of the current element and has better
    // cost, don't consider this element.
    let is_worse = map.iter().any(|(existing_key, existing_elem)| {
        let existing_elem_cost = existing_elem.cost_1d(sat_prob, dissat_prob);
        existing_key.is_subtype(elem_key) && existing_elem_cost <= elem_cost
    });
    if !is_worse {
        // If the element is not worse any element in the map, remove elements
        // whose subtype is the current element and have worse cost.
        *map = mem::take(map)
            .into_iter()
            .filter(|(existing_key, existing_elem)| {
                let existing_elem_cost = existing_elem.cost_1d(sat_prob, dissat_prob);
                !(elem_key.is_subtype(*existing_key) && existing_elem_cost >= elem_cost)
            })
            .collect();
        map.insert(elem_key, elem);
    }
    !is_worse
}

/// Insert the cast-closure of  in the `astelem_ext`. The cast_stack
/// has all the elements whose closure is yet to inserted in the map.
/// A cast-closure refers to trying all possible casts on a particular element
/// if they are better than the current elements in the global map.
///
/// At the start and end of this function, we maintain that the invariant that
/// all map is smallest possible closure of all compilations of a policy with
/// given sat and dissat probabilities.
fn insert_elem_closure<Pk: MiniscriptKey, Ctx: ScriptContext>(
    map: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    astelem_ext: AstElemExt<Pk, Ctx>,
    sat_prob: PositiveF64,
    dissat_prob: Option<PositiveF64>,
) {
    let mut cast_stack: VecDeque<AstElemExt<Pk, Ctx>> = VecDeque::new();
    if insert_elem(map, astelem_ext.clone(), sat_prob, dissat_prob) {
        cast_stack.push_back(astelem_ext);
    }

    let casts: [Cast<Pk, Ctx>; 10] = all_casts::<Pk, Ctx>();
    while !cast_stack.is_empty() {
        let current = cast_stack.pop_front().unwrap();

        for c in &casts {
            if let Ok(new_ext) = c.cast(&current) {
                if insert_elem(map, new_ext.clone(), sat_prob, dissat_prob) {
                    cast_stack.push_back(new_ext);
                }
            }
        }
    }
}

/// Insert the best wrapped compilations of a particular Terminal. If the
/// dissat probability is None, then we directly get the closure of the element
/// Otherwise, some wrappers require the compilation of the policy with dissat
/// `None` because they convert it into a dissat around it.
/// For example, `l` wrapper should it argument it dissat. `None` because it can
/// always dissatisfy the policy outside and it find the better inner compilation
/// given that it may be not be necessary to dissatisfy. For these elements, we
/// apply the wrappers around the element once and bring them into the same
/// dissat probability map and get their closure.
fn insert_best_wrapped<Pk: MiniscriptKey, Ctx: ScriptContext>(
    policy_cache: &mut PolicyCache<Pk, Ctx>,
    policy: &Concrete<Pk>,
    map: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    data: AstElemExt<Pk, Ctx>,
    sat_prob: PositiveF64,
    dissat_prob: Option<PositiveF64>,
) -> Result<(), CompilerError> {
    insert_elem_closure(map, data, sat_prob, dissat_prob);

    if dissat_prob.is_some() {
        let casts: [Cast<Pk, Ctx>; 10] = all_casts::<Pk, Ctx>();

        for c in &casts {
            for x in best_compilations(policy_cache, policy, sat_prob, None)?.values() {
                if let Ok(new_ext) = c.cast(x) {
                    insert_elem_closure(map, new_ext, sat_prob, dissat_prob);
                }
            }
        }
    }
    Ok(())
}

/// Get the best compilations of a policy with a given sat and dissat
/// probabilities. This functions caches the results into a global policy cache.
fn best_compilations<Pk, Ctx>(
    policy_cache: &mut PolicyCache<Pk, Ctx>,
    policy: &Concrete<Pk>,
    sat_prob: PositiveF64,
    dissat_prob: Option<PositiveF64>,
) -> Result<BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>, CompilerError>
where
    Pk: MiniscriptKey,
    Ctx: ScriptContext,
{
    //Check the cache for hits
    if let Some(ret) = policy_cache.get(&(policy.clone(), sat_prob, dissat_prob)) {
        return Ok(ret.clone());
    }

    let mut ret = BTreeMap::new();

    //handy macro for good looking code
    macro_rules! insert_wrap {
        ($x:expr) => {
            insert_best_wrapped(policy_cache, policy, &mut ret, $x, sat_prob, dissat_prob)?
        };
    }

    match *policy {
        Concrete::Unsatisfiable => {
            insert_wrap!(AstElemExt::unsatisfiable());
        }
        Concrete::Trivial => {
            insert_wrap!(AstElemExt::trivial());
        }
        Concrete::Key(ref pk) => {
            insert_wrap!(AstElemExt::pk_h(pk.clone()));
            insert_wrap!(AstElemExt::pk_k(pk.clone()));
        }
        Concrete::After(n) => insert_wrap!(AstElemExt::after(n)),
        Concrete::Older(n) => insert_wrap!(AstElemExt::older(n)),
        Concrete::Sha256(ref hash) => insert_wrap!(AstElemExt::sha256(hash.clone())),
        // Satisfaction-cost + script-cost
        Concrete::Hash256(ref hash) => insert_wrap!(AstElemExt::hash256(hash.clone())),
        Concrete::Ripemd160(ref hash) => insert_wrap!(AstElemExt::ripemd160(hash.clone())),
        Concrete::Hash160(ref hash) => insert_wrap!(AstElemExt::hash160(hash.clone())),
        Concrete::And(ref subs) => {
            assert_eq!(subs.len(), 2, "and takes 2 args");
            let left = best_compilations(policy_cache, subs[0].as_ref(), sat_prob, dissat_prob)?;
            let right = best_compilations(policy_cache, subs[1].as_ref(), sat_prob, dissat_prob)?;
            let q_zero_right = best_compilations(policy_cache, subs[1].as_ref(), sat_prob, None)?;
            let q_zero_left = best_compilations(policy_cache, subs[0].as_ref(), sat_prob, None)?;

            let mut insert_binary = |left: &BTreeMap<_, _>,
                                     right: &BTreeMap<_, _>,
                                     combinator: fn(&_, &_) -> Result<_, _>|
             -> Result<(), CompilerError> {
                for l in left.values() {
                    for r in right.values() {
                        if let Ok(new_ext) = combinator(l, r) {
                            insert_best_wrapped(
                                policy_cache,
                                policy,
                                &mut ret,
                                new_ext,
                                sat_prob,
                                dissat_prob,
                            )?;
                        }
                    }
                }
                Ok(())
            };
            insert_binary(&left, &right, AstElemExt::and_b)?;
            // Do a separate loop with 'l' and 'r' swapped; we could combine the loops,
            // but this would sometimes result in compiling e.g. and(pk(A),pk(B)) into
            // an and with A and B swapped, which is surprising to the user since the
            // cost is the same with or without the swap.
            insert_binary(&right, &left, AstElemExt::and_b)?;
            insert_binary(&left, &right, AstElemExt::and_v)?;
            insert_binary(&right, &left, AstElemExt::and_v)?;
            insert_binary(&left, &q_zero_right, AstElemExt::and_n)?;
            insert_binary(&right, &q_zero_left, AstElemExt::and_n)?;
        }
        Concrete::Or(ref subs) => {
            best_compilations_or(&mut ret, policy_cache, policy, subs, sat_prob, dissat_prob)?;
        }
        Concrete::Thresh(ref thresh) => {
            let n = thresh.n();
            let k_over_n = PositiveF64::k_over_n(thresh);

            let mut sub_ext_data = Vec::with_capacity(n);

            let mut best_es = Vec::with_capacity(n);
            let mut best_ws = Vec::with_capacity(n);

            let mut min_value = (0, f64::INFINITY);

            let total_sat_prob = sat_prob * k_over_n;
            // This match can be written in terms of nested conditional_adds() but seems less clear that way.
            let total_dissat_prob = match (dissat_prob, PositiveF64::one_minus_k_over_n(thresh)) {
                (Some(dp), Some(kn)) => Some(dp + kn * sat_prob),
                (Some(dp), None) => Some(dp),
                (None, Some(kn)) => Some(kn * sat_prob),
                (None, None) => None,
            };

            for (i, ast) in thresh.iter().enumerate() {
                let sp = total_sat_prob;
                let dp = total_dissat_prob;

                let be = best(types::Base::B, policy_cache, ast.as_ref(), sp, dp)?;
                let bw = best(types::Base::W, policy_cache, ast.as_ref(), sp, dp)?;

                let diff = be.cost_1d(sp, dp) - bw.cost_1d(sp, dp);
                best_es.push((be.comp_ext_data, be));
                best_ws.push((bw.comp_ext_data, bw));

                if diff < min_value.1 {
                    min_value.0 = i;
                    min_value.1 = diff;
                }
            }

            // Construct the threshold, swapping the index of the best (i.e. most
            // advantageous to be a E vs a W) entry into the first slot so that
            // it can be an E.
            let mut idx = 0;
            let ast = Terminal::Thresh(thresh.map_ref(|_| {
                let ret = if idx == 0 {
                    // swap 0 with min_value...
                    sub_ext_data.push(best_es[min_value.0].0);
                    Arc::clone(&best_es[min_value.0].1.ms)
                } else if idx == min_value.0 {
                    // swap min_value with 0...
                    sub_ext_data.push(best_ws[0].0);
                    Arc::clone(&best_ws[0].1.ms)
                } else {
                    // ...and leave everything else unchanged
                    sub_ext_data.push(best_ws[idx].0);
                    Arc::clone(&best_ws[idx].1.ms)
                };
                idx += 1;
                ret
            }));

            if let Ok(ms) = Miniscript::from_ast(ast) {
                let ast_ext = AstElemExt {
                    ms: Arc::new(ms),
                    comp_ext_data: CompilerExtData::threshold(thresh, |i| sub_ext_data[i]),
                };
                insert_wrap!(ast_ext);
            }

            let key_count = thresh
                .iter()
                .filter(|s| matches!(***s, Concrete::Key(_)))
                .count();
            if key_count == thresh.n() {
                let pk_thresh = thresh.map_ref(|s| {
                    if let Concrete::Key(ref pk) = **s {
                        Pk::clone(pk)
                    } else {
                        unreachable!()
                    }
                });
                match Ctx::sig_type() {
                    SigType::Schnorr => {
                        if let Ok(pk_thresh) = pk_thresh.set_maximum() {
                            insert_wrap!(AstElemExt::multi_a(pk_thresh))
                        }
                    }
                    SigType::Ecdsa => {
                        if let Ok(pk_thresh) = pk_thresh.set_maximum() {
                            insert_wrap!(AstElemExt::multi(pk_thresh))
                        }
                    }
                }
            }
            if thresh.is_and() {
                let mut it = thresh.iter();
                let mut policy = it.next().expect("No sub policy in thresh() ?").clone();
                policy = it.fold(policy, |acc, pol| Concrete::And(vec![acc, pol.clone()]).into());

                ret = best_compilations(policy_cache, policy.as_ref(), sat_prob, dissat_prob)?;
            }

            // FIXME: Should we also special-case thresh.is_or() ?
        }
    }
    for k in ret.keys() {
        debug_assert_eq!(k.dissat_prob, dissat_prob);
    }
    if ret.is_empty() {
        // The only reason we are discarding elements out of compiler is because
        // compilations exceeded consensus and standardness limits or are non-malleable.
        // If there no possible compilations for any policies regardless of dissat
        // probability then it must have all compilations exceeded consensus or standardness
        // limits because we already checked that policy must have non-malleable compilations
        // before calling this compile function
        Err(CompilerError::LimitsExceeded)
    } else {
        policy_cache.insert((policy.clone(), sat_prob, dissat_prob), ret.clone());
        Ok(ret)
    }
}

/// Obtain the best compilation of for p=1.0 and q=0
pub fn best_compilation<Pk: MiniscriptKey, Ctx: ScriptContext>(
    policy: &Concrete<Pk>,
) -> Result<Miniscript<Pk, Ctx>, CompilerError> {
    let mut policy_cache = PolicyCache::<Pk, Ctx>::new();
    let x = &*best_t(&mut policy_cache, policy, PositiveF64::ONE, None)?.ms;
    match x.ty.mall {
        // Malleable candidates are never inserted into the compilation map, so
        // reaching this is a bug rather than a property of the policy.
        types::Malleability::Malleable => Err(CompilerError::ImpossibleNonMalleableCompilation),
        types::Malleability::NonMalleable { signed: false, .. } => {
            Err(CompilerError::TopLevelSigless)
        }
        types::Malleability::NonMalleable { .. } => Ok(x.clone()),
    }
}

/// Obtain the best B expression with given sat and dissat
fn best_t<Pk, Ctx>(
    policy_cache: &mut PolicyCache<Pk, Ctx>,
    policy: &Concrete<Pk>,
    sat_prob: PositiveF64,
    dissat_prob: Option<PositiveF64>,
) -> Result<AstElemExt<Pk, Ctx>, CompilerError>
where
    Pk: MiniscriptKey,
    Ctx: ScriptContext,
{
    best_compilations(policy_cache, policy, sat_prob, dissat_prob)?
        .into_iter()
        .filter(|&(key, _)| key.ty.corr.base == types::Base::B && key.dissat_prob == dissat_prob)
        .map(|(_, val)| val)
        .min_by_key(|ext| PositiveF64::new(ext.cost_1d(sat_prob, dissat_prob)))
        .ok_or(CompilerError::LimitsExceeded)
}

/// Obtain the <basic-type>.deu (e.g. W.deu, B.deu) expression with the given sat and dissat
fn best<Pk, Ctx>(
    basic_type: types::Base,
    policy_cache: &mut PolicyCache<Pk, Ctx>,
    policy: &Concrete<Pk>,
    sat_prob: PositiveF64,
    dissat_prob: Option<PositiveF64>,
) -> Result<AstElemExt<Pk, Ctx>, CompilerError>
where
    Pk: MiniscriptKey,
    Ctx: ScriptContext,
{
    best_compilations(policy_cache, policy, sat_prob, dissat_prob)?
        .into_iter()
        .filter(|(key, val)| {
            key.ty.corr.base == basic_type
                && key.ty.corr.unit
                && val.ms.ty.mall.dissat() == Some(types::Dissat::Unique)
                && key.dissat_prob == dissat_prob
        })
        .map(|(_, val)| val)
        .min_by_key(|ext| PositiveF64::new(ext.cost_1d(sat_prob, dissat_prob)))
        .ok_or(CompilerError::LimitsExceeded)
}

#[cfg(test)]
mod tests {
    use core::num::NonZeroU32;
    use core::str::FromStr;

    use bitcoin::blockdata::{opcodes, script};
    use bitcoin::hashes;

    use super::*;
    use crate::miniscript::{Legacy, Segwitv0, Tap};
    use crate::policy::Liftable;
    use crate::{script_num_size, AbsLockTime, RelLockTime, Threshold, ToPublicKey};

    type SPolicy = Concrete<String>;
    type BPolicy = Concrete<bitcoin::PublicKey>;
    type TapAstElemExt = policy::compiler::AstElemExt<String, Tap>;
    type SegwitMiniScript = Miniscript<bitcoin::PublicKey, Segwitv0>;

    #[allow(unsafe_code)]
    const ONE: NonZeroU32 = unsafe { NonZeroU32::new_unchecked(1) }; // can be NonZeroU32::MIN in 1.70

    fn pubkeys_and_a_sig(n: usize) -> (Vec<bitcoin::PublicKey>, secp256k1::ecdsa::Signature) {
        let mut ret = Vec::with_capacity(n);
        let secp = secp256k1::Secp256k1::new();
        let mut sk = [0; 32];
        for i in 1..n + 1 {
            sk[0] = i as u8;
            sk[1] = (i >> 8) as u8;
            sk[2] = (i >> 16) as u8;

            let pk = bitcoin::PublicKey {
                inner: secp256k1::PublicKey::from_secret_key(
                    &secp,
                    &secp256k1::SecretKey::from_slice(&sk[..]).expect("sk"),
                ),
                compressed: true,
            };
            ret.push(pk);
        }
        let sig = secp.sign_ecdsa(
            &secp256k1::Message::from_digest(sk), // Not a digest but 32 bytes nonetheless.
            &secp256k1::SecretKey::from_slice(&sk[..]).expect("secret key"),
        );
        (ret, sig)
    }

    fn policy_compile_lift_check(s: &str) -> Result<(), CompilerError> {
        let policy = SPolicy::from_str(s).expect("parse");
        let miniscript: Miniscript<String, Segwitv0> = policy.compile()?;

        assert_eq!(policy.lift().unwrap().sorted(), miniscript.lift().unwrap().sorted());
        Ok(())
    }

    #[test]
    fn compile_timelocks() {
        // artificially create a policy that is problematic and try to compile
        let pol: SPolicy = Concrete::And(vec![
            Arc::new(Concrete::Key("A".to_string())),
            Arc::new(Concrete::And(vec![
                Arc::new(Concrete::After(AbsLockTime::from_consensus(9).unwrap())),
                Arc::new(Concrete::After(AbsLockTime::from_consensus(1_000_000_000).unwrap())),
            ])),
        ]);
        assert!(pol.compile::<Segwitv0>().is_err());

        // This should compile
        let pol: SPolicy =
            SPolicy::from_str("and(pk(A),or(and(after(9),pk(B)),and(after(1000000000),pk(C))))")
                .unwrap();
        assert!(pol.compile::<Segwitv0>().is_ok());
    }
    #[test]
    fn compile_basic() {
        assert!(policy_compile_lift_check("pk(A)").is_ok());
        assert_eq!(policy_compile_lift_check("after(9)"), Err(CompilerError::TopLevelSigless));
        assert_eq!(policy_compile_lift_check("older(1)"), Err(CompilerError::TopLevelSigless));
        assert_eq!(
            policy_compile_lift_check(
                "sha256(1111111111111111111111111111111111111111111111111111111111111111)"
            ),
            Err(CompilerError::TopLevelSigless)
        );
        assert!(policy_compile_lift_check("and(pk(A),pk(B))").is_ok());
        assert!(policy_compile_lift_check("or(pk(A),pk(B))").is_ok());
        assert!(policy_compile_lift_check("thresh(2,pk(A),pk(B),pk(C))").is_ok());
        assert!(policy_compile_lift_check("or(thresh(1,pk(A),pk(B)),pk(C))").is_ok());

        assert_eq!(
            policy_compile_lift_check("thresh(2,after(9),after(9),pk(A))"),
            Err(CompilerError::TopLevelSigless)
        );

        assert_eq!(
            policy_compile_lift_check("and(pk(A),or(after(9),after(9)))"),
            Err(CompilerError::ImpossibleNonMalleableCompilation)
        );
    }

    #[test]
    fn compile_q() {
        let policy = SPolicy::from_str("or(1@and(pk(A),pk(B)),127@pk(C))").expect("parsing");
        let compilation: TapAstElemExt =
            best_t(&mut BTreeMap::new(), &policy, PositiveF64::ONE, None).unwrap();

        assert_eq!(compilation.cost_1d(PositiveF64::ONE, None), 87.0 + 67.0390625);
        assert_eq!(policy.lift().unwrap().sorted(), compilation.ms.lift().unwrap().sorted());

        // compile into taproot context to avoid limit errors
        let policy = SPolicy::from_str(
                "and(and(and(or(127@thresh(2,pk(A),pk(B),thresh(2,or(127@pk(A),1@pk(B)),after(100),or(and(pk(C),after(200)),and(pk(D),sha256(66687aadf862bd776c8fc18b8e9f8e20089714856ee233b3902a591d0d5f2925))),pk(E))),1@pk(F)),sha256(66687aadf862bd776c8fc18b8e9f8e20089714856ee233b3902a591d0d5f2925)),or(127@pk(G),1@after(300))),or(127@after(400),pk(H)))"
            ).expect("parsing");
        let compilation: TapAstElemExt =
            best_t(&mut BTreeMap::new(), &policy, PositiveF64::ONE, None).unwrap();

        assert_eq!(compilation.cost_1d(PositiveF64::ONE, None), 433.0 + 275.7909749348958);
        assert_eq!(policy.lift().unwrap().sorted(), compilation.ms.lift().unwrap().sorted());
    }

    #[test]
    #[allow(clippy::needless_range_loop)]
    fn compile_misc() {
        let (keys, signature) = pubkeys_and_a_sig(10);
        let key_pol: Vec<BPolicy> = keys.iter().map(|k| Concrete::Key(*k)).collect();

        let policy: BPolicy = Concrete::Key(keys[0]);
        let ms: SegwitMiniScript = policy.compile().unwrap();
        assert_eq!(
            ms.encode(),
            script::Builder::new()
                .push_key(&keys[0])
                .push_opcode(opcodes::all::OP_CHECKSIG)
                .into_script()
        );

        // CSV reordering trick
        let policy: BPolicy = policy_str!(
            "and(older(10000),thresh(2,pk({}),pk({}),pk({})))",
            keys[5],
            keys[6],
            keys[7]
        );
        let ms: SegwitMiniScript = policy.compile().unwrap();
        assert_eq!(
            ms.encode(),
            script::Builder::new()
                .push_opcode(opcodes::all::OP_PUSHNUM_2)
                .push_key(&keys[5])
                .push_key(&keys[6])
                .push_key(&keys[7])
                .push_opcode(opcodes::all::OP_PUSHNUM_3)
                .push_opcode(opcodes::all::OP_CHECKMULTISIGVERIFY)
                .push_int(10000)
                .push_opcode(opcodes::all::OP_CSV)
                .into_script()
        );

        // Liquid policy
        let policy: BPolicy = Concrete::Or(vec![
            (
                NonZeroU32::new(127).unwrap(),
                Arc::new(Concrete::Thresh(
                    Threshold::from_iter(3, key_pol[0..5].iter().map(|p| (p.clone()).into()))
                        .unwrap(),
                )),
            ),
            (
                NonZeroU32::new(1).unwrap(),
                Arc::new(Concrete::And(vec![
                    Arc::new(Concrete::Older(RelLockTime::from_height(10000).unwrap())),
                    Arc::new(Concrete::Thresh(
                        Threshold::from_iter(2, key_pol[5..8].iter().map(|p| (p.clone()).into()))
                            .unwrap(),
                    )),
                ])),
            ),
        ]);

        let ms: SegwitMiniScript = policy.compile().unwrap();

        let ms_comp_res: Miniscript<bitcoin::PublicKey, Segwitv0> = ms_str!(
            "or_d(multi(3,{},{},{},{},{}),\
             and_v(v:thresh(2,c:pk_h({}),\
             ac:pk_h({}),ac:pk_h({})),older(10000)))",
            keys[0],
            keys[1],
            keys[2],
            keys[3],
            keys[4],
            keys[5],
            keys[6],
            keys[7]
        );

        assert_eq!(ms, ms_comp_res);

        let mut abs = policy.lift().unwrap();
        assert_eq!(abs.n_keys(), 8);
        assert_eq!(abs.minimum_n_keys(), Some(2));
        abs = abs.at_age(RelLockTime::from_height(10000).unwrap().into());
        assert_eq!(abs.n_keys(), 8);
        assert_eq!(abs.minimum_n_keys(), Some(2));
        abs = abs.at_age(RelLockTime::from_height(9999).unwrap().into());
        assert_eq!(abs.n_keys(), 5);
        assert_eq!(abs.minimum_n_keys(), Some(3));
        abs = abs.at_age(RelLockTime::ZERO.into());
        assert_eq!(abs.n_keys(), 5);
        assert_eq!(abs.minimum_n_keys(), Some(3));

        let bitcoinsig = bitcoin::ecdsa::Signature {
            signature,
            sighash_type: bitcoin::sighash::EcdsaSighashType::All,
        };
        let sigvec = bitcoinsig.to_vec();

        let no_sat = BTreeMap::<bitcoin::PublicKey, bitcoin::ecdsa::Signature>::new();
        let mut left_sat = BTreeMap::<bitcoin::PublicKey, bitcoin::ecdsa::Signature>::new();
        let mut right_sat = BTreeMap::<
            hashes::hash160::Hash,
            (bitcoin::PublicKey, bitcoin::ecdsa::Signature),
        >::new();

        for i in 0..5 {
            left_sat.insert(keys[i], bitcoinsig);
        }
        for i in 5..8 {
            right_sat.insert(keys[i].to_pubkeyhash(SigType::Ecdsa), (keys[i], bitcoinsig));
        }

        assert!(ms.satisfy(no_sat).is_err());
        assert!(ms.satisfy(&left_sat).is_ok());
        assert!(ms
            .satisfy((&right_sat, RelLockTime::from_height(10001).unwrap(),))
            .is_ok());
        //timelock not met
        assert!(ms
            .satisfy((&right_sat, RelLockTime::from_height(9999).unwrap()))
            .is_err());

        assert_eq!(
            ms.satisfy((left_sat, RelLockTime::from_height(9999).unwrap()))
                .unwrap(),
            vec![
                // sat for left branch
                vec![],
                sigvec.clone(),
                sigvec.clone(),
                sigvec.clone(),
            ]
        );

        assert_eq!(
            ms.satisfy((right_sat, RelLockTime::from_height(10000).unwrap()))
                .unwrap(),
            vec![
                // sat for right branch
                vec![],
                keys[7].to_bytes(),
                sigvec.clone(),
                keys[6].to_bytes(),
                sigvec.clone(),
                keys[5].to_bytes(),
                // dissat for left branch
                vec![],
                vec![],
                vec![],
                vec![],
            ]
        );
    }

    #[test]
    fn compile_thresh() {
        let (keys, _) = pubkeys_and_a_sig(21);

        // For 3 < n <= 20, thresh should be compiled to a multi no matter the value of k
        for k in 1..4 {
            let small_thresh: BPolicy = policy_str!(
                "thresh({},pk({}),pk({}),pk({}),pk({}))",
                k,
                keys[0],
                keys[1],
                keys[2],
                keys[3]
            );
            let small_thresh_ms: SegwitMiniScript = small_thresh.compile().unwrap();
            let small_thresh_ms_expected: SegwitMiniScript =
                ms_str!("multi({},{},{},{},{})", k, keys[0], keys[1], keys[2], keys[3]);
            assert_eq!(small_thresh_ms, small_thresh_ms_expected);
        }

        // Above 20 keys, thresh is compiled to a combination of and()s if it's a N of N,
        // and to a ms thresh otherwise.
        // k = 1 (or 2) does not compile, see https://github.com/rust-bitcoin/rust-miniscript/issues/114
        for k in &[10, 15, 21] {
            let thresh: Threshold<Arc<Concrete<bitcoin::PublicKey>>, 0> = Threshold::from_iter(
                *k,
                keys.iter().map(|pubkey| Arc::new(Concrete::Key(*pubkey))),
            )
            .unwrap();
            let big_thresh = Concrete::Thresh(thresh);
            let big_thresh_ms: SegwitMiniScript = big_thresh.compile().unwrap();
            if *k == 21 {
                // N * (PUSH + pubkey + CHECKSIGVERIFY)
                assert_eq!(big_thresh_ms.script_size(), keys.len() * (1 + 33 + 1));
            } else {
                // N * (PUSH + pubkey + CHECKSIG + ADD + SWAP) + N EQUAL
                assert_eq!(
                    big_thresh_ms.script_size(),
                    keys.len() * (1 + 33 + 3) + script_num_size(*k) + 1 - 2 // minus one SWAP and one ADD
                );
                let big_thresh_ms_expected = ms_str!(
                "thresh({},pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}),s:pk({}))",
                k, keys[0], keys[1], keys[2], keys[3], keys[4], keys[5], keys[6], keys[7], keys[8], keys[9],keys[10], keys[11], keys[12], keys[13], keys[14], keys[15], keys[16], keys[17], keys[18], keys[19], keys[20]
            );
                assert_eq!(big_thresh_ms, big_thresh_ms_expected);
            };
        }
    }

    #[test]
    fn segwit_limits_1() {
        // Hit the maximum witness script size limit.
        // or(thresh(52, [pubkey; 52]), thresh(52, [pubkey; 52])) results in a 3642-bytes long
        // witness script with only 54 stack elements
        let (keys, _) = pubkeys_and_a_sig(104);
        let keys_a: Vec<Arc<Concrete<bitcoin::PublicKey>>> = keys[..keys.len() / 2]
            .iter()
            .map(|pubkey| Arc::new(Concrete::Key(*pubkey)))
            .collect();
        let keys_b: Vec<Arc<Concrete<bitcoin::PublicKey>>> = keys[keys.len() / 2..]
            .iter()
            .map(|pubkey| Arc::new(Concrete::Key(*pubkey)))
            .collect();

        let thresh_res: Result<SegwitMiniScript, _> = Concrete::Or(vec![
            (ONE, Arc::new(Concrete::Thresh(Threshold::and_n(keys_a)))),
            (ONE, Arc::new(Concrete::Thresh(Threshold::and_n(keys_b)))),
        ])
        .compile();
        let script_size = thresh_res.clone().map(|m| m.script_size());
        assert_eq!(
            thresh_res,
            Err(CompilerError::LimitsExceeded),
            "Compilation succeeded with a witscript size of '{:?}'",
            script_size,
        );
    }

    #[test]
    fn segwit_limits_2() {
        // Hit the maximum witness stack elements limit
        let (keys, _) = pubkeys_and_a_sig(100);
        let keys: Vec<Arc<Concrete<bitcoin::PublicKey>>> = keys
            .iter()
            .map(|pubkey| Arc::new(Concrete::Key(*pubkey)))
            .collect();
        let thresh_res: Result<SegwitMiniScript, _> =
            Concrete::Thresh(Threshold::and_n(keys)).compile();
        let n_elements = thresh_res
            .clone()
            .map(|m| m.max_satisfaction_witness_elements());
        assert_eq!(
            thresh_res,
            Err(CompilerError::LimitsExceeded),
            "Compilation succeeded with '{:?}' elements",
            n_elements,
        );
    }

    #[test]
    fn shared_limits() {
        // Test the maximum number of OPs with a 67-of-68 multisig
        let (keys, _) = pubkeys_and_a_sig(68);
        let thresh = Threshold::from_iter(
            keys.len() - 1,
            keys.iter().map(|pubkey| Arc::new(Concrete::Key(*pubkey))),
        )
        .unwrap();
        let thresh_res: Result<SegwitMiniScript, _> = Concrete::Thresh(thresh).compile();
        let ops_count = thresh_res.clone().map(|m| m.ext.sat_op_count());
        assert_eq!(
            thresh_res,
            Err(CompilerError::LimitsExceeded),
            "Compilation succeeded with '{:?}' OP count (sat)",
            ops_count,
        );
        // For legacy too..
        let (keys, _) = pubkeys_and_a_sig(68);
        let thresh = Threshold::from_iter(
            keys.len() - 1,
            keys.iter().map(|pubkey| Arc::new(Concrete::Key(*pubkey))),
        )
        .unwrap();

        let thresh_res = Concrete::Thresh(thresh).compile::<Legacy>();
        let ops_count = thresh_res.clone().map(|m| m.ext.sat_op_count());
        assert_eq!(
            thresh_res,
            Err(CompilerError::LimitsExceeded),
            "Compilation succeeded with '{:?}' OP count (sat)",
            ops_count,
        );

        // Test that we refuse to compile policies with duplicated keys
        let (keys, _) = pubkeys_and_a_sig(1);
        let key = Arc::new(Concrete::Key(keys[0]));
        let res = Concrete::Or(vec![(ONE, Arc::clone(&key)), (ONE, Arc::clone(&key))])
            .compile::<Segwitv0>();
        assert_eq!(
            res,
            Err(CompilerError::PolicyError(policy::concrete::PolicyError::DuplicatePubKeys))
        );
        // Same for legacy
        let res = Concrete::Or(vec![(ONE, key.clone()), (ONE, key)]).compile::<Legacy>();
        assert_eq!(
            res,
            Err(CompilerError::PolicyError(policy::concrete::PolicyError::DuplicatePubKeys))
        );
    }

    #[test]
    fn compile_tr_thresh() {
        for k in 1..4 {
            let small_thresh: Concrete<String> =
                policy_str!("{}", &format!("thresh({},pk(B),pk(C),pk(D))", k));
            let small_thresh_ms: Miniscript<String, Tap> = small_thresh.compile().unwrap();
            // When k == 3 it is more efficient to use and_v than multi_a
            if k == 3 {
                assert_eq!(
                    small_thresh_ms,
                    ms_str!("and_v(v:and_v(vc:pk_k(B),c:pk_k(C)),c:pk_k(D))")
                );
            } else {
                assert_eq!(small_thresh_ms, ms_str!("multi_a({},B,C,D)", k));
            }
        }
    }

    #[test]
    fn compile_and_n_dissat_cost() {
        // Regression: if you change the dissat_cost of `and_n` to `None`, this test will fail.
        let policy = SPolicy::from_str(
            "thresh(4,and(or(1@pk(A),1@pk(B)),sha256(H)),pk(C),pk(D),pk(E),pk(F))",
        )
        .unwrap();
        let miniscript: Miniscript<String, Segwitv0> = policy.compile().unwrap();
        let expected: Miniscript<String, Segwitv0> = ms_str!(
            "thresh(4,and_n(or_b(pk(A),s:pk(B)),sha256(H)),s:pk(C),s:pk(D),s:pk(E),s:pk(F))"
        );

        assert_eq!(miniscript, expected);
    }
}
