// SPDX-License-Identifier: CC0-1.0

//! # Extra Node Data for the Policy Compiler

use sync::Arc;

use crate::miniscript::context::SigType;
use crate::miniscript::limits::{MAX_PUBKEYS_IN_CHECKSIGADD, MAX_PUBKEYS_PER_MULTISIG};
use crate::miniscript::types;
use crate::prelude::*;
use crate::{Miniscript, MiniscriptKey, PositiveF64, ScriptContext, Terminal};

/// Miniscript AST fragment with additional data needed by the compiler
#[derive(Clone, Debug)]
pub struct AstElemExt<Pk: MiniscriptKey, Ctx: ScriptContext> {
    /// The actual Miniscript fragment with type information
    pub ms: Arc<Miniscript<Pk, Ctx>>,
    /// The number of bytes needed to satisfy the fragment in segwit format
    /// (total length of all witness pushes, plus their own length prefixes)
    sat_cost: f64,
    /// The number of bytes needed to dissatisfy the fragment in segwit format
    /// (total length of all witness pushes, plus their own length prefixes)
    /// for fragments that can be dissatisfied without failing the script.
    dissat_cost: Option<f64>,
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> AstElemExt<Pk, Ctx> {
    /// Compute a 1-dimensional cost, given a probability of satisfaction
    /// and a probability of dissatisfaction; if `dissat_prob` is `None`
    /// then it is assumed that dissatisfaction never occurs
    pub fn cost_1d(&self, sat_prob: PositiveF64, dissat_prob: Option<PositiveF64>) -> f64 {
        self.ms.ext.pk_cost as f64
            + self.sat_cost * f64::from(sat_prob)
            + match (dissat_prob, self.dissat_cost) {
                (Some(prob), Some(cost)) => f64::from(prob) * cost,
                (Some(_), None) => f64::INFINITY,
                (None, Some(_)) => 0.0,
                (None, None) => 0.0,
            }
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> AstElemExt<Pk, Ctx> {
    pub fn unsatisfiable() -> Self {
        Self { ms: Arc::new(Miniscript::FALSE), sat_cost: f64::MAX, dissat_cost: Some(0.0) }
    }

    pub fn trivial() -> Self {
        Self { ms: Arc::new(Miniscript::TRUE), sat_cost: 0.0, dissat_cost: None }
    }

    pub fn pk_h(key: Pk) -> Self {
        Self {
            ms: Arc::new(Miniscript::pk_h(key)),
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

    pub fn pk_k(key: Pk) -> Self {
        Self {
            ms: Arc::new(Miniscript::pk_k(key)),
            sat_cost: match Ctx::sig_type() {
                SigType::Ecdsa => 73.0,
                SigType::Schnorr => 1.0 /* <var_int> */ + 64.0 /* sig */ + 1.0, /* <sighash_type> */
            },
            dissat_cost: Some(1.0),
        }
    }

    pub fn after(t: crate::AbsLockTime) -> Self {
        Self { ms: Arc::new(Miniscript::after(t)), sat_cost: 0.0, dissat_cost: None }
    }

    pub fn older(t: crate::RelLockTime) -> Self {
        Self { ms: Arc::new(Miniscript::older(t)), sat_cost: 0.0, dissat_cost: None }
    }

    pub fn sha256(h: Pk::Sha256) -> Self {
        Self { ms: Arc::new(Miniscript::sha256(h)), sat_cost: 33.0, dissat_cost: Some(33.0) }
    }

    pub fn hash256(h: Pk::Hash256) -> Self {
        Self { ms: Arc::new(Miniscript::hash256(h)), sat_cost: 33.0, dissat_cost: Some(33.0) }
    }

    pub fn ripemd160(h: Pk::Ripemd160) -> Self {
        Self { ms: Arc::new(Miniscript::ripemd160(h)), sat_cost: 33.0, dissat_cost: Some(33.0) }
    }

    pub fn hash160(h: Pk::Hash160) -> Self {
        Self { ms: Arc::new(Miniscript::hash160(h)), sat_cost: 33.0, dissat_cost: Some(33.0) }
    }

    pub fn multi(thresh: crate::Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>) -> Self {
        let k = thresh.k();
        Self {
            ms: Arc::new(Miniscript::multi(thresh)),
            sat_cost: 1.0 + 73.0 * k as f64,
            dissat_cost: Some(1.0 * (k + 1) as f64),
        }
    }

    pub fn multi_a(thresh: crate::Threshold<Pk, MAX_PUBKEYS_IN_CHECKSIGADD>) -> Self {
        let k = thresh.k();
        let n = thresh.n();
        Self {
            ms: Arc::new(Miniscript::multi_a(thresh)),
            sat_cost: 66.0 * k as f64 + (n - k) as f64,
            dissat_cost: Some(n as f64), /* <w_n> ... <w_1> := 0x00 ... 0x00 (n times) */
        }
    }

    /// Helper functions to compose two Miniscript fragments, where we assume
    /// by construction that all validation parameters are upheld.
    fn compose_typeck_only(term: Terminal<Pk, Ctx>, ty: types::Type) -> Arc<Miniscript<Pk, Ctx>> {
        let ext = types::ExtData::type_check(&term);
        Arc::new(Miniscript::from_components_unchecked(term, ty, ext))
    }

    pub fn and_b(left: &Self, right: &Self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::AndB(Arc::clone(&left.ms), Arc::clone(&right.ms)),
                types::Type::and_b(left.ms.ty, right.ms.ty)?,
            ),
            sat_cost: left.sat_cost + right.sat_cost,
            dissat_cost: left.dissat_cost.zip(right.dissat_cost).map(|(l, r)| l + r),
        })
    }

    pub fn and_v(left: &Self, right: &Self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::AndV(Arc::clone(&left.ms), Arc::clone(&right.ms)),
                types::Type::and_v(left.ms.ty, right.ms.ty)?,
            ),
            sat_cost: left.sat_cost + right.sat_cost,
            dissat_cost: None,
        })
    }

    /// and_n(a,b) == andor(a,b,0) is a conjunction of a and b
    pub fn and_n(left: &Self, right: &Self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::AndOr(
                    Arc::clone(&left.ms),
                    Arc::clone(&right.ms),
                    Arc::new(Miniscript::FALSE),
                ),
                types::Type::and_or(left.ms.ty, right.ms.ty, types::Type::FALSE)?,
            ),
            sat_cost: left.sat_cost + right.sat_cost,
            dissat_cost: left.dissat_cost,
        })
    }

    pub fn and_or(
        a: &Self,
        b: &Self,
        c: &Self,
        l_weight: PositiveF64,
        r_weight: PositiveF64,
    ) -> Result<Self, types::ErrorKind> {
        // Do typecheck first, or the 'expect' on the next line might fire.
        let ty = types::Type::and_or(a.ms.ty, b.ms.ty, c.ms.ty)?;
        let adis = a
            .dissat_cost
            .expect("BUG: and_or first arg(a) must be dissatisfiable");

        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::AndOr(Arc::clone(&a.ms), Arc::clone(&b.ms), Arc::clone(&c.ms)),
                ty,
            ),
            sat_cost: f64::from(l_weight) * (a.sat_cost + b.sat_cost)
                + f64::from(r_weight) * (adis + c.sat_cost),
            dissat_cost: c.dissat_cost.map(|cdis| adis + cdis),
        })
    }

    pub fn or_b(
        left: &Self,
        right: &Self,
        l_weight: PositiveF64,
        r_weight: PositiveF64,
    ) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::OrB(Arc::clone(&left.ms), Arc::clone(&right.ms)),
                types::Type::or_b(left.ms.ty, right.ms.ty)?,
            ),
            sat_cost: f64::from(l_weight) * (left.sat_cost + right.dissat_cost.unwrap())
                + f64::from(r_weight) * (right.sat_cost + left.dissat_cost.unwrap()),
            dissat_cost: Some(left.dissat_cost.unwrap() + right.dissat_cost.unwrap()),
        })
    }

    pub fn or_d(
        left: &Self,
        right: &Self,
        l_weight: PositiveF64,
        r_weight: PositiveF64,
    ) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::OrD(Arc::clone(&left.ms), Arc::clone(&right.ms)),
                types::Type::or_d(left.ms.ty, right.ms.ty)?,
            ),
            sat_cost: f64::from(l_weight) * left.sat_cost
                + f64::from(r_weight) * (right.sat_cost + left.dissat_cost.unwrap()),
            dissat_cost: right.dissat_cost.map(|rd| left.dissat_cost.unwrap() + rd),
        })
    }

    pub fn or_c(
        left: &Self,
        right: &Self,
        l_weight: PositiveF64,
        r_weight: PositiveF64,
    ) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::OrC(Arc::clone(&left.ms), Arc::clone(&right.ms)),
                types::Type::or_c(left.ms.ty, right.ms.ty)?,
            ),
            sat_cost: f64::from(l_weight) * left.sat_cost
                + f64::from(r_weight) * (right.sat_cost + left.dissat_cost.unwrap()),
            dissat_cost: None,
        })
    }

    #[allow(clippy::manual_map)] // Complex if/let is better as is.
    pub fn or_i(
        left: &Self,
        right: &Self,
        l_weight: PositiveF64,
        r_weight: PositiveF64,
    ) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::OrI(Arc::clone(&left.ms), Arc::clone(&right.ms)),
                types::Type::or_i(left.ms.ty, right.ms.ty)?,
            ),
            sat_cost: f64::from(l_weight) * (2.0 + left.sat_cost)
                + f64::from(r_weight) * (1.0 + right.sat_cost),
            dissat_cost: {
                let ldis = left.dissat_cost.map(|ldis| 2.0 + ldis);
                let rdis = right.dissat_cost.map(|rdis| 1.0 + rdis);
                match (ldis, rdis) {
                    (Some(ldis), Some(rdis)) => Some(ldis.min(rdis)),
                    (opt_l, opt_r) => opt_l.or(opt_r),
                }
            },
        })
    }

    pub fn threshold(ms: Miniscript<Pk, Ctx>, k_over_n: f64, subs: &[Self]) -> Self {
        let mut sat_cost = 0.0;
        let mut dissat_cost = 0.0;
        for sub in subs {
            sat_cost += sub.sat_cost;
            dissat_cost += sub.dissat_cost.unwrap();
        }

        Self {
            ms: Arc::new(ms),
            sat_cost: sat_cost * k_over_n + dissat_cost * (1.0 - k_over_n),
            dissat_cost: Some(dissat_cost),
        }
    }

    pub fn cast_alt(&self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::Alt(Arc::clone(&self.ms)),
                types::Type::cast_alt(self.ms.ty)?,
            ),
            ..*self
        })
    }

    pub fn cast_swap(&self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::Swap(Arc::clone(&self.ms)),
                types::Type::cast_swap(self.ms.ty)?,
            ),
            ..*self
        })
    }

    pub fn cast_check(&self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::Check(Arc::clone(&self.ms)),
                types::Type::cast_check(self.ms.ty)?,
            ),
            ..*self
        })
    }

    pub fn cast_dupif(&self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::DupIf(Arc::clone(&self.ms)),
                types::Type::cast_dupif(self.ms.ty)?,
            ),
            sat_cost: 2.0 + self.sat_cost,
            dissat_cost: Some(1.0),
        })
    }

    pub fn cast_verify(&self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::Verify(Arc::clone(&self.ms)),
                types::Type::cast_verify(self.ms.ty)?,
            ),
            dissat_cost: None,
            ..*self
        })
    }

    pub fn cast_nonzero(&self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::NonZero(Arc::clone(&self.ms)),
                types::Type::cast_nonzero(self.ms.ty)?,
            ),
            dissat_cost: Some(1.0),
            ..*self
        })
    }

    pub fn cast_zeronotequal(&self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::ZeroNotEqual(Arc::clone(&self.ms)),
                types::Type::cast_zeronotequal(self.ms.ty)?,
            ),
            ..*self
        })
    }

    pub fn cast_true(&self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::AndV(Arc::clone(&self.ms), Arc::new(Miniscript::TRUE)),
                types::Type::cast_true(self.ms.ty)?,
            ),
            dissat_cost: None,
            ..*self
        })
    }

    pub fn cast_likely(&self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::OrI(Arc::new(Miniscript::FALSE), Arc::clone(&self.ms)),
                types::Type::cast_likely(self.ms.ty)?,
            ),
            sat_cost: 1.0 + self.sat_cost,
            dissat_cost: Some(2.0),
        })
    }

    pub fn cast_unlikely(&self) -> Result<Self, types::ErrorKind> {
        Ok(Self {
            ms: Self::compose_typeck_only(
                Terminal::OrI(Arc::clone(&self.ms), Arc::new(Miniscript::FALSE)),
                types::Type::cast_unlikely(self.ms.ty)?,
            ),
            sat_cost: 2.0 + self.sat_cost,
            dissat_cost: Some(1.0),
        })
    }
}
