// SPDX-License-Identifier: CC0-1.0

//! Miniscript Types
//!
//! Contains structures representing Miniscript types and utility functions
//! Contains all the type checking rules for correctness and malleability
//! Implemented as per rules on bitcoin.sipa.be/miniscript
pub mod correctness;
pub mod extra_props;
pub mod malleability;

#[cfg(all(not(feature = "std"), not(test)))]
use alloc::string::ToString as _;
use core::fmt;

pub use self::correctness::{Base, Correctness, Input};
pub use self::extra_props::ExtData;
pub use self::malleability::{Dissat, Malleability};
use super::ScriptContext;
use crate::{MiniscriptKey, Terminal, WithSpan};

/// Detailed type of a typechecker error
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Error {
    /// Passed a `z` argument to a `d` wrapper when `z` was expected
    NonZeroDupIf,
    /// Many fragments (all disjunctions except `or_i` as well as
    /// `andor` require their left child be dissatisfiable.
    LeftNotDissatisfiable,
    /// `or_b` requires its right child be dissatisfiable
    RightNotDissatisfiable,
    /// Tried to use the `s:` modifier on a fragment that takes more
    /// than one input
    SwapNonOne,
    /// Tried to use the `j:` (`SIZE 0NOTEQUAL IF`) wrapper on something
    /// that may be satisfied by a 0 input
    NonZeroZero,
    /// Many fragments require their left child to be a unit. This
    /// was not the case.
    LeftNotUnit,
    /// Attempted to construct a wrapper, but the child had
    /// an invalid type
    ChildBase1(Base),
    /// Attempted to construct a conjunction or disjunction, but
    /// the fragments' children were of invalid types
    ChildBase2(Base, Base),
    /// Attempted to construct an `andor` but the fragments'
    /// children were of invalid types
    ChildBase3(Base, Base, Base),
    /// The nth child of a threshold fragment had an invalid type (the
    /// first must be `B` and the rest `W`s)
    ThresholdBase(usize, Base),
    /// The nth child of a threshold fragment did not have a unique
    /// satisfaction
    ThresholdDissat(usize),
    /// The nth child of a threshold fragment was not a unit
    ThresholdNonUnit(usize),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::NonZeroDupIf => f.write_str(
                "the `d` wrapper requires its child be `z`, i.e. to consume zero stack elements",
            ),
            Self::LeftNotDissatisfiable => {
                f.write_str("this fragment requires its left child to be dissatisfiable")
            }
            Self::RightNotDissatisfiable => {
                f.write_str("this fragment requires its right child to be dissatisfiable")
            }
            Self::SwapNonOne => f.write_str(
                "the `s` wrapper requires its child to have exactly one input",
            ),
            Self::NonZeroZero => f.write_str(
                "the `j` wrapper requires its child's input to never be 0",
            ),
            Self::LeftNotUnit => f.write_str(
                "this fragment requires its left child to be a unit, i.e. to output 1 when satisfied",
            ),
            Self::ChildBase1(base) => write!(
                f,
                "this wrapper cannot be used on a fragment of type {:?}",
                base,
            ),
            Self::ChildBase2(base1, base2) => write!(
                f,
                "this combinator cannot be used on children of types {:?} and {:?}",
                base1, base2,
            ),
            Self::ChildBase3(base1, base2, base3) => write!(
                f,
                "this combinator cannot be used on children of types {:?}, {:?} and {:?}",
                base1, base2, base3,
            ),
            Self::ThresholdBase(idx, base) => write!(
                f,
                "threshold child {} has type {:?} rather than {:?}",
                idx,
                base,
                if *idx == 0 { Base::B } else { Base::W },
            ),
            Self::ThresholdDissat(idx) => write!(
                f,
                "threshold child {} cannot be dissatisfied",
                idx,
            ),
            Self::ThresholdNonUnit(idx) => write!(
                f,
                "threshold child {} is not a unit, i.e. it does not output 1 when satisfied",
                idx,
            ),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

/// Structure representing the type of a Miniscript fragment, including all
/// properties relevant to the main codebase
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Type {
    /// Correctness/soundness properties
    pub corr: Correctness,
    /// Malleability properties
    pub mall: Malleability,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self.corr.base {
            Base::B => "B",
            Base::K => "K",
            Base::V => "V",
            Base::W => "W",
        })?;
        f.write_str("/")?;
        f.write_str(match self.corr.input {
            Input::Zero => "z",
            Input::One => "o",
            Input::OneNonZero => "on",
            Input::Any => "",
            Input::AnyNonZero => "n",
        })?;
        if self.corr.dissatisfiable {
            f.write_str("d")?;
        }
        if self.corr.unit {
            f.write_str("u")?;
        }
        f.write_str(match self.mall.dissat {
            Dissat::None => "f",
            Dissat::Unique => "e",
            Dissat::Unknown => "",
        })?;
        if self.mall.safe {
            f.write_str("s")?;
        }
        if self.mall.non_malleable {
            f.write_str("m")?;
        }
        Ok(())
    }
}

impl Type {
    /// Type of the `0` combinator
    pub const TRUE: Self = Type { corr: Correctness::TRUE, mall: Malleability::TRUE };

    /// Type of the `0` combinator
    pub const FALSE: Self = Type { corr: Correctness::FALSE, mall: Malleability::FALSE };

    /// Check whether the `self` is a subtype of `other` argument .
    /// This checks whether the argument `other` has attributes which are present
    /// in the given `Type`. This returns `true` on same arguments
    /// `a.is_subtype(a)` is `true`.
    pub const fn is_subtype(&self, other: Self) -> bool {
        self.corr.is_subtype(other.corr) && self.mall.is_subtype(other.mall)
    }

    /// Confirm invariants of the type checker.
    fn sanity_checks(&self) {
        debug_assert!(!self.corr.dissatisfiable || self.mall.dissat != Dissat::None);
        debug_assert!(self.mall.dissat == Dissat::None || self.corr.base != Base::V);
        debug_assert!(self.mall.safe || self.corr.base != Base::K);
        debug_assert!(self.mall.non_malleable || self.corr.input != Input::Zero);
        self.corr.sanity_checks();
    }

    /// Constructor for the type of the `pk_k` fragment.
    pub const fn pk_k() -> Self { Type { corr: Correctness::pk_k(), mall: Malleability::pk_k() } }

    /// Constructor for the type of the `pk_h` fragment.
    pub const fn pk_h() -> Self { Type { corr: Correctness::pk_h(), mall: Malleability::pk_h() } }

    /// Constructor for the type of the `multi` fragment.
    pub const fn multi() -> Self {
        Type { corr: Correctness::multi(), mall: Malleability::multi() }
    }

    /// Constructor for the type of the `multi_a` fragment.
    pub const fn multi_a() -> Self {
        Type { corr: Correctness::multi_a(), mall: Malleability::multi_a() }
    }

    /// Constructor for the type of all the hash fragments.
    pub const fn hash() -> Self { Type { corr: Correctness::hash(), mall: Malleability::hash() } }

    /// Constructor for the type of the `after` and `older` fragments.
    pub const fn time() -> Self { Type { corr: Correctness::time(), mall: Malleability::time() } }

    /// Constructor for the type of the `a:` fragment.
    pub const fn cast_alt(self) -> Result<Self, Error> {
        // FIXME need to do manual `?` because ? is not supported in constfns. (Also below.)
        Ok(Type {
            corr: match Correctness::cast_alt(self.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::cast_alt(self.mall),
        })
    }

    /// Constructor for the type of the `s:` fragment.
    pub const fn cast_swap(self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::cast_swap(self.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::cast_swap(self.mall),
        })
    }

    /// Constructor for the type of the `c:` fragment.
    pub const fn cast_check(self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::cast_check(self.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::cast_check(self.mall),
        })
    }

    /// Constructor for the type of the `d:` fragment.
    pub const fn cast_dupif(self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::cast_dupif(self.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::cast_dupif(self.mall),
        })
    }

    /// Constructor for the type of the `v:` fragment.
    pub const fn cast_verify(self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::cast_verify(self.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::cast_verify(self.mall),
        })
    }

    /// Constructor for the type of the `j:` fragment.
    pub const fn cast_nonzero(self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::cast_nonzero(self.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::cast_nonzero(self.mall),
        })
    }

    /// Constructor for the type of the `n:` fragment.
    pub const fn cast_zeronotequal(self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::cast_zeronotequal(self.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::cast_zeronotequal(self.mall),
        })
    }

    /// Constructor for the type of the `t:` fragment.
    pub const fn cast_true(self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::cast_true(self.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::cast_true(self.mall),
        })
    }

    /// Constructor for the type of the `u:` fragment.
    pub const fn cast_unlikely(self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::cast_or_i_false(self.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::cast_or_i_false(self.mall),
        })
    }

    /// Constructor for the type of the `l:` fragment.
    pub const fn cast_likely(self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::cast_or_i_false(self.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::cast_or_i_false(self.mall),
        })
    }

    /// Constructor for the type of the `and_b` fragment.
    pub const fn and_b(left: Self, right: Self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::and_b(left.corr, right.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::and_b(left.mall, right.mall),
        })
    }

    /// Constructor for the type of the `and_v` fragment.
    pub const fn and_v(left: Self, right: Self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::and_v(left.corr, right.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::and_v(left.mall, right.mall),
        })
    }

    /// Constructor for the type of the `or_b` fragment.
    pub const fn or_b(left: Self, right: Self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::or_b(left.corr, right.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::or_b(left.mall, right.mall),
        })
    }

    /// Constructor for the type of the `or_b` fragment.
    pub const fn or_d(left: Self, right: Self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::or_d(left.corr, right.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::or_d(left.mall, right.mall),
        })
    }

    /// Constructor for the type of the `or_c` fragment.
    pub const fn or_c(left: Self, right: Self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::or_c(left.corr, right.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::or_c(left.mall, right.mall),
        })
    }

    /// Constructor for the type of the `or_i` fragment.
    pub const fn or_i(left: Self, right: Self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::or_i(left.corr, right.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::or_i(left.mall, right.mall),
        })
    }

    /// Constructor for the type of the `and_or` fragment.
    pub const fn and_or(a: Self, b: Self, c: Self) -> Result<Self, Error> {
        Ok(Type {
            corr: match Correctness::and_or(a.corr, b.corr, c.corr) {
                Ok(x) => x,
                Err(e) => return Err(e),
            },
            mall: Malleability::and_or(a.mall, b.mall, c.mall),
        })
    }

    /// Constructor for the type of the `thresh` fragment.
    // Cannot be a constfn because it takes a closure.
    pub fn threshold<'a, I>(k: usize, subs: I) -> Result<Self, Error>
    where
        I: Clone + ExactSizeIterator<Item = &'a Self>,
    {
        Ok(Type {
            corr: Correctness::threshold(k, subs.clone().map(|s| &s.corr))?,
            mall: Malleability::threshold(k, subs.map(|s| &s.mall)),
        })
    }
}

impl Type {
    /// Compute the type of a fragment assuming all the children of
    /// Miniscript have been computed already.
    pub fn type_check<Pk, Ctx>(fragment: &Terminal<Pk, Ctx>) -> Result<Self, WithSpan<Error>>
    where
        Pk: MiniscriptKey,
        Ctx: ScriptContext,
    {
        let wrap_err = |result: Result<Self, Error>| {
            result.map_err(|kind| WithSpan::new(kind).with_string(fragment.to_string()))
        };

        let ret = match *fragment {
            Terminal::True => Ok(Self::TRUE),
            Terminal::False => Ok(Self::FALSE),
            Terminal::PkK(..) => Ok(Self::pk_k()),
            Terminal::PkH(..) | Terminal::RawPkH(..) => Ok(Self::pk_h()),
            Terminal::Multi(..) => Ok(Self::multi()),
            Terminal::MultiA(..) => Ok(Self::multi_a()),
            Terminal::After(_) => Ok(Self::time()),
            Terminal::Older(_) => Ok(Self::time()),
            Terminal::Sha256(..) => Ok(Self::hash()),
            Terminal::Hash256(..) => Ok(Self::hash()),
            Terminal::Ripemd160(..) => Ok(Self::hash()),
            Terminal::Hash160(..) => Ok(Self::hash()),
            Terminal::Alt(ref sub) => wrap_err(Self::cast_alt(sub.ty)),
            Terminal::Swap(ref sub) => wrap_err(Self::cast_swap(sub.ty)),
            Terminal::Check(ref sub) => wrap_err(Self::cast_check(sub.ty)),
            Terminal::DupIf(ref sub) => wrap_err(Self::cast_dupif(sub.ty)),
            Terminal::Verify(ref sub) => wrap_err(Self::cast_verify(sub.ty)),
            Terminal::NonZero(ref sub) => wrap_err(Self::cast_nonzero(sub.ty)),
            Terminal::ZeroNotEqual(ref sub) => wrap_err(Self::cast_zeronotequal(sub.ty)),
            Terminal::AndB(ref l, ref r) => {
                let ltype = l.ty;
                let rtype = r.ty;
                wrap_err(Self::and_b(ltype, rtype))
            }
            Terminal::AndV(ref l, ref r) => {
                let ltype = l.ty;
                let rtype = r.ty;
                wrap_err(Self::and_v(ltype, rtype))
            }
            Terminal::OrB(ref l, ref r) => {
                let ltype = l.ty;
                let rtype = r.ty;
                wrap_err(Self::or_b(ltype, rtype))
            }
            Terminal::OrD(ref l, ref r) => {
                let ltype = l.ty;
                let rtype = r.ty;
                wrap_err(Self::or_d(ltype, rtype))
            }
            Terminal::OrC(ref l, ref r) => {
                let ltype = l.ty;
                let rtype = r.ty;
                wrap_err(Self::or_c(ltype, rtype))
            }
            Terminal::OrI(ref l, ref r) => {
                let ltype = l.ty;
                let rtype = r.ty;
                wrap_err(Self::or_i(ltype, rtype))
            }
            Terminal::AndOr(ref a, ref b, ref c) => {
                let atype = a.ty;
                let btype = b.ty;
                let ctype = c.ty;
                wrap_err(Self::and_or(atype, btype, ctype))
            }
            Terminal::Thresh(ref thresh) => {
                wrap_err(Self::threshold(thresh.k(), thresh.iter().map(|ms| &ms.ty)))
            }
        };
        if let Ok(ref ret) = ret {
            ret.sanity_checks()
        }
        ret
    }
}
