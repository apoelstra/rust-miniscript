// SPDX-License-Identifier: CC0-1.0

//! Correctness/Soundness type properties

use super::Error;

/// Basic type representing where the fragment can go
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Base {
    /// Takes its inputs from the top of the stack. Pushes
    /// nonzero if the condition is satisfied. If not, if it
    /// does not abort, then 0 is pushed.
    B,
    /// Takes its inputs from the top of the stack. Pushes a
    /// public key, regardless of satisfaction, onto the stack.
    /// Must be wrapped in `c:` to turn into any other type.
    K,
    /// Takes its inputs from the top of the stack, which
    /// must satisfy the condition (will abort otherwise).
    /// Does not push anything onto the stack.
    V,
    /// Takes from the stack its inputs + element X at the top.
    /// If the inputs satisfy the condition, [nonzero X] or
    /// [X nonzero] is pushed. If not, if it does not abort,
    /// then [0 X] or [X 0] is pushed.
    W,
}

/// Type property representing expectations about how many inputs
/// the fragment accepts, and assumptions about that
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Input {
    /// Consumes no stack elements under any circumstances
    Zero,
    /// Consumes exactly one stack element under all circumstances
    One,
    /// Consumes any number of stack elements
    Any,
    /// Consumes exactly one stack element. If the fragment is
    /// satisfied, this element must be nonzero.
    OneNonZero,
    /// Consumes 1 or more stack elements. If the fragment is
    /// satisfied, the top element must be nonzero. (This property
    /// cannot be applied to any type with a `W` base.)
    AnyNonZero,
}

impl Input {
    // FIXME rustc should eventually support derived == on enums in constfns
    const fn constfn_eq(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Input::Zero, Input::Zero)
                | (Input::One, Input::One)
                | (Input::Any, Input::Any)
                | (Input::OneNonZero, Input::OneNonZero)
                | (Input::AnyNonZero, Input::AnyNonZero)
        )
    }

    /// Check whether given `Input` is a subtype of `other`. That is,
    /// if some Input is `OneNonZero` then it must be `One`, hence `OneNonZero` is
    /// a subtype if `One`. Returns `true` for `a.is_subtype(a)`.
    const fn is_subtype(&self, other: Self) -> bool {
        match (*self, other) {
            (x, y) if x.constfn_eq(y) => true,
            (Input::OneNonZero, Input::One)
            | (Input::OneNonZero, Input::AnyNonZero)
            | (_, Input::Any) => true,
            _ => false,
        }
    }
}

/// Soundness and completeness type properties of a fragment.
///
/// Completeness is the property that a valid witness actually exists for all
/// branches, which an honest user can produce. Soundness is the property
/// that no branch can be satisfied _without_ an honest user.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Correctness {
    /// The base type
    pub base: Base,
    /// Properties of the inputs
    pub input: Input,
    /// Whether it is definitely possible to dissatisfy the expression.
    /// If this is false, it does not necessarily mean that dissatisfaction
    /// is impossible (see `Dissat::None` for this property); it only means
    /// that we cannot depend on having a dissatisfaction when reasoning
    /// about completeness.
    pub dissatisfiable: bool,
    /// Whether the fragment's "nonzero" output on satisfaction is
    /// always the constant 1.
    pub unit: bool,
}

impl Correctness {
    /// Correctness data for the `1` combinator
    pub const TRUE: Self =
        Correctness { base: Base::B, input: Input::Zero, dissatisfiable: false, unit: true };

    /// Correctness data for the `0` combinator
    pub const FALSE: Self =
        Correctness { base: Base::B, input: Input::Zero, dissatisfiable: true, unit: true };

    /// Check whether the `self` is a subtype of `other` argument .
    /// This checks whether the argument `other` has attributes which are present
    /// in the given `Type`. This returns `true` on same arguments
    /// `a.is_subtype(a)` is `true`.
    pub const fn is_subtype(&self, other: Self) -> bool {
        self.base as u8 == other.base as u8
            && self.input.is_subtype(other.input)
            && self.dissatisfiable >= other.dissatisfiable
            && self.unit >= other.unit
    }

    /// Confirm invariants of the correctness checker.
    pub(crate) fn sanity_checks(&self) {
        match self.base {
            Base::B => {}
            Base::K => {
                debug_assert!(self.unit);
            }
            Base::V => {
                debug_assert!(!self.unit);
                debug_assert!(!self.dissatisfiable);
            }
            Base::W => {
                debug_assert!(!self.input.constfn_eq(Input::OneNonZero));
                debug_assert!(!self.input.constfn_eq(Input::AnyNonZero));
            }
        }
    }

    /// Constructor for the correctness properties of the `pk_k` fragment.
    pub const fn pk_k() -> Self {
        Correctness { base: Base::K, input: Input::OneNonZero, dissatisfiable: true, unit: true }
    }

    /// Constructor for the correctness properties of the `pk_h` fragment.
    pub const fn pk_h() -> Self {
        Correctness {
            base: Base::K,
            input: Input::AnyNonZero,
            dissatisfiable: true, // FIXME check with sipa
            unit: true,
        }
    }

    /// Constructor for the correctness properties of the `multi` fragment.
    pub const fn multi() -> Self {
        Correctness { base: Base::B, input: Input::AnyNonZero, dissatisfiable: true, unit: true }
    }

    /// Constructor for the correctness properties of the `multi_a` fragment.
    pub const fn multi_a() -> Self {
        Correctness { base: Base::B, input: Input::Any, dissatisfiable: true, unit: true }
    }

    /// Constructor for the correctness properties of any of the hash fragments.
    pub const fn hash() -> Self {
        Correctness { base: Base::B, input: Input::OneNonZero, dissatisfiable: true, unit: true }
    }

    /// Constructor for the correctness properties of either of the time fragments.
    pub const fn time() -> Self {
        Correctness { base: Base::B, input: Input::Zero, dissatisfiable: false, unit: false }
    }

    /// Constructor for the correctness properties of the `a:` fragment.
    pub const fn cast_alt(self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match self.base {
                Base::B => Base::W,
                x => return Err(Error::ChildBase1(x)),
            },
            input: Input::Any,
            dissatisfiable: self.dissatisfiable,
            unit: self.unit,
        })
    }

    /// Constructor for the correctness properties of the `s:` fragment.
    pub const fn cast_swap(self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match self.base {
                Base::B => Base::W,
                x => return Err(Error::ChildBase1(x)),
            },
            input: match self.input {
                Input::One | Input::OneNonZero => Input::Any,
                _ => return Err(Error::SwapNonOne),
            },
            dissatisfiable: self.dissatisfiable,
            unit: self.unit,
        })
    }

    /// Constructor for the correctness properties of the `c:` fragment.
    pub const fn cast_check(self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match self.base {
                Base::K => Base::B,
                x => return Err(Error::ChildBase1(x)),
            },
            input: self.input,
            dissatisfiable: self.dissatisfiable,
            unit: true,
        })
    }

    /// Constructor for the correctness properties of the `d:` fragment.
    pub const fn cast_dupif(self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match self.base {
                Base::V => Base::B,
                x => return Err(Error::ChildBase1(x)),
            },
            input: match self.input {
                Input::Zero => Input::OneNonZero,
                _ => return Err(Error::NonZeroDupIf),
            },
            dissatisfiable: true,
            unit: false,
        })
    }

    /// Constructor for the correctness properties of the `v:` fragment.
    pub const fn cast_verify(self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match self.base {
                Base::B => Base::V,
                x => return Err(Error::ChildBase1(x)),
            },
            input: self.input,
            dissatisfiable: false,
            unit: false,
        })
    }

    /// Constructor for the correctness properties of the `j:` fragment.
    pub const fn cast_nonzero(self) -> Result<Self, Error> {
        if !self.input.constfn_eq(Input::OneNonZero) && !self.input.constfn_eq(Input::AnyNonZero) {
            return Err(Error::NonZeroZero);
        }
        Ok(Correctness {
            base: match self.base {
                Base::B => Base::B,
                x => return Err(Error::ChildBase1(x)),
            },
            input: self.input,
            dissatisfiable: true,
            unit: self.unit,
        })
    }

    /// Constructor for the correctness properties of the `n:` fragment.
    pub const fn cast_zeronotequal(self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match self.base {
                Base::B => Base::B,
                x => return Err(Error::ChildBase1(x)),
            },
            input: self.input,
            dissatisfiable: self.dissatisfiable,
            unit: true,
        })
    }

    /// Constructor for the correctness properties of the `t:` fragment.
    pub const fn cast_true(self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match self.base {
                Base::V => Base::B,
                x => return Err(Error::ChildBase1(x)),
            },
            input: self.input,
            dissatisfiable: false,
            unit: true,
        })
    }

    /// Constructor for the correctness properties of the `l:` and `u:` fragments.
    pub const fn cast_or_i_false(self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match self.base {
                Base::B => Base::B,
                x => return Err(Error::ChildBase1(x)),
            },
            input: match self.input {
                // could by `Input::OneNonZero` but the type system
                // isn't safe enough to capture that `0` is unsatisfiable
                Input::Zero => Input::One,
                _ => Input::Any,
            },
            dissatisfiable: true,
            unit: self.unit,
        })
    }

    /// Constructor for the correctness properties of the `and_b` fragment
    pub const fn and_b(left: Self, right: Self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match (left.base, right.base) {
                (Base::B, Base::W) => Base::B,
                (x, y) => return Err(Error::ChildBase2(x, y)),
            },
            input: match (left.input, right.input) {
                (Input::Zero, Input::Zero) => Input::Zero,
                (Input::Zero, Input::One) | (Input::One, Input::Zero) => Input::One,
                (Input::Zero, Input::OneNonZero) | (Input::OneNonZero, Input::Zero) => {
                    Input::OneNonZero
                }
                (Input::OneNonZero, _)
                | (Input::AnyNonZero, _)
                | (Input::Zero, Input::AnyNonZero) => Input::AnyNonZero,
                _ => Input::Any,
            },
            dissatisfiable: left.dissatisfiable && right.dissatisfiable,
            unit: true,
        })
    }

    /// Constructor for the correctness properties of the `and_v` fragment
    pub const fn and_v(left: Self, right: Self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match (left.base, right.base) {
                (Base::V, Base::B) => Base::B,
                (Base::V, Base::K) => Base::K,
                (Base::V, Base::V) => Base::V,
                (x, y) => return Err(Error::ChildBase2(x, y)),
            },
            input: match (left.input, right.input) {
                (Input::Zero, Input::Zero) => Input::Zero,
                (Input::Zero, Input::One) | (Input::One, Input::Zero) => Input::One,
                (Input::Zero, Input::OneNonZero) | (Input::OneNonZero, Input::Zero) => {
                    Input::OneNonZero
                }
                (Input::OneNonZero, _)
                | (Input::AnyNonZero, _)
                | (Input::Zero, Input::AnyNonZero) => Input::AnyNonZero,
                _ => Input::Any,
            },
            dissatisfiable: false,
            unit: right.unit,
        })
    }

    /// Constructor for the correctness properties of the `or_b` fragment
    pub const fn or_b(left: Self, right: Self) -> Result<Self, Error> {
        if !left.dissatisfiable {
            return Err(Error::LeftNotDissatisfiable);
        }
        if !right.dissatisfiable {
            return Err(Error::RightNotDissatisfiable);
        }
        Ok(Correctness {
            base: match (left.base, right.base) {
                (Base::B, Base::W) => Base::B,
                (x, y) => return Err(Error::ChildBase2(x, y)),
            },
            input: match (left.input, right.input) {
                (Input::Zero, Input::Zero) => Input::Zero,
                (Input::Zero, Input::One)
                | (Input::One, Input::Zero)
                | (Input::Zero, Input::OneNonZero)
                | (Input::OneNonZero, Input::Zero) => Input::One,
                _ => Input::Any,
            },
            dissatisfiable: true,
            unit: true,
        })
    }

    /// Constructor for the correctness properties of the `or_d` fragment
    pub const fn or_d(left: Self, right: Self) -> Result<Self, Error> {
        if !left.dissatisfiable {
            return Err(Error::LeftNotDissatisfiable);
        }
        if !left.unit {
            return Err(Error::LeftNotUnit);
        }
        Ok(Correctness {
            base: match (left.base, right.base) {
                (Base::B, Base::B) => Base::B,
                (x, y) => return Err(Error::ChildBase2(x, y)),
            },
            input: match (left.input, right.input) {
                (Input::Zero, Input::Zero) => Input::Zero,
                (Input::One, Input::Zero) | (Input::OneNonZero, Input::Zero) => Input::One,
                _ => Input::Any,
            },
            dissatisfiable: right.dissatisfiable,
            unit: right.unit,
        })
    }

    /// Constructor for the correctness properties of the `or_c` fragment
    pub const fn or_c(left: Self, right: Self) -> Result<Self, Error> {
        if !left.dissatisfiable {
            return Err(Error::LeftNotDissatisfiable);
        }
        if !left.unit {
            return Err(Error::LeftNotUnit);
        }
        Ok(Correctness {
            base: match (left.base, right.base) {
                (Base::B, Base::V) => Base::V,
                (x, y) => return Err(Error::ChildBase2(x, y)),
            },
            input: match (left.input, right.input) {
                (Input::Zero, Input::Zero) => Input::Zero,
                (Input::One, Input::Zero) | (Input::OneNonZero, Input::Zero) => Input::One,
                _ => Input::Any,
            },
            dissatisfiable: false,
            unit: false,
        })
    }

    /// Constructor for the correctness properties of the `or_i` fragment
    pub const fn or_i(left: Self, right: Self) -> Result<Self, Error> {
        Ok(Correctness {
            base: match (left.base, right.base) {
                (Base::B, Base::B) => Base::B,
                (Base::V, Base::V) => Base::V,
                (Base::K, Base::K) => Base::K,
                (x, y) => return Err(Error::ChildBase2(x, y)),
            },
            input: match (left.input, right.input) {
                (Input::Zero, Input::Zero) => Input::One,
                _ => Input::Any,
            },
            dissatisfiable: left.dissatisfiable || right.dissatisfiable,
            unit: left.unit && right.unit,
        })
    }

    /// Constructor for the correctness properties of the `andor` fragment
    pub const fn and_or(a: Self, b: Self, c: Self) -> Result<Self, Error> {
        if !a.dissatisfiable {
            return Err(Error::LeftNotDissatisfiable);
        }
        if !a.unit {
            return Err(Error::LeftNotUnit);
        }
        Ok(Correctness {
            base: match (a.base, b.base, c.base) {
                (Base::B, Base::B, Base::B) => Base::B,
                (Base::B, Base::K, Base::K) => Base::K,
                (Base::B, Base::V, Base::V) => Base::V,
                (x, y, z) => return Err(Error::ChildBase3(x, y, z)),
            },
            input: match (a.input, b.input, c.input) {
                (Input::Zero, Input::Zero, Input::Zero) => Input::Zero,
                (Input::Zero, Input::One, Input::One)
                | (Input::Zero, Input::One, Input::OneNonZero)
                | (Input::Zero, Input::OneNonZero, Input::One)
                | (Input::Zero, Input::OneNonZero, Input::OneNonZero)
                | (Input::One, Input::Zero, Input::Zero)
                | (Input::OneNonZero, Input::Zero, Input::Zero) => Input::One,
                _ => Input::Any,
            },
            dissatisfiable: c.dissatisfiable,
            unit: b.unit && c.unit,
        })
    }

    /// Constructor for the correctness properties of the `thresh` fragment
    // Cannot be constfn because it takes a closure.
    pub fn threshold<'a, I>(_k: usize, subs: I) -> Result<Self, Error>
    where
        I: Iterator<Item = &'a Self>,
    {
        let mut num_args = 0;
        for (i, subtype) in subs.enumerate() {
            num_args += match subtype.input {
                Input::Zero => 0,
                Input::One | Input::OneNonZero => 1,
                Input::Any | Input::AnyNonZero => 2, // we only check if num args is max 1
            };
            if i == 0 && subtype.base != Base::B {
                return Err(Error::ThresholdBase(i, subtype.base));
            }
            if i != 0 && subtype.base != Base::W {
                return Err(Error::ThresholdBase(i, subtype.base));
            }
            if !subtype.unit {
                return Err(Error::ThresholdNonUnit(i));
            }
            if !subtype.dissatisfiable {
                return Err(Error::ThresholdDissat(i));
            }
        }

        Ok(Correctness {
            base: Base::B,
            input: match num_args {
                0 => Input::Zero,
                1 => Input::One,
                _ => Input::Any,
            },
            dissatisfiable: true,
            unit: true,
        })
    }
}
