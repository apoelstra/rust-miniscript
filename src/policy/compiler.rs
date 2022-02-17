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

//! # Policy Compiler
//!
//! Optimizing compiler from concrete policies to Miniscript
//!

use std::collections::BTreeMap;
use std::convert::From;
use std::marker::PhantomData;
use std::{cmp, error, f64, fmt, mem};

use miniscript::limits::MAX_PUBKEYS_PER_MULTISIG;
use miniscript::types::{self, ErrorKind, ExtData, Property, Type};
use miniscript::ScriptContext;
use policy::Concrete;
use std::collections::vec_deque::VecDeque;
use std::hash;
use std::sync::Arc;
use {policy, Terminal};
use {Miniscript, MiniscriptKey};

type PolicyCache<Pk, Ctx> =
    BTreeMap<(Concrete<Pk>, OrdF64, Option<OrdF64>), BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>>;

///Ordered f64 for comparison
#[derive(Copy, Clone, PartialEq, PartialOrd, Debug)]
struct OrdF64(f64);

impl Eq for OrdF64 {}
impl Ord for OrdF64 {
    fn cmp(&self, other: &OrdF64) -> cmp::Ordering {
        // will panic if given NaN
        self.0.partial_cmp(&other.0).unwrap()
    }
}

/// Detailed Error type for Compiler
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum CompilerError {
    /// Compiler has non-safe input policy.
    TopLevelNonSafe,
    /// Non-Malleable compilation  does exists for the given sub-policy.
    ImpossibleNonMalleableCompilation,
    /// At least one satisfaction path in the optimal Miniscript has exceeded
    /// the consensus or standardness limits.
    /// There may exist other miniscripts which are under these limits but the
    /// compiler currently does not find them.
    LimitsExceeded,
    ///Policy related errors
    PolicyError(policy::concrete::PolicyError),
}

impl error::Error for CompilerError {}

impl fmt::Display for CompilerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CompilerError::TopLevelNonSafe => {
                f.write_str("Top Level script is not safe on some spendpath")
            }
            CompilerError::ImpossibleNonMalleableCompilation => {
                f.write_str("The compiler could not find any non-malleable compilation")
            }
            CompilerError::LimitsExceeded => f.write_str(
                "At least one spending path has exceeded the standardness or consensus limits",
            ),
            CompilerError::PolicyError(ref e) => fmt::Display::fmt(e, f),
        }
    }
}

#[doc(hidden)]
impl From<policy::concrete::PolicyError> for CompilerError {
    fn from(e: policy::concrete::PolicyError) -> CompilerError {
        CompilerError::PolicyError(e)
    }
}

/// Hash required for using OrdF64 as key for hashmap
impl hash::Hash for OrdF64 {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

/// Compilation key: This represents the state of the best possible compilation
/// of a given policy(implicitly keyed).
#[derive(Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
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
    dissat_prob: Option<OrdF64>,
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
    fn from_type(ty: Type, expensive_verify: bool, dissat_prob: Option<f64>) -> CompilationKey {
        CompilationKey {
            ty,
            expensive_verify,
            dissat_prob: dissat_prob.and_then(|x| Some(OrdF64(x))),
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct CompilerExtData {
    /// If this node is the direct child of a disjunction, this field must
    /// have the probability of its branch being taken. Otherwise it is ignored.
    /// All functions initialize it to `None`.
    branch_prob: Option<f64>,
    /// The number of bytes needed to satisfy the fragment in segwit format
    /// (total length of all witness pushes, plus their own length prefixes)
    sat_cost: f64,
    /// The number of bytes needed to dissatisfy the fragment in segwit format
    /// (total length of all witness pushes, plus their own length prefixes)
    /// for fragments that can be dissatisfied without failing the script.
    dissat_cost: Option<f64>,
}

impl Property for CompilerExtData {
    fn from_true() -> Self {
        CompilerExtData {
            branch_prob: None,
            sat_cost: 0.0,
            dissat_cost: None,
        }
    }

    fn from_false() -> Self {
        CompilerExtData {
            branch_prob: None,
            sat_cost: f64::MAX,
            dissat_cost: Some(0.0),
        }
    }

    fn from_pk_k() -> Self {
        CompilerExtData {
            branch_prob: None,
            sat_cost: 73.0,
            dissat_cost: Some(1.0),
        }
    }

    fn from_pk_h() -> Self {
        CompilerExtData {
            branch_prob: None,
            sat_cost: 73.0 + 34.0,
            dissat_cost: Some(1.0 + 34.0),
        }
    }

    fn from_multi(k: usize, _n: usize) -> Self {
        CompilerExtData {
            branch_prob: None,
            sat_cost: 1.0 + 73.0 * k as f64,
            dissat_cost: Some(1.0 * (k + 1) as f64),
        }
    }

    fn from_hash() -> Self {
        CompilerExtData {
            branch_prob: None,
            sat_cost: 33.0,
            dissat_cost: Some(33.0),
        }
    }

    fn from_time(_t: u32) -> Self {
        CompilerExtData {
            branch_prob: None,
            sat_cost: 0.0,
            dissat_cost: None,
        }
    }

    fn cast_alt(self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: self.sat_cost,
            dissat_cost: self.dissat_cost,
        })
    }

    fn cast_swap(self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: self.sat_cost,
            dissat_cost: self.dissat_cost,
        })
    }

    fn cast_check(self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: self.sat_cost,
            dissat_cost: self.dissat_cost,
        })
    }

    fn cast_dupif(self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: 2.0 + self.sat_cost,
            dissat_cost: Some(1.0),
        })
    }

    fn cast_verify(self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: self.sat_cost,
            dissat_cost: None,
        })
    }

    fn cast_nonzero(self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: self.sat_cost,
            dissat_cost: Some(1.0),
        })
    }

    fn cast_zeronotequal(self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: self.sat_cost,
            dissat_cost: self.dissat_cost,
        })
    }

    fn cast_true(self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: self.sat_cost,
            dissat_cost: None,
        })
    }

    fn cast_or_i_false(self) -> Result<Self, types::ErrorKind> {
        // never called directly
        unreachable!()
    }

    fn cast_unlikely(self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: 2.0 + self.sat_cost,
            dissat_cost: Some(1.0),
        })
    }

    fn cast_likely(self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: 1.0 + self.sat_cost,
            dissat_cost: Some(2.0),
        })
    }

    fn and_b(left: Self, right: Self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: left.sat_cost + right.sat_cost,
            dissat_cost: match (left.dissat_cost, right.dissat_cost) {
                (Some(l), Some(r)) => Some(l + r),
                _ => None,
            },
        })
    }

    fn and_v(left: Self, right: Self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: left.sat_cost + right.sat_cost,
            dissat_cost: None,
        })
    }

    fn or_b(l: Self, r: Self) -> Result<Self, types::ErrorKind> {
        let lprob = l
            .branch_prob
            .expect("BUG: left branch prob must be set for disjunctions");
        let rprob = r
            .branch_prob
            .expect("BUG: right branch prob must be set for disjunctions");
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: lprob * (l.sat_cost + r.dissat_cost.unwrap())
                + rprob * (r.sat_cost + l.dissat_cost.unwrap()),
            dissat_cost: Some(l.dissat_cost.unwrap() + r.dissat_cost.unwrap()),
        })
    }

    fn or_d(l: Self, r: Self) -> Result<Self, types::ErrorKind> {
        let lprob = l
            .branch_prob
            .expect("BUG: left branch prob must be set for disjunctions");
        let rprob = r
            .branch_prob
            .expect("BUG: right branch prob must be set for disjunctions");
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: lprob * l.sat_cost + rprob * (r.sat_cost + l.dissat_cost.unwrap()),
            dissat_cost: r.dissat_cost.map(|rd| l.dissat_cost.unwrap() + rd),
        })
    }

    fn or_c(l: Self, r: Self) -> Result<Self, types::ErrorKind> {
        let lprob = l
            .branch_prob
            .expect("BUG: left branch prob must be set for disjunctions");
        let rprob = r
            .branch_prob
            .expect("BUG: right branch prob must be set for disjunctions");
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: lprob * l.sat_cost + rprob * (r.sat_cost + l.dissat_cost.unwrap()),
            dissat_cost: None,
        })
    }

    fn or_i(l: Self, r: Self) -> Result<Self, types::ErrorKind> {
        let lprob = l
            .branch_prob
            .expect("BUG: left branch prob must be set for disjunctions");
        let rprob = r
            .branch_prob
            .expect("BUG: right branch prob must be set for disjunctions");
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: lprob * (2.0 + l.sat_cost) + rprob * (1.0 + r.sat_cost),
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
        })
    }

    fn and_or(a: Self, b: Self, c: Self) -> Result<Self, types::ErrorKind> {
        if a.dissat_cost.is_none() {
            return Err(ErrorKind::LeftNotDissatisfiable);
        }
        let aprob = a.branch_prob.expect("andor, a prob must be set");
        let bprob = b.branch_prob.expect("andor, b prob must be set");
        let cprob = c.branch_prob.expect("andor, c prob must be set");

        let adis = a
            .dissat_cost
            .expect("BUG: and_or first arg(a) must be dissatisfiable");
        debug_assert_eq!(aprob, bprob); //A and B must have same branch prob.
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: aprob * (a.sat_cost + b.sat_cost) + cprob * (adis + c.sat_cost),
            dissat_cost: if let Some(cdis) = c.dissat_cost {
                Some(adis + cdis)
            } else {
                None
            },
        })
    }

    fn and_n(a: Self, b: Self) -> Result<Self, types::ErrorKind> {
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: a.sat_cost + b.sat_cost,
            dissat_cost: a.dissat_cost,
        })
    }

    fn threshold<S>(k: usize, n: usize, mut sub_ck: S) -> Result<Self, types::ErrorKind>
    where
        S: FnMut(usize) -> Result<Self, types::ErrorKind>,
    {
        let k_over_n = k as f64 / n as f64;
        let mut sat_cost = 0.0;
        let mut dissat_cost = 0.0;
        for i in 0..n {
            let sub = sub_ck(i)?;
            sat_cost += sub.sat_cost;
            dissat_cost += sub.dissat_cost.unwrap();
        }
        Ok(CompilerExtData {
            branch_prob: None,
            sat_cost: sat_cost * k_over_n + dissat_cost * (1.0 - k_over_n),
            dissat_cost: Some(dissat_cost),
        })
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
    fn cost_1d(&self, sat_prob: f64, dissat_prob: Option<f64>) -> f64 {
        self.ms.ext.pk_cost as f64
            + self.comp_ext_data.sat_cost * sat_prob
            + match (dissat_prob, self.comp_ext_data.dissat_cost) {
                (Some(prob), Some(cost)) => prob * cost,
                (Some(_), None) => f64::INFINITY,
                (None, Some(_)) => 0.0,
                (None, None) => 0.0,
            }
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> AstElemExt<Pk, Ctx> {
    fn terminal(ast: Terminal<Pk, Ctx>) -> AstElemExt<Pk, Ctx> {
        AstElemExt {
            comp_ext_data: CompilerExtData::type_check(&ast, |_| None).unwrap(),
            ms: Arc::new(Miniscript::from_ast(ast).expect("Terminal creation must always succeed")),
        }
    }

    fn binary(
        ast: Terminal<Pk, Ctx>,
        l: &AstElemExt<Pk, Ctx>,
        r: &AstElemExt<Pk, Ctx>,
    ) -> Result<AstElemExt<Pk, Ctx>, types::Error<Pk, Ctx>> {
        let lookup_ext = |n| match n {
            0 => Some(l.comp_ext_data),
            1 => Some(r.comp_ext_data),
            _ => unreachable!(),
        };
        //Types and ExtData are already cached and stored in children. So, we can
        //type_check without cache. For Compiler extra data, we supply a cache.
        let ty = types::Type::type_check(&ast, |_| None)?;
        let ext = types::ExtData::type_check(&ast, |_| None)?;
        let comp_ext_data = CompilerExtData::type_check(&ast, lookup_ext)?;
        Ok(AstElemExt {
            ms: Arc::new(Miniscript {
                ty,
                ext,
                node: ast,
                phantom: PhantomData,
            }),
            comp_ext_data,
        })
    }

    fn ternary(
        ast: Terminal<Pk, Ctx>,
        a: &AstElemExt<Pk, Ctx>,
        b: &AstElemExt<Pk, Ctx>,
        c: &AstElemExt<Pk, Ctx>,
    ) -> Result<AstElemExt<Pk, Ctx>, types::Error<Pk, Ctx>> {
        let lookup_ext = |n| match n {
            0 => Some(a.comp_ext_data),
            1 => Some(b.comp_ext_data),
            2 => Some(c.comp_ext_data),
            _ => unreachable!(),
        };
        //Types and ExtData are already cached and stored in children. So, we can
        //type_check without cache. For Compiler extra data, we supply a cache.
        let ty = types::Type::type_check(&ast, |_| None)?;
        let ext = types::ExtData::type_check(&ast, |_| None)?;
        let comp_ext_data = CompilerExtData::type_check(&ast, lookup_ext)?;
        Ok(AstElemExt {
            ms: Arc::new(Miniscript {
                ty: ty,
                ext: ext,
                node: ast,
                phantom: PhantomData,
            }),
            comp_ext_data,
        })
    }
}

/// Different types of casts possible for each node.
#[derive(Copy, Clone)]
struct Cast<Pk: MiniscriptKey, Ctx: ScriptContext> {
    node: fn(Arc<Miniscript<Pk, Ctx>>) -> Terminal<Pk, Ctx>,
    ast_type: fn(types::Type) -> Result<types::Type, ErrorKind>,
    ext_data: fn(types::ExtData) -> Result<types::ExtData, ErrorKind>,
    comp_ext_data: fn(CompilerExtData) -> Result<CompilerExtData, types::ErrorKind>,
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Cast<Pk, Ctx> {
    fn cast(&self, ast: &AstElemExt<Pk, Ctx>) -> Result<AstElemExt<Pk, Ctx>, ErrorKind> {
        Ok(AstElemExt {
            ms: Arc::new(Miniscript {
                ty: (self.ast_type)(ast.ms.ty)?,
                ext: (self.ext_data)(ast.ms.ext)?,
                node: (self.node)(Arc::clone(&ast.ms)),
                phantom: PhantomData,
            }),
            comp_ext_data: (self.comp_ext_data)(ast.comp_ext_data)?,
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
            node: |ms| {
                Terminal::OrI(
                    Arc::new(
                        Miniscript::from_ast(Terminal::False).expect("False Miniscript creation"),
                    ),
                    ms,
                )
            },
            ast_type: types::Type::cast_likely,
            comp_ext_data: CompilerExtData::cast_likely,
        },
        Cast {
            ext_data: types::ExtData::cast_unlikely,
            node: |ms| {
                Terminal::OrI(
                    ms,
                    Arc::new(
                        Miniscript::from_ast(Terminal::False).expect("False Miniscript creation"),
                    ),
                )
            },
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
            node: |ms| {
                Terminal::AndV(
                    ms,
                    Arc::new(
                        Miniscript::from_ast(Terminal::True).expect("True Miniscript creation"),
                    ),
                )
            },
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
    sat_prob: f64,
    dissat_prob: Option<f64>,
) -> bool {
    // return malleable types directly. If a elem is malleable under current context,
    // all the casts to it are also going to be malleable
    if !elem.ms.ty.mall.non_malleable && Ctx::check_terminal_non_malleable(&elem.ms.node).is_ok() {
        return false;
    }

    if let Err(_) = Ctx::check_local_validity(&elem.ms) {
        return false;
    }

    let elem_cost = elem.cost_1d(sat_prob, dissat_prob);

    let elem_key = CompilationKey::from_type(elem.ms.ty, elem.ms.ext.has_free_verify, dissat_prob);

    // Check whether the new element is worse than any existing element. If there
    // is an element which is a subtype of the current element and has better
    // cost, don't consider this element.
    let is_worse = map
        .iter()
        .map(|(existing_key, existing_elem)| {
            let existing_elem_cost = existing_elem.cost_1d(sat_prob, dissat_prob);
            existing_key.is_subtype(elem_key) && existing_elem_cost <= elem_cost
        })
        .fold(false, |acc, x| acc || x);
    if !is_worse {
        // If the element is not worse any element in the map, remove elements
        // whose subtype is the current element and have worse cost.
        *map = mem::replace(map, BTreeMap::new())
            .into_iter()
            .filter(|&(ref existing_key, ref existing_elem)| {
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
    sat_prob: f64,
    dissat_prob: Option<f64>,
) {
    let mut cast_stack: VecDeque<AstElemExt<Pk, Ctx>> = VecDeque::new();
    if insert_elem(map, astelem_ext.clone(), sat_prob, dissat_prob) {
        cast_stack.push_back(astelem_ext);
    }

    let casts: [Cast<Pk, Ctx>; 10] = all_casts::<Pk, Ctx>();
    while !cast_stack.is_empty() {
        let current = cast_stack.pop_front().unwrap();

        for i in 0..casts.len() {
            if let Ok(new_ext) = casts[i].cast(&current) {
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
    sat_prob: f64,
    dissat_prob: Option<f64>,
) -> Result<(), CompilerError> {
    insert_elem_closure(map, data, sat_prob, dissat_prob);

    if dissat_prob.is_some() {
        let casts: [Cast<Pk, Ctx>; 10] = all_casts::<Pk, Ctx>();

        for i in 0..casts.len() {
            for x in best_compilations(policy_cache, policy, sat_prob, None)?.values() {
                if let Ok(new_ext) = casts[i].cast(x) {
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
    sat_prob: f64,
    dissat_prob: Option<f64>,
) -> Result<BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>, CompilerError>
where
    Pk: MiniscriptKey,
    Ctx: ScriptContext,
{
    //Check the cache for hits
    let ord_sat_prob = OrdF64(sat_prob);
    let ord_dissat_prob = dissat_prob.and_then(|x| Some(OrdF64(x)));
    if let Some(ret) = policy_cache.get(&(policy.clone(), ord_sat_prob, ord_dissat_prob)) {
        return Ok(ret.clone());
    }

    let mut ret = BTreeMap::new();

    //handy macro for good looking code
    macro_rules! insert_wrap {
        ($x:expr) => {
            insert_best_wrapped(policy_cache, policy, &mut ret, $x, sat_prob, dissat_prob)?
        };
    }
    macro_rules! compile_binary {
        ($l:expr, $r:expr, $w: expr, $f: expr) => {
            compile_binary(
                policy_cache,
                policy,
                &mut ret,
                $l,
                $r,
                $w,
                sat_prob,
                dissat_prob,
                $f,
            )?
        };
    }
    macro_rules! compile_tern {
        ($a:expr, $b:expr, $c: expr, $w: expr) => {
            compile_tern(
                policy_cache,
                policy,
                &mut ret,
                $a,
                $b,
                $c,
                $w,
                sat_prob,
                dissat_prob,
            )?
        };
    }

    match *policy {
        Concrete::Unsatisfiable => {
            insert_wrap!(AstElemExt::terminal(Terminal::False));
        }
        Concrete::Trivial => {
            insert_wrap!(AstElemExt::terminal(Terminal::True));
        }
        Concrete::Key(ref pk) => {
            insert_wrap!(AstElemExt::terminal(Terminal::PkH(
                pk.to_pubkeyhash().clone()
            )));
            insert_wrap!(AstElemExt::terminal(Terminal::PkK(pk.clone())));
        }
        Concrete::After(n) => insert_wrap!(AstElemExt::terminal(Terminal::After(n))),
        Concrete::Older(n) => insert_wrap!(AstElemExt::terminal(Terminal::Older(n))),
        Concrete::Sha256(hash) => insert_wrap!(AstElemExt::terminal(Terminal::Sha256(hash))),
        Concrete::Hash256(hash) => insert_wrap!(AstElemExt::terminal(Terminal::Hash256(hash))),
        Concrete::Ripemd160(hash) => insert_wrap!(AstElemExt::terminal(Terminal::Ripemd160(hash))),
        Concrete::Hash160(hash) => insert_wrap!(AstElemExt::terminal(Terminal::Hash160(hash))),
        Concrete::And(ref subs) => {
            assert_eq!(subs.len(), 2, "and takes 2 args");
            let mut left = best_compilations(policy_cache, &subs[0], sat_prob, dissat_prob)?;
            let mut right = best_compilations(policy_cache, &subs[1], sat_prob, dissat_prob)?;
            let mut q_zero_right = best_compilations(policy_cache, &subs[1], sat_prob, None)?;
            let mut q_zero_left = best_compilations(policy_cache, &subs[0], sat_prob, None)?;

            compile_binary!(&mut left, &mut right, [1.0, 1.0], Terminal::AndB);
            compile_binary!(&mut right, &mut left, [1.0, 1.0], Terminal::AndB);
            compile_binary!(&mut left, &mut right, [1.0, 1.0], Terminal::AndV);
            compile_binary!(&mut right, &mut left, [1.0, 1.0], Terminal::AndV);
            let mut zero_comp = BTreeMap::new();
            zero_comp.insert(
                CompilationKey::from_type(
                    Type::from_false(),
                    ExtData::from_false().has_free_verify,
                    dissat_prob,
                ),
                AstElemExt::terminal(Terminal::False),
            );
            compile_tern!(&mut left, &mut q_zero_right, &mut zero_comp, [1.0, 0.0]);
            compile_tern!(&mut right, &mut q_zero_left, &mut zero_comp, [1.0, 0.0]);
        }
        Concrete::Or(ref subs) => {
            let total = (subs[0].0 + subs[1].0) as f64;
            let lw = subs[0].0 as f64 / total;
            let rw = subs[1].0 as f64 / total;

            //and-or
            if let (&Concrete::And(ref x), _) = (&subs[0].1, &subs[1].1) {
                let mut a1 = best_compilations(
                    policy_cache,
                    &x[0],
                    lw * sat_prob,
                    Some(dissat_prob.unwrap_or(0 as f64) + rw * sat_prob),
                )?;
                let mut a2 = best_compilations(policy_cache, &x[0], lw * sat_prob, None)?;

                let mut b1 = best_compilations(
                    policy_cache,
                    &x[1],
                    lw * sat_prob,
                    Some(dissat_prob.unwrap_or(0 as f64) + rw * sat_prob),
                )?;
                let mut b2 = best_compilations(policy_cache, &x[1], lw * sat_prob, None)?;

                let mut c =
                    best_compilations(policy_cache, &subs[1].1, rw * sat_prob, dissat_prob)?;

                compile_tern!(&mut a1, &mut b2, &mut c, [lw, rw]);
                compile_tern!(&mut b1, &mut a2, &mut c, [lw, rw]);
            };
            if let (_, &Concrete::And(ref x)) = (&subs[0].1, &subs[1].1) {
                let mut a1 = best_compilations(
                    policy_cache,
                    &x[0],
                    rw * sat_prob,
                    Some(dissat_prob.unwrap_or(0 as f64) + lw * sat_prob),
                )?;
                let mut a2 = best_compilations(policy_cache, &x[0], rw * sat_prob, None)?;

                let mut b1 = best_compilations(
                    policy_cache,
                    &x[1],
                    rw * sat_prob,
                    Some(dissat_prob.unwrap_or(0 as f64) + lw * sat_prob),
                )?;
                let mut b2 = best_compilations(policy_cache, &x[1], rw * sat_prob, None)?;

                let mut c =
                    best_compilations(policy_cache, &subs[0].1, lw * sat_prob, dissat_prob)?;

                compile_tern!(&mut a1, &mut b2, &mut c, [rw, lw]);
                compile_tern!(&mut b1, &mut a2, &mut c, [rw, lw]);
            };

            let dissat_probs = |w: f64| -> Vec<Option<f64>> {
                let mut dissat_set = Vec::new();
                dissat_set.push(Some(dissat_prob.unwrap_or(0 as f64) + w * sat_prob));
                dissat_set.push(Some(w * sat_prob));
                dissat_set.push(dissat_prob);
                dissat_set.push(None);
                dissat_set
            };

            let mut l_comp = vec![];
            let mut r_comp = vec![];

            for dissat_prob in dissat_probs(rw).iter() {
                let l = best_compilations(policy_cache, &subs[0].1, lw * sat_prob, *dissat_prob)?;
                l_comp.push(l);
            }

            for dissat_prob in dissat_probs(lw).iter() {
                let r = best_compilations(policy_cache, &subs[1].1, rw * sat_prob, *dissat_prob)?;
                r_comp.push(r);
            }
            compile_binary!(&mut l_comp[0], &mut r_comp[0], [lw, rw], Terminal::OrB);
            compile_binary!(&mut r_comp[0], &mut l_comp[0], [rw, lw], Terminal::OrB);

            compile_binary!(&mut l_comp[0], &mut r_comp[2], [lw, rw], Terminal::OrD);
            compile_binary!(&mut r_comp[0], &mut l_comp[2], [rw, lw], Terminal::OrD);

            compile_binary!(&mut l_comp[1], &mut r_comp[3], [lw, rw], Terminal::OrC);
            compile_binary!(&mut r_comp[1], &mut l_comp[3], [rw, lw], Terminal::OrC);

            compile_binary!(&mut l_comp[2], &mut r_comp[3], [lw, rw], Terminal::OrI);
            compile_binary!(&mut r_comp[2], &mut l_comp[3], [rw, lw], Terminal::OrI);

            compile_binary!(&mut l_comp[3], &mut r_comp[2], [lw, rw], Terminal::OrI);
            compile_binary!(&mut r_comp[3], &mut l_comp[2], [rw, lw], Terminal::OrI);
        }
        Concrete::Threshold(k, ref subs) => {
            let n = subs.len();
            let k_over_n = k as f64 / n as f64;

            let mut sub_ast = Vec::with_capacity(n);
            let mut sub_ext_data = Vec::with_capacity(n);

            let mut best_es = Vec::with_capacity(n);
            let mut best_ws = Vec::with_capacity(n);

            let mut min_value = (0 as usize, f64::INFINITY as f64);
            for (i, ast) in subs.iter().enumerate() {
                let sp = sat_prob * k_over_n;
                //Expressions must be dissatisfiable
                let dp = Some(dissat_prob.unwrap_or(0 as f64) + (1.0 - k_over_n) * sat_prob);
                let be = best(types::Base::B, policy_cache, ast, sp, dp)?;
                let bw = best(types::Base::W, policy_cache, ast, sp, dp)?;

                let diff = be.cost_1d(sp, dp) - bw.cost_1d(sp, dp);
                best_es.push((be.comp_ext_data, be));
                best_ws.push((bw.comp_ext_data, bw));

                if diff < min_value.1 {
                    min_value.0 = i;
                    min_value.1 = diff;
                }
            }
            sub_ext_data.push(best_es[min_value.0].0);
            sub_ast.push(Arc::clone(&best_es[min_value.0].1.ms));
            for (i, _ast) in subs.iter().enumerate() {
                if i != min_value.0 {
                    sub_ext_data.push(best_ws[i].0);
                    sub_ast.push(Arc::clone(&best_ws[i].1.ms));
                }
            }

            let ast = Terminal::Thresh(k, sub_ast);
            let ast_ext = AstElemExt {
                ms: Arc::new(
                    Miniscript::from_ast(ast)
                        .expect("threshold subs, which we just compiled, typeck"),
                ),
                comp_ext_data: CompilerExtData::threshold(k, n, |i| Ok(sub_ext_data[i]))
                    .expect("threshold subs, which we just compiled, typeck"),
            };
            insert_wrap!(ast_ext);

            let key_vec: Vec<Pk> = subs
                .iter()
                .filter_map(|s| {
                    if let Concrete::Key(ref pk) = *s {
                        Some(pk.clone())
                    } else {
                        None
                    }
                })
                .collect();

            if key_vec.len() == subs.len() && subs.len() <= MAX_PUBKEYS_PER_MULTISIG {
                insert_wrap!(AstElemExt::terminal(Terminal::Multi(k, key_vec)));
            }
            // Not a threshold, it's always more optimal to translate it to and()s as we save the
            // resulting threshold check (N EQUAL) in any case.
            else if k == subs.len() {
                let mut policy = subs.first().expect("No sub policy in thresh() ?").clone();
                for sub in &subs[1..] {
                    policy = Concrete::And(vec![sub.clone(), policy]);
                }

                ret = best_compilations(policy_cache, &policy, sat_prob, dissat_prob)?;
            }

            // FIXME: Should we also optimize thresh(1, subs) ?
        }
    }
    for k in ret.keys() {
        debug_assert_eq!(k.dissat_prob, ord_dissat_prob);
    }
    if ret.len() == 0 {
        // The only reason we are discarding elements out of compiler is because
        // compilations exceeded consensus and standardness limits or are non-malleable.
        // If there no possible compilations for any policies regardless of dissat
        // probability then it must have all compilations exceeded consensus or standardness
        // limits because we already checked that policy must have non-malleable compilations
        // before calling this compile function
        Err(CompilerError::LimitsExceeded)
    } else {
        policy_cache.insert((policy.clone(), ord_sat_prob, ord_dissat_prob), ret.clone());
        Ok(ret)
    }
}

/// Helper function to compile different types of binary fragments.
/// `sat_prob` and `dissat_prob` represent the sat and dissat probabilities of
/// root or. `weights` represent the odds for taking each sub branch
fn compile_binary<Pk, Ctx, F>(
    policy_cache: &mut PolicyCache<Pk, Ctx>,
    policy: &Concrete<Pk>,
    ret: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    left_comp: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    right_comp: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    weights: [f64; 2],
    sat_prob: f64,
    dissat_prob: Option<f64>,
    bin_func: F,
) -> Result<(), CompilerError>
where
    Pk: MiniscriptKey,
    Ctx: ScriptContext,
    F: Fn(Arc<Miniscript<Pk, Ctx>>, Arc<Miniscript<Pk, Ctx>>) -> Terminal<Pk, Ctx>,
{
    for l in left_comp.values_mut() {
        let lref = Arc::clone(&l.ms);
        for r in right_comp.values_mut() {
            let rref = Arc::clone(&r.ms);
            let ast = bin_func(Arc::clone(&lref), Arc::clone(&rref));
            l.comp_ext_data.branch_prob = Some(weights[0]);
            r.comp_ext_data.branch_prob = Some(weights[1]);
            if let Ok(new_ext) = AstElemExt::binary(ast, l, r) {
                insert_best_wrapped(policy_cache, policy, ret, new_ext, sat_prob, dissat_prob)?;
            }
        }
    }
    Ok(())
}

/// Helper function to compile different order of and_or fragments.
/// `sat_prob` and `dissat_prob` represent the sat and dissat probabilities of
/// root and_or node. `weights` represent the odds for taking each sub branch
fn compile_tern<Pk: MiniscriptKey, Ctx: ScriptContext>(
    policy_cache: &mut PolicyCache<Pk, Ctx>,
    policy: &Concrete<Pk>,
    ret: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    a_comp: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    b_comp: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    c_comp: &mut BTreeMap<CompilationKey, AstElemExt<Pk, Ctx>>,
    weights: [f64; 2],
    sat_prob: f64,
    dissat_prob: Option<f64>,
) -> Result<(), CompilerError> {
    for a in a_comp.values_mut() {
        let aref = Arc::clone(&a.ms);
        for b in b_comp.values_mut() {
            let bref = Arc::clone(&b.ms);
            for c in c_comp.values_mut() {
                let cref = Arc::clone(&c.ms);
                let ast = Terminal::AndOr(Arc::clone(&aref), Arc::clone(&bref), Arc::clone(&cref));
                a.comp_ext_data.branch_prob = Some(weights[0]);
                b.comp_ext_data.branch_prob = Some(weights[0]);
                c.comp_ext_data.branch_prob = Some(weights[1]);
                if let Ok(new_ext) = AstElemExt::ternary(ast, a, b, c) {
                    insert_best_wrapped(policy_cache, policy, ret, new_ext, sat_prob, dissat_prob)?;
                }
            }
        }
    }
    Ok(())
}

/// Obtain the best compilation of for p=1.0 and q=0
pub fn best_compilation<Pk: MiniscriptKey, Ctx: ScriptContext>(
    policy: &Concrete<Pk>,
) -> Result<Miniscript<Pk, Ctx>, CompilerError> {
    let mut policy_cache = PolicyCache::<Pk, Ctx>::new();
    let x = &*best_t(&mut policy_cache, policy, 1.0, None)?.ms;
    if !x.ty.mall.safe {
        Err(CompilerError::TopLevelNonSafe)
    } else if !x.ty.mall.non_malleable {
        Err(CompilerError::ImpossibleNonMalleableCompilation)
    } else {
        Ok(x.clone())
    }
}

/// Obtain the best B expression with given sat and dissat
fn best_t<Pk, Ctx>(
    policy_cache: &mut PolicyCache<Pk, Ctx>,
    policy: &Concrete<Pk>,
    sat_prob: f64,
    dissat_prob: Option<f64>,
) -> Result<AstElemExt<Pk, Ctx>, CompilerError>
where
    Pk: MiniscriptKey,
    Ctx: ScriptContext,
{
    best_compilations(policy_cache, policy, sat_prob, dissat_prob)?
        .into_iter()
        .filter(|&(key, _)| {
            key.ty.corr.base == types::Base::B
                && key.dissat_prob == dissat_prob.and_then(|x| Some(OrdF64(x)))
        })
        .map(|(_, val)| val)
        .min_by_key(|ext| OrdF64(ext.cost_1d(sat_prob, dissat_prob)))
        .ok_or(CompilerError::LimitsExceeded)
}

/// Obtain the <basic-type>.deu (e.g. W.deu, B.deu) expression with the given sat and dissat
fn best<Pk, Ctx>(
    basic_type: types::Base,
    policy_cache: &mut PolicyCache<Pk, Ctx>,
    policy: &Concrete<Pk>,
    sat_prob: f64,
    dissat_prob: Option<f64>,
) -> Result<AstElemExt<Pk, Ctx>, CompilerError>
where
    Pk: MiniscriptKey,
    Ctx: ScriptContext,
{
    best_compilations(policy_cache, policy, sat_prob, dissat_prob)?
        .into_iter()
        .filter(|&(ref key, ref val)| {
            key.ty.corr.base == basic_type
                && key.ty.corr.unit
                && val.ms.ty.mall.dissat == types::Dissat::Unique
                && key.dissat_prob == dissat_prob.and_then(|x| Some(OrdF64(x)))
        })
        .map(|(_, val)| val)
        .min_by_key(|ext| OrdF64(ext.cost_1d(sat_prob, dissat_prob)))
        .ok_or(CompilerError::LimitsExceeded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::blockdata::{opcodes, script};
    use bitcoin::{self, hashes, secp256k1};
    use std::collections::HashMap;
    use std::str::FromStr;
    use std::string::String;

    use miniscript::{satisfy, Legacy, Segwitv0};
    use policy::Liftable;
    use script_num_size;

    type SPolicy = Concrete<String>;
    type BPolicy = Concrete<bitcoin::PublicKey>;
    type DummySegwitAstElemExt = policy::compiler::AstElemExt<String, Segwitv0>;
    type SegwitMiniScript = Miniscript<bitcoin::PublicKey, Segwitv0>;

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
            &secp256k1::Message::from_slice(&sk[..]).expect("secret key"),
            &secp256k1::SecretKey::from_slice(&sk[..]).expect("secret key"),
        );
        (ret, sig)
    }

    fn policy_compile_lift_check(s: &str) -> Result<(), CompilerError> {
        let policy = SPolicy::from_str(s).expect("parse");
        let miniscript: Miniscript<String, Segwitv0> = policy.compile()?;

        assert_eq!(
            policy.lift().unwrap().sorted(),
            miniscript.lift().unwrap().sorted()
        );
        Ok(())
    }

    #[test]
    fn compile_timelocks() {
        // artificially create a policy that is problematic and try to compile
        let pol: SPolicy = Concrete::And(vec![
            Concrete::Key("A".to_string()),
            Concrete::And(vec![Concrete::After(9), Concrete::After(1000_000_000)]),
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
        assert_eq!(
            policy_compile_lift_check("after(9)"),
            Err(CompilerError::TopLevelNonSafe)
        );
        assert_eq!(
            policy_compile_lift_check("older(1)"),
            Err(CompilerError::TopLevelNonSafe)
        );
        assert_eq!(
            policy_compile_lift_check(
                "sha256(1111111111111111111111111111111111111111111111111111111111111111)"
            ),
            Err(CompilerError::TopLevelNonSafe)
        );
        assert!(policy_compile_lift_check("and(pk(A),pk(B))").is_ok());
        assert!(policy_compile_lift_check("or(pk(A),pk(B))").is_ok());
        assert!(policy_compile_lift_check("thresh(2,pk(A),pk(B),pk(C))").is_ok());

        assert_eq!(
            policy_compile_lift_check("thresh(2,after(9),after(9),pk(A))"),
            Err(CompilerError::TopLevelNonSafe)
        );

        assert_eq!(
            policy_compile_lift_check("and(pk(A),or(after(9),after(9)))"),
            Err(CompilerError::ImpossibleNonMalleableCompilation)
        );
    }

    #[test]
    fn compile_q() {
        let policy = SPolicy::from_str("or(1@and(pk(A),pk(B)),127@pk(C))").expect("parsing");
        let compilation: DummySegwitAstElemExt =
            best_t(&mut BTreeMap::new(), &policy, 1.0, None).unwrap();

        assert_eq!(compilation.cost_1d(1.0, None), 88.0 + 74.109375);
        assert_eq!(
            policy.lift().unwrap().sorted(),
            compilation.ms.lift().unwrap().sorted()
        );

        let policy = SPolicy::from_str(
                "and(and(and(or(127@thresh(2,pk(A),pk(B),thresh(2,or(127@pk(A),1@pk(B)),after(100),or(and(pk(C),after(200)),and(pk(D),sha256(66687aadf862bd776c8fc18b8e9f8e20089714856ee233b3902a591d0d5f2925))),pk(E))),1@pk(F)),sha256(66687aadf862bd776c8fc18b8e9f8e20089714856ee233b3902a591d0d5f2925)),or(127@pk(G),1@after(300))),or(127@after(400),pk(H)))"
            ).expect("parsing");
        let compilation: DummySegwitAstElemExt =
            best_t(&mut BTreeMap::new(), &policy, 1.0, None).unwrap();

        assert_eq!(compilation.cost_1d(1.0, None), 437.0 + 299.4003295898438);
        assert_eq!(
            policy.lift().unwrap().sorted(),
            compilation.ms.lift().unwrap().sorted()
        );
    }

    #[test]
    fn compile_misc() {
        let (keys, sig) = pubkeys_and_a_sig(10);
        let key_pol: Vec<BPolicy> = keys.iter().map(|k| Concrete::Key(*k)).collect();

        let policy: BPolicy = Concrete::Key(keys[0].clone());
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
            (127, Concrete::Threshold(3, key_pol[0..5].to_owned())),
            (
                1,
                Concrete::And(vec![
                    Concrete::Older(10000),
                    Concrete::Threshold(2, key_pol[5..8].to_owned()),
                ]),
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
            keys[5].to_pubkeyhash(),
            keys[6].to_pubkeyhash(),
            keys[7].to_pubkeyhash()
        );

        assert_eq!(ms, ms_comp_res);

        let mut abs = policy.lift().unwrap();
        assert_eq!(abs.n_keys(), 8);
        assert_eq!(abs.minimum_n_keys(), Some(2));
        abs = abs.at_age(10000);
        assert_eq!(abs.n_keys(), 8);
        assert_eq!(abs.minimum_n_keys(), Some(2));
        abs = abs.at_age(9999);
        assert_eq!(abs.n_keys(), 5);
        assert_eq!(abs.minimum_n_keys(), Some(3));
        abs = abs.at_age(0);
        assert_eq!(abs.n_keys(), 5);
        assert_eq!(abs.minimum_n_keys(), Some(3));

        let bitcoinsig = bitcoin::EcdsaSig {
            sig,
            hash_ty: bitcoin::EcdsaSigHashType::All,
        };
        let sigvec = bitcoinsig.to_vec();

        let no_sat = HashMap::<bitcoin::PublicKey, bitcoin::EcdsaSig>::new();
        let mut left_sat = HashMap::<bitcoin::PublicKey, bitcoin::EcdsaSig>::new();
        let mut right_sat =
            HashMap::<hashes::hash160::Hash, (bitcoin::PublicKey, bitcoin::EcdsaSig)>::new();

        for i in 0..5 {
            left_sat.insert(keys[i], bitcoinsig);
        }
        for i in 5..8 {
            right_sat.insert(keys[i].to_pubkeyhash(), (keys[i], bitcoinsig));
        }

        assert!(ms.satisfy(no_sat).is_err());
        assert!(ms.satisfy(&left_sat).is_ok());
        assert!(ms.satisfy((&right_sat, satisfy::Older(10001))).is_ok());
        //timelock not met
        assert!(ms.satisfy((&right_sat, satisfy::Older(9999))).is_err());

        assert_eq!(
            ms.satisfy((left_sat, satisfy::Older(9999))).unwrap(),
            vec![
                // sat for left branch
                vec![],
                sigvec.clone(),
                sigvec.clone(),
                sigvec.clone(),
            ]
        );

        assert_eq!(
            ms.satisfy((right_sat, satisfy::Older(10000))).unwrap(),
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

        // Up until 20 keys, thresh should be compiled to a multi no matter the value of k
        for k in 1..4 {
            let small_thresh: BPolicy = policy_str!(
                "thresh({},pk({}),pk({}),pk({}))",
                k,
                keys[0],
                keys[1],
                keys[2]
            );
            let small_thresh_ms: SegwitMiniScript = small_thresh.compile().unwrap();
            let small_thresh_ms_expected: SegwitMiniScript =
                ms_str!("multi({},{},{},{})", k, keys[0], keys[1], keys[2]);
            assert_eq!(small_thresh_ms, small_thresh_ms_expected);
        }

        // Above 20 keys, thresh is compiled to a combination of and()s if it's a N of N,
        // and to a ms thresh otherwise.
        // k = 1 (or 2) does not compile, see https://github.com/rust-bitcoin/rust-miniscript/issues/114
        for k in &[10, 15, 21] {
            let pubkeys: Vec<Concrete<bitcoin::PublicKey>> =
                keys.iter().map(|pubkey| Concrete::Key(*pubkey)).collect();
            let big_thresh = Concrete::Threshold(*k, pubkeys);
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
    fn segwit_limits() {
        // Hit the maximum witness script size limit.
        // or(thresh(52, [pubkey; 52]), thresh(52, [pubkey; 52])) results in a 3642-bytes long
        // witness script with only 54 stack elements
        let (keys, _) = pubkeys_and_a_sig(104);
        let keys_a: Vec<Concrete<bitcoin::PublicKey>> = keys[..keys.len() / 2]
            .iter()
            .map(|pubkey| Concrete::Key(*pubkey))
            .collect();
        let keys_b: Vec<Concrete<bitcoin::PublicKey>> = keys[keys.len() / 2..]
            .iter()
            .map(|pubkey| Concrete::Key(*pubkey))
            .collect();

        let thresh_res: Result<SegwitMiniScript, _> = Concrete::Or(vec![
            (1, Concrete::Threshold(keys_a.len(), keys_a)),
            (1, Concrete::Threshold(keys_b.len(), keys_b)),
        ])
        .compile();
        let script_size = thresh_res.clone().and_then(|m| Ok(m.script_size()));
        assert_eq!(
            thresh_res,
            Err(CompilerError::LimitsExceeded),
            "Compilation succeeded with a witscript size of '{:?}'",
            script_size,
        );

        // Hit the maximum witness stack elements limit
        let (keys, _) = pubkeys_and_a_sig(100);
        let keys: Vec<Concrete<bitcoin::PublicKey>> =
            keys.iter().map(|pubkey| Concrete::Key(*pubkey)).collect();
        let thresh_res: Result<SegwitMiniScript, _> =
            Concrete::Threshold(keys.len(), keys).compile();
        let n_elements = thresh_res
            .clone()
            .and_then(|m| Ok(m.max_satisfaction_witness_elements()));
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
        let keys: Vec<Concrete<bitcoin::PublicKey>> =
            keys.iter().map(|pubkey| Concrete::Key(*pubkey)).collect();
        let thresh_res: Result<SegwitMiniScript, _> =
            Concrete::Threshold(keys.len() - 1, keys).compile();
        let ops_count = thresh_res.clone().and_then(|m| Ok(m.ext.ops_count_sat));
        assert_eq!(
            thresh_res,
            Err(CompilerError::LimitsExceeded),
            "Compilation succeeded with '{:?}' OP count (sat)",
            ops_count,
        );
        // For legacy too..
        let (keys, _) = pubkeys_and_a_sig(68);
        let keys: Vec<Concrete<bitcoin::PublicKey>> =
            keys.iter().map(|pubkey| Concrete::Key(*pubkey)).collect();
        let thresh_res = Concrete::Threshold(keys.len() - 1, keys).compile::<Legacy>();
        let ops_count = thresh_res.clone().and_then(|m| Ok(m.ext.ops_count_sat));
        assert_eq!(
            thresh_res,
            Err(CompilerError::LimitsExceeded),
            "Compilation succeeded with '{:?}' OP count (sat)",
            ops_count,
        );

        // Test that we refuse to compile policies with duplicated keys
        let (keys, _) = pubkeys_and_a_sig(1);
        let key = Concrete::Key(keys[0]);
        let res = Concrete::Or(vec![(1, key.clone()), (1, key.clone())]).compile::<Segwitv0>();
        assert_eq!(
            res,
            Err(CompilerError::PolicyError(
                policy::concrete::PolicyError::DuplicatePubKeys
            ))
        );
        // Same for legacy
        let res = Concrete::Or(vec![(1, key.clone()), (1, key)]).compile::<Legacy>();
        assert_eq!(
            res,
            Err(CompilerError::PolicyError(
                policy::concrete::PolicyError::DuplicatePubKeys
            ))
        );
    }
}

#[cfg(all(test, feature = "unstable"))]
mod benches {
    use std::str::FromStr;
    use test::{black_box, Bencher};

    use super::{CompilerError, Concrete};
    use miniscript::Segwitv0;
    use Miniscript;
    type SegwitMsRes = Result<Miniscript<String, Segwitv0>, CompilerError>;
    #[bench]
    pub fn compile_basic(bh: &mut Bencher) {
        let h = (0..64).map(|_| "a").collect::<String>();
        let pol = Concrete::<String>::from_str(&format!(
            "and(thresh(2,and(sha256({}),or(sha256({}),pk(A))),pk(B),pk(C),pk(D),sha256({})),pk(E))",
            h, h, h
        ))
        .expect("parsing");
        bh.iter(|| {
            let pt: SegwitMsRes = pol.compile();
            black_box(pt).unwrap();
        });
    }

    #[bench]
    pub fn compile_large(bh: &mut Bencher) {
        let h = (0..64).map(|_| "a").collect::<String>();
        let pol = Concrete::<String>::from_str(
            &format!("or(pk(L),thresh(9,sha256({}),pk(A),pk(B),and(or(pk(C),pk(D)),pk(E)),after(100),pk(F),pk(G),pk(H),pk(I),and(pk(J),pk(K))))", h)
        ).expect("parsing");
        bh.iter(|| {
            let pt: SegwitMsRes = pol.compile();
            black_box(pt).unwrap();
        });
    }

    #[bench]
    pub fn compile_xlarge(bh: &mut Bencher) {
        let pol = Concrete::<String>::from_str(
            "or(pk(A),thresh(4,pk(B),older(100),pk(C),and(after(100),or(pk(D),or(pk(E),and(pk(F),thresh(2,pk(G),or(pk(H),and(thresh(5,pk(I),or(pk(J),pk(K)),pk(L),pk(M),pk(N),pk(O),pk(P),pk(Q),pk(R),pk(S),pk(T)),pk(U))),pk(V),or(and(pk(W),pk(X)),pk(Y)),after(100)))))),pk(Z)))"
        ).expect("parsing");
        bh.iter(|| {
            let pt: SegwitMsRes = pol.compile();
            black_box(pt).unwrap();
        });
    }
}
