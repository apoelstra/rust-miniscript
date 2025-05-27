// SPDX-License-Identifier: CC0-1.0

//! Script Decoder
//!
//! Functionality to parse a Bitcoin Script into a `Miniscript`
//!

use core::{fmt, mem};
#[cfg(feature = "std")]
use std::error;

use bitcoin::hashes::{hash160, ripemd160, sha256, Hash};
use sync::Arc;

use crate::iter::TreeLike;
use crate::miniscript::lex::{Token as Tk, TokenIter};
use crate::miniscript::limits::{MAX_PUBKEYS_IN_CHECKSIGADD, MAX_PUBKEYS_PER_MULTISIG};
use crate::miniscript::ScriptContext;
use crate::prelude::*;
use crate::primitives::threshold;
#[cfg(doc)]
use crate::Descriptor;
use crate::{
    hash256, AbsLockTime, Miniscript, MiniscriptKey, RelLockTime, Threshold, ToPublicKey,
    ValidationParams,
};

/// Trait for parsing keys from byte slices
pub trait ParseableKey: Sized + ToPublicKey + private::Sealed {
    /// Parse a key from slice
    fn from_slice(sl: &[u8]) -> Result<Self, KeyError>;
}

impl ParseableKey for bitcoin::PublicKey {
    fn from_slice(sl: &[u8]) -> Result<Self, KeyError> {
        bitcoin::PublicKey::from_slice(sl).map_err(KeyError::Full)
    }
}

impl ParseableKey for bitcoin::secp256k1::XOnlyPublicKey {
    fn from_slice(sl: &[u8]) -> Result<Self, KeyError> {
        bitcoin::secp256k1::XOnlyPublicKey::from_slice(sl).map_err(KeyError::XOnly)
    }
}

/// Private Mod to prevent downstream from implementing this public trait
mod private {

    pub trait Sealed {}

    // Implement for those same types, but no others.
    impl Sealed for bitcoin::PublicKey {}
    impl Sealed for bitcoin::secp256k1::XOnlyPublicKey {}
}

#[derive(Copy, Clone, Debug)]
enum NonTerm {
    Expression,
    WExpression,
    Swap,
    MaybeAndV,
    Alt,
    Check,
    DupIf,
    Verify,
    NonZero,
    ZeroNotEqual,
    AndV,
    AndB,
    Tern,
    OrB,
    OrD,
    OrC,
    ThreshW { k: usize, n: usize },
    ThreshE { k: usize, n: usize },
    // could be or_d, or_c, or_i, d:, n:
    EndIf,
    // could be or_d, or_c
    EndIfNotIf,
    // could be or_i or tern
    EndIfElse,
}
/// All AST elements.
///
/// This variant is the inner Miniscript variant that allows the user to bypass some of the
/// miniscript rules. You should *never* construct `Terminal` directly. This is only exposed to
/// external users to allow matching on the [`Miniscript`].
///
/// The average user should always use the [`Descriptor`] APIs. Advanced users who want deal
/// with Miniscript ASTs should use the [`Miniscript`] APIs.
pub enum Terminal<Pk: MiniscriptKey, Ctx: ScriptContext> {
    /// `1`
    True,
    /// `0`
    False,
    // pubkey checks
    /// `<key>`
    PkK(Pk),
    /// `DUP HASH160 <keyhash> EQUALVERIFY`
    PkH(Pk),
    /// Only for parsing PkH for Script. These raw descriptors are not yet specified in miniscript.
    /// We only this variant internally for inferring miniscripts from raw Scripts.
    /// It is not possible to construct this variant from any of the Miniscript APIs.
    /// We don't have a generic over here because we don't want to user to have any abstract reasoning
    /// over raw descriptors.
    RawPkH(hash160::Hash),
    // timelocks
    /// `n CHECKLOCKTIMEVERIFY`
    After(AbsLockTime),
    /// `n CHECKSEQUENCEVERIFY`
    Older(RelLockTime),
    // hashlocks
    /// `SIZE 32 EQUALVERIFY SHA256 <hash> EQUAL`
    Sha256(Pk::Sha256),
    /// `SIZE 32 EQUALVERIFY HASH256 <hash> EQUAL`
    Hash256(Pk::Hash256),
    /// `SIZE 32 EQUALVERIFY RIPEMD160 <hash> EQUAL`
    Ripemd160(Pk::Ripemd160),
    /// `SIZE 32 EQUALVERIFY HASH160 <hash> EQUAL`
    Hash160(Pk::Hash160),
    // Wrappers
    /// `TOALTSTACK [E] FROMALTSTACK`
    Alt(Arc<Miniscript<Pk, Ctx>>),
    /// `SWAP [E1]`
    Swap(Arc<Miniscript<Pk, Ctx>>),
    /// `[Kt]/[Ke] CHECKSIG`
    Check(Arc<Miniscript<Pk, Ctx>>),
    /// `DUP IF [V] ENDIF`
    DupIf(Arc<Miniscript<Pk, Ctx>>),
    /// `[T] VERIFY`
    Verify(Arc<Miniscript<Pk, Ctx>>),
    /// `SIZE 0NOTEQUAL IF [Fn] ENDIF`
    NonZero(Arc<Miniscript<Pk, Ctx>>),
    /// `[X] 0NOTEQUAL`
    ZeroNotEqual(Arc<Miniscript<Pk, Ctx>>),
    // Conjunctions
    /// `[V] [T]/[V]/[F]/[Kt]`
    AndV(Arc<Miniscript<Pk, Ctx>>, Arc<Miniscript<Pk, Ctx>>),
    /// `[E] [W] BOOLAND`
    AndB(Arc<Miniscript<Pk, Ctx>>, Arc<Miniscript<Pk, Ctx>>),
    /// `[various] NOTIF [various] ELSE [various] ENDIF`
    AndOr(Arc<Miniscript<Pk, Ctx>>, Arc<Miniscript<Pk, Ctx>>, Arc<Miniscript<Pk, Ctx>>),
    // Disjunctions
    /// `[E] [W] BOOLOR`
    OrB(Arc<Miniscript<Pk, Ctx>>, Arc<Miniscript<Pk, Ctx>>),
    /// `[E] IFDUP NOTIF [T]/[E] ENDIF`
    OrD(Arc<Miniscript<Pk, Ctx>>, Arc<Miniscript<Pk, Ctx>>),
    /// `[E] NOTIF [V] ENDIF`
    OrC(Arc<Miniscript<Pk, Ctx>>, Arc<Miniscript<Pk, Ctx>>),
    /// `IF [various] ELSE [various] ENDIF`
    OrI(Arc<Miniscript<Pk, Ctx>>, Arc<Miniscript<Pk, Ctx>>),
    // Thresholds
    /// `[E] ([W] ADD)* k EQUAL`
    Thresh(Threshold<Arc<Miniscript<Pk, Ctx>>, 0>),
    /// `k (<key>)* n CHECKMULTISIG`
    Multi(Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>),
    /// `<key> CHECKSIG (<key> CHECKSIGADD)*(n-1) k NUMEQUAL`
    MultiA(Threshold<Pk, MAX_PUBKEYS_IN_CHECKSIGADD>),
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Clone for Terminal<Pk, Ctx> {
    /// We implement clone as a "deep clone" which reconstructs the entire tree.
    ///
    /// If users just want to clone Arcs they can use Arc::clone themselves.
    fn clone(&self) -> Self {
        match self {
            Terminal::PkK(ref p) => Terminal::PkK(p.clone()),
            Terminal::PkH(ref p) => Terminal::PkH(p.clone()),
            Terminal::RawPkH(ref p) => Terminal::RawPkH(*p),
            Terminal::After(ref n) => Terminal::After(*n),
            Terminal::Older(ref n) => Terminal::Older(*n),
            Terminal::Sha256(ref x) => Terminal::Sha256(x.clone()),
            Terminal::Hash256(ref x) => Terminal::Hash256(x.clone()),
            Terminal::Ripemd160(ref x) => Terminal::Ripemd160(x.clone()),
            Terminal::Hash160(ref x) => Terminal::Hash160(x.clone()),
            Terminal::True => Terminal::True,
            Terminal::False => Terminal::False,
            Terminal::Alt(ref sub) => Terminal::Alt(Arc::new(Miniscript::clone(sub))),
            Terminal::Swap(ref sub) => Terminal::Swap(Arc::new(Miniscript::clone(sub))),
            Terminal::Check(ref sub) => Terminal::Check(Arc::new(Miniscript::clone(sub))),
            Terminal::DupIf(ref sub) => Terminal::DupIf(Arc::new(Miniscript::clone(sub))),
            Terminal::Verify(ref sub) => Terminal::Verify(Arc::new(Miniscript::clone(sub))),
            Terminal::NonZero(ref sub) => Terminal::NonZero(Arc::new(Miniscript::clone(sub))),
            Terminal::ZeroNotEqual(ref sub) => {
                Terminal::ZeroNotEqual(Arc::new(Miniscript::clone(sub)))
            }
            Terminal::AndV(ref left, ref right) => Terminal::AndV(
                Arc::new(Miniscript::clone(left)),
                Arc::new(Miniscript::clone(right)),
            ),
            Terminal::AndB(ref left, ref right) => Terminal::AndB(
                Arc::new(Miniscript::clone(left)),
                Arc::new(Miniscript::clone(right)),
            ),
            Terminal::AndOr(ref a, ref b, ref c) => Terminal::AndOr(
                Arc::new(Miniscript::clone(a)),
                Arc::new(Miniscript::clone(b)),
                Arc::new(Miniscript::clone(c)),
            ),
            Terminal::OrB(ref left, ref right) => {
                Terminal::OrB(Arc::new(Miniscript::clone(left)), Arc::new(Miniscript::clone(right)))
            }
            Terminal::OrD(ref left, ref right) => {
                Terminal::OrD(Arc::new(Miniscript::clone(left)), Arc::new(Miniscript::clone(right)))
            }
            Terminal::OrC(ref left, ref right) => {
                Terminal::OrC(Arc::new(Miniscript::clone(left)), Arc::new(Miniscript::clone(right)))
            }
            Terminal::OrI(ref left, ref right) => {
                Terminal::OrI(Arc::new(Miniscript::clone(left)), Arc::new(Miniscript::clone(right)))
            }
            Terminal::Thresh(ref thresh) => {
                Terminal::Thresh(thresh.map_ref(|child| Arc::new(Miniscript::clone(child))))
            }
            Terminal::Multi(ref thresh) => Terminal::Multi(thresh.clone()),
            Terminal::MultiA(ref thresh) => Terminal::MultiA(thresh.clone()),
        }
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> PartialEq for Terminal<Pk, Ctx> {
    fn eq(&self, other: &Self) -> bool {
        for (me, you) in self.pre_order_iter().zip(other.pre_order_iter()) {
            match (me, you) {
                (Terminal::PkK(key1), Terminal::PkK(key2)) if key1 != key2 => return false,
                (Terminal::PkH(key1), Terminal::PkH(key2)) if key1 != key2 => return false,
                (Terminal::RawPkH(h1), Terminal::RawPkH(h2)) if h1 != h2 => return false,
                (Terminal::After(t1), Terminal::After(t2)) if t1 != t2 => return false,
                (Terminal::Older(t1), Terminal::Older(t2)) if t1 != t2 => return false,
                (Terminal::Sha256(h1), Terminal::Sha256(h2)) if h1 != h2 => return false,
                (Terminal::Hash256(h1), Terminal::Hash256(h2)) if h1 != h2 => return false,
                (Terminal::Ripemd160(h1), Terminal::Ripemd160(h2)) if h1 != h2 => return false,
                (Terminal::Hash160(h1), Terminal::Hash160(h2)) if h1 != h2 => return false,
                (Terminal::Multi(th1), Terminal::Multi(th2)) if th1 != th2 => return false,
                (Terminal::MultiA(th1), Terminal::MultiA(th2)) if th1 != th2 => return false,
                _ => {
                    if mem::discriminant(me) != mem::discriminant(you) {
                        return false;
                    }
                }
            }
        }
        true
    }
}
impl<Pk: MiniscriptKey, Ctx: ScriptContext> Eq for Terminal<Pk, Ctx> {}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> core::hash::Hash for Terminal<Pk, Ctx> {
    fn hash<H: core::hash::Hasher>(&self, hasher: &mut H) {
        for term in self.pre_order_iter() {
            mem::discriminant(term).hash(hasher);
            match term {
                Terminal::PkK(key) => key.hash(hasher),
                Terminal::PkH(key) => key.hash(hasher),
                Terminal::RawPkH(h) => h.hash(hasher),
                Terminal::After(t) => t.hash(hasher),
                Terminal::Older(t) => t.hash(hasher),
                Terminal::Sha256(h) => h.hash(hasher),
                Terminal::Hash256(h) => h.hash(hasher),
                Terminal::Ripemd160(h) => h.hash(hasher),
                Terminal::Hash160(h) => h.hash(hasher),
                Terminal::Thresh(th) => {
                    th.k().hash(hasher);
                    th.n().hash(hasher);
                    // The actual children will be hashed when we iterate
                }
                Terminal::Multi(th) => th.hash(hasher),
                Terminal::MultiA(th) => th.hash(hasher),
                _ => {}
            }
        }
    }
}

macro_rules! match_token {
    // Base case
    ($tokens:expr => $sub:expr,) => { $sub };
    // Recursive case
    ($tokens:expr, $($first:pat $(,$rest:pat)* => $sub:expr,)*) => {
        match $tokens.next() {
            $(
                Some($first) => match_token!($tokens $(,$rest)* => $sub,),
            )*
            Some(other) => return Err(Error::Unexpected(other)),
            None => return Err(Error::UnexpectedStart),
        }
    };
}

///Vec representing terminals stack while decoding.
#[derive(Debug)]
struct TerminalStack<Pk: MiniscriptKey, Ctx: ScriptContext>(Vec<Miniscript<Pk, Ctx>>);

impl<Pk: MiniscriptKey, Ctx: ScriptContext> TerminalStack<Pk, Ctx> {
    /// Wrapper around self.0.pop()
    fn pop(&mut self) -> Option<Miniscript<Pk, Ctx>> { self.0.pop() }

    /// Wrapper around self.0.push()
    fn push(&mut self, ms: Miniscript<Pk, Ctx>) { self.0.push(ms) }

    /// reduce, type check and push a 0-arg node
    fn reduce0(&mut self, ms: Terminal<Pk, Ctx>, params: &ValidationParams) -> Result<(), Error> {
        let ms = Miniscript::from_ast(ms, params).map_err(Error::Construct)?;
        self.0.push(ms);
        Ok(())
    }

    ///reduce, type check and push a 1-arg node
    fn reduce1<F>(&mut self, params: &ValidationParams, wrap: F) -> Result<(), Error>
    where
        F: FnOnce(Arc<Miniscript<Pk, Ctx>>) -> Terminal<Pk, Ctx>,
    {
        let top = self.pop().unwrap();
        let wrapped_ms = wrap(Arc::new(top));

        self.reduce0(wrapped_ms, params)
    }

    ///reduce, type check and push a 2-arg node
    fn reduce2<F>(&mut self, params: &ValidationParams, wrap: F) -> Result<(), Error>
    where
        F: FnOnce(Arc<Miniscript<Pk, Ctx>>, Arc<Miniscript<Pk, Ctx>>) -> Terminal<Pk, Ctx>,
    {
        let left = self.pop().unwrap();
        let right = self.pop().unwrap();

        let wrapped_ms = wrap(Arc::new(left), Arc::new(right));

        self.reduce0(wrapped_ms, params)
    }
}

/// Parse a script fragment into an `Miniscript`
#[allow(unreachable_patterns)]
pub fn decode<Ctx: ScriptContext>(
    tokens: &mut TokenIter,
    params: &ValidationParams,
) -> Result<Miniscript<Ctx::Key, Ctx>, Error> {
    let mut non_term = Vec::with_capacity(tokens.len());
    let mut term = TerminalStack(Vec::with_capacity(tokens.len()));

    // top level cannot be swap, must be B
    non_term.push(NonTerm::MaybeAndV);
    non_term.push(NonTerm::Expression);
    loop {
        match non_term.pop() {
            Some(NonTerm::Expression) => {
                match_token!(
                    tokens,
                    // pubkey
                    Tk::Bytes33(pk) => {
                        let ret = Ctx::Key::from_slice(&pk)
                            .map_err(|e| Error::PubKeyCtxError(e, Ctx::name_str()))?;
                        term.push(Miniscript::pk_k(ret));
                    },
                    Tk::Bytes65(pk) => {
                        let ret = Ctx::Key::from_slice(&pk)
                            .map_err(|e| Error::PubKeyCtxError(e, Ctx::name_str()))?;
                        term.push(Miniscript::pk_k(ret));
                    },
                    // Note this does not collide with hash32 because they always followed by equal
                    // and would be parsed in different branch. If we get a naked Bytes32, it must be
                    // a x-only key
                    // In miniscript spec, bytes32 only occurs at three places.
                    // - during parsing XOnly keys in Pk fragment
                    // - during parsing XOnly keys in MultiA fragment
                    // - checking for 32 bytes hashlocks (sha256/hash256)
                    // The second case(MultiA) is disambiguated using NumEqual which is not used anywhere in miniscript
                    // The third case can only occur hashlocks is disambiguated because hashlocks start from equal, and
                    // it is impossible for any K type fragment to be followed by EQUAL in miniscript spec. Thus, EQUAL
                    // after bytes32 means bytes32 is in a hashlock
                    // Finally for the first case, K being parsed as a solo expression is a Pk type
                    Tk::Bytes32(pk) => {
                        let ret = Ctx::Key::from_slice(&pk).map_err(|e| Error::PubKeyCtxError(e, Ctx::name_str()))?;
                        term.push(Miniscript::pk_k(ret));
                    },
                    // checksig
                    Tk::CheckSig => {
                        non_term.push(NonTerm::Check);
                        non_term.push(NonTerm::Expression);
                    },
                    // pubkeyhash and [T] VERIFY and [T] 0NOTEQUAL
                    Tk::Verify => match_token!(
                        tokens,
                        Tk::Equal => match_token!(
                            tokens,
                            Tk::Hash20(hash) => match_token!(
                                tokens,
                                Tk::Hash160 => match_token!(
                                    tokens,
                                    Tk::Dup => {
                                        term.push(Miniscript::expr_raw_pkh(
                                            hash160::Hash::from_byte_array(hash)
                                        ));
                                    },
                                    Tk::Verify, Tk::Equal, Tk::Num(32), Tk::Size => {
                                        non_term.push(NonTerm::Verify);
                                        term.push(Miniscript::hash160(
                                            hash160::Hash::from_byte_array(hash)
                                        ));
                                    },
                                ),
                                Tk::Ripemd160, Tk::Verify, Tk::Equal, Tk::Num(32), Tk::Size => {
                                    non_term.push(NonTerm::Verify);
                                    term.push(Miniscript::ripemd160(
                                        ripemd160::Hash::from_byte_array(hash)
                                    ));
                                },
                            ),
                            // Tk::Hash20(hash),
                            Tk::Bytes32(hash) => match_token!(
                                tokens,
                                Tk::Sha256, Tk::Verify, Tk::Equal, Tk::Num(32), Tk::Size => {
                                    non_term.push(NonTerm::Verify);
                                    term.push(Miniscript::sha256(
                                        sha256::Hash::from_byte_array(hash)
                                    ));
                                },
                                Tk::Hash256, Tk::Verify, Tk::Equal, Tk::Num(32), Tk::Size => {
                                    non_term.push(NonTerm::Verify);
                                    term.push(Miniscript::hash256(
                                        hash256::Hash::from_byte_array(hash)
                                    ));
                                },
                            ),
                            Tk::Num(k) => {
                                non_term.push(NonTerm::Verify);
                                non_term.push(NonTerm::ThreshW {
                                    k: k as usize,
                                    n: 0
                                });
                            },
                        ),
                        x => {
                            tokens.un_next(x);
                            non_term.push(NonTerm::Verify);
                            non_term.push(NonTerm::Expression);
                        },
                    ),
                    Tk::ZeroNotEqual => {
                        non_term.push(NonTerm::ZeroNotEqual);
                        non_term.push(NonTerm::Expression);
                    },
                    // timelocks
                    Tk::CheckSequenceVerify, Tk::Num(n)
                        => term.push(Miniscript::older(RelLockTime::from_consensus(n).map_err(Error::RelativeLockTime)?)),
                    Tk::CheckLockTimeVerify, Tk::Num(n)
                        => term.push(Miniscript::after(AbsLockTime::from_consensus(n).map_err(Error::AbsoluteLockTime)?)),
                    // hashlocks
                    Tk::Equal => match_token!(
                        tokens,
                        Tk::Bytes32(hash) => match_token!(
                            tokens,
                            Tk::Sha256,
                            Tk::Verify,
                            Tk::Equal,
                            Tk::Num(32),
                            Tk::Size => term.push(Miniscript::sha256(
                                sha256::Hash::from_byte_array(hash)
                            )),
                            Tk::Hash256,
                            Tk::Verify,
                            Tk::Equal,
                            Tk::Num(32),
                            Tk::Size => term.push(Miniscript::hash256(
                                hash256::Hash::from_byte_array(hash)
                            )),
                        ),
                        Tk::Hash20(hash) => match_token!(
                            tokens,
                            Tk::Ripemd160,
                            Tk::Verify,
                            Tk::Equal,
                            Tk::Num(32),
                            Tk::Size => term.push(Miniscript::ripemd160(
                                ripemd160::Hash::from_byte_array(hash)
                            )),
                            Tk::Hash160,
                            Tk::Verify,
                            Tk::Equal,
                            Tk::Num(32),
                            Tk::Size => term.push(Miniscript::hash160(
                                hash160::Hash::from_byte_array(hash)
                            )),
                        ),
                        // thresholds
                        Tk::Num(k) => {
                            non_term.push(NonTerm::ThreshW {
                                k: k as usize,
                                n: 0
                            });
                            // note we do *not* expect an `Expression` here;
                            // the `ThreshW` handler below will look for
                            // `OP_ADD` or not and do the right thing
                        },
                    ),
                    // most other fragments
                    Tk::Num(0) => term.push(Miniscript::FALSE),
                    Tk::Num(1) => term.push(Miniscript::TRUE),
                    Tk::EndIf => {
                        non_term.push(NonTerm::EndIf);
                        non_term.push(NonTerm::MaybeAndV);
                        non_term.push(NonTerm::Expression);
                    },
                    // boolean conjunctions and disjunctions
                    Tk::BoolAnd => {
                        non_term.push(NonTerm::AndB);
                        non_term.push(NonTerm::Expression);
                        non_term.push(NonTerm::WExpression);
                    },
                    Tk::BoolOr => {
                        non_term.push(NonTerm::OrB);
                        non_term.push(NonTerm::Expression);
                        non_term.push(NonTerm::WExpression);
                    },
                    // CHECKMULTISIG based multisig
                    Tk::CheckMultiSig, Tk::Num(n) => {
                        threshold::validate_k_n::<MAX_PUBKEYS_PER_MULTISIG>(1, n as usize).map_err(Error::Threshold)?;

                        let mut keys = Vec::with_capacity(n as usize);
                        for _ in 0..n {
                            match_token!(
                                tokens,
                                Tk::Bytes33(pk) => keys.push(<Ctx::Key>::from_slice(&pk)
                                    .map_err(|e| Error::PubKeyCtxError(e, Ctx::name_str()))?),
                                Tk::Bytes65(pk) => keys.push(<Ctx::Key>::from_slice(&pk)
                                    .map_err(|e| Error::PubKeyCtxError(e, Ctx::name_str()))?),
                            );
                        }
                        let k = match_token!(
                            tokens,
                            Tk::Num(k) => k,
                        );
                        keys.reverse();
                        let thresh = Threshold::new(k as usize, keys).map_err(Error::Threshold)?;
                        term.push(Miniscript::multi(thresh));
                    },
                    // MultiA
                    Tk::NumEqual, Tk::Num(k) => {
                        threshold::validate_k_n::<MAX_PUBKEYS_IN_CHECKSIGADD>(k as usize, k as usize).map_err(Error::Threshold)?;

                        let mut keys = Vec::with_capacity(k as usize); // at least k capacity
                        while tokens.peek() == Some(&Tk::CheckSigAdd) {
                            match_token!(
                                tokens,
                                Tk::CheckSigAdd, Tk::Bytes32(pk) => keys.push(<Ctx::Key>::from_slice(&pk)
                                    .map_err(|e| Error::PubKeyCtxError(e, Ctx::name_str()))?),
                            );
                        }
                        // Last key must be with a CheckSig
                        match_token!(
                            tokens,
                            Tk::CheckSig, Tk::Bytes32(pk) => keys.push(<Ctx::Key>::from_slice(&pk)
                                .map_err(|e| Error::PubKeyCtxError(e, Ctx::name_str()))?),
                        );
                        keys.reverse();
                        let thresh = Threshold::new(k as usize, keys).map_err(Error::Threshold)?;
                        term.push(Miniscript::multi_a(thresh));
                    },
                );
            }
            Some(NonTerm::MaybeAndV) => {
                // Handle `and_v` prefixing
                if is_and_v(tokens) {
                    non_term.push(NonTerm::AndV);
                    non_term.push(NonTerm::Expression);
                }
            }
            Some(NonTerm::Swap) => {
                // Handle `SWAP` prefixing
                match_token!(
                    tokens,
                    Tk::Swap => {},
                );
                term.reduce1(params, Terminal::Swap)?;
                // Swap must be always be terminating a NonTerm as it cannot be in and_v
            }
            Some(NonTerm::Alt) => {
                match_token!(
                    tokens,
                    Tk::ToAltStack => {},
                );
                term.reduce1(params, Terminal::Alt)?;
            }
            Some(NonTerm::Check) => term.reduce1(params, Terminal::Check)?,
            Some(NonTerm::DupIf) => term.reduce1(params, Terminal::DupIf)?,
            Some(NonTerm::Verify) => term.reduce1(params, Terminal::Verify)?,
            Some(NonTerm::NonZero) => term.reduce1(params, Terminal::NonZero)?,
            Some(NonTerm::ZeroNotEqual) => term.reduce1(params, Terminal::ZeroNotEqual)?,
            Some(NonTerm::AndV) => {
                if is_and_v(tokens) {
                    non_term.push(NonTerm::AndV);
                    non_term.push(NonTerm::MaybeAndV);
                } else {
                    term.reduce2(params, Terminal::AndV)?
                }
            }
            Some(NonTerm::AndB) => term.reduce2(params, Terminal::AndB)?,
            Some(NonTerm::OrB) => term.reduce2(params, Terminal::OrB)?,
            Some(NonTerm::OrC) => term.reduce2(params, Terminal::OrC)?,
            Some(NonTerm::OrD) => term.reduce2(params, Terminal::OrD)?,
            Some(NonTerm::Tern) => {
                let a = term.pop().unwrap();
                let b = term.pop().unwrap();
                let c = term.pop().unwrap();
                let wrapped_ms = Terminal::AndOr(Arc::new(a), Arc::new(c), Arc::new(b));

                term.0
                    .push(Miniscript::from_ast(wrapped_ms, params).map_err(Error::Construct)?);
            }
            Some(NonTerm::ThreshW { n, k }) => {
                match_token!(
                    tokens,
                    Tk::Add => {
                        non_term.push(NonTerm::ThreshW { n: n + 1, k });
                        non_term.push(NonTerm::WExpression);
                    },
                    x => {
                        tokens.un_next(x);
                        non_term.push(NonTerm::ThreshE { n: n + 1, k });
                        non_term.push(NonTerm::Expression);
                    },
                );
            }
            Some(NonTerm::ThreshE { n, k }) => {
                let mut subs = Vec::with_capacity(n);
                for _ in 0..n {
                    subs.push(Arc::new(term.pop().unwrap()));
                }
                term.reduce0(
                    Terminal::Thresh(Threshold::new(k, subs).map_err(Error::Threshold)?),
                    params,
                )?;
            }
            Some(NonTerm::EndIf) => {
                match_token!(
                    tokens,
                    Tk::Else => {
                        non_term.push(NonTerm::EndIfElse);
                        non_term.push(NonTerm::MaybeAndV);
                        non_term.push(NonTerm::Expression);
                    },
                    Tk::If => match_token!(
                        tokens,
                        Tk::Dup => non_term.push(NonTerm::DupIf),
                        Tk::ZeroNotEqual, Tk::Size
                            => non_term.push(NonTerm::NonZero),
                    ),
                    Tk::NotIf => {
                        non_term.push(NonTerm::EndIfNotIf);
                    },
                );
            }
            Some(NonTerm::EndIfNotIf) => {
                match_token!(
                    tokens,
                    Tk::IfDup => non_term.push(NonTerm::OrD),
                    x => {
                        tokens.un_next(x);
                        non_term.push(NonTerm::OrC);
                    },
                );
                non_term.push(NonTerm::Expression);
            }
            Some(NonTerm::EndIfElse) => {
                match_token!(
                    tokens,
                    Tk::If => {
                        term.reduce2(params, Terminal::OrI)?;
                    },
                    Tk::NotIf => {
                        non_term.push(NonTerm::Tern);
                        non_term.push(NonTerm::Expression);
                    },
                );
            }
            Some(NonTerm::WExpression) => {
                // W expression must be either from swap or Fromaltstack
                match_token!(tokens,
                    Tk::FromAltStack => { non_term.push(NonTerm::Alt);},
                    tok => { tokens.un_next(tok); non_term.push(NonTerm::Swap);},);
                non_term.push(NonTerm::MaybeAndV);
                non_term.push(NonTerm::Expression);
            }
            None => {
                // Done :)
                break;
            }
        }
    }

    assert_eq!(non_term.len(), 0);
    assert_eq!(term.0.len(), 1);
    Ok(term.pop().unwrap())
}

fn is_and_v(tokens: &mut TokenIter) -> bool {
    !matches!(
        tokens.peek(),
        None | Some(&Tk::If)
            | Some(&Tk::NotIf)
            | Some(&Tk::Else)
            | Some(&Tk::ToAltStack)
            | Some(&Tk::Swap)
    )
}

/// Decoding error while parsing keys
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KeyError {
    /// Bitcoin PublicKey parse error
    Full(bitcoin::key::FromSliceError),
    /// Xonly key parse Error
    XOnly(bitcoin::secp256k1::Error),
}

impl fmt::Display for KeyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Full(e) => e.fmt(f),
            Self::XOnly(e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for KeyError {
    fn cause(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::Full(e) => Some(e),
            Self::XOnly(e) => Some(e),
        }
    }
}

/// Decoding error.
#[derive(Debug)]
pub enum Error {
    /// Error constructing a Miniscript.
    Construct(crate::WithSpan<super::ConstructError>),
    /// Error lexing a Script into Miniscript tokens.
    Lex(super::lex::Error),
    /// PubKey invalid under current context
    PubKeyCtxError(KeyError, &'static str),
    /// Invalid absolute locktime
    AbsoluteLockTime(crate::AbsLockTimeError),
    /// Invalid absolute locktime
    RelativeLockTime(crate::RelLockTimeError),
    /// Invalid threshold.
    Threshold(crate::ThresholdError),
    /// Parsed a miniscript but there were more script opcodes after it.
    Trailing(Tk),
    /// Got token that we did not expect.
    Unexpected(Tk),
    /// While parsing backward, hit beginning of script
    UnexpectedStart,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::Construct(ref e) => e.fmt(f),
            Self::Lex(ref e) => e.fmt(f),
            Self::PubKeyCtxError(ref pk, ref ctx) => {
                write!(f, "failed to parse {} key: {}", ctx, pk)
            }
            Self::AbsoluteLockTime(ref e) => e.fmt(f),
            Self::RelativeLockTime(ref e) => e.fmt(f),
            Self::Threshold(ref e) => e.fmt(f),
            Self::Trailing(ref tk) => {
                write!(f, "unexpected extra token {} after decoding script end-to-front", tk)
            }
            Self::Unexpected(ref tk) => {
                write!(f, "unexpected token {} when decoding script end-to-front", tk)
            }
            Self::UnexpectedStart => {
                f.write_str("unexpected start-of-script when decoding back-to-front")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn cause(&self) -> Option<&dyn std::error::Error> {
        match *self {
            Self::Construct(ref e) => Some(e),
            Self::Lex(ref e) => Some(e),
            Self::PubKeyCtxError(ref e, _) => Some(e),
            Self::AbsoluteLockTime(ref e) => Some(e),
            Self::RelativeLockTime(ref e) => Some(e),
            Self::Threshold(ref e) => Some(e),
            Self::Trailing(..) => None,
            Self::Unexpected(..) => None,
            Self::UnexpectedStart => None,
        }
    }
}
