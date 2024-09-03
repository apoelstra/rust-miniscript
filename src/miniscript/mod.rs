// SPDX-License-Identifier: CC0-1.0

//! Abstract Syntax Tree
//!
//! Defines a variety of data structures for describing Miniscript, a subset of
//! Bitcoin Script which can be efficiently parsed and serialized from Script,
//! and from which it is easy to extract data needed to construct witnesses.
//!
//! Users of the library in general will only need to use the structures exposed
//! from the top level of this module; however for people wanting to do advanced
//! things, the submodules are public as well which provide visibility into the
//! components of the AST.
//!

use core::{hash, str};

use bitcoin::hashes::hash160;
use bitcoin::script;
use bitcoin::taproot::{LeafVersion, TapLeafHash};

use self::analyzable::ExtParams;
pub use self::context::{BareCtx, Legacy, Segwitv0, Tap};
use crate::iter::TreeLike;
use crate::prelude::*;
use crate::{script_num_size, TranslateErr};

pub mod analyzable;
pub mod astelem;
pub(crate) mod context;
pub mod decode;
mod display;
pub mod iter;
pub mod lex;
pub mod limits;
pub mod satisfy;
pub mod types;

use core::cmp;

use sync::Arc;

use self::lex::{lex, TokenIter};
pub use crate::miniscript::context::ScriptContext;
use crate::miniscript::decode::Terminal;
use crate::{
    expression, plan, Error, ForEachKey, FromStrKey, MiniscriptKey, ToPublicKey, Translator,
};
#[cfg(test)]
mod ms_tests;

mod private {
    use core::marker::PhantomData;

    use super::types::{ExtData, Type};
    use crate::iter::TreeLike as _;
    pub use crate::miniscript::context::ScriptContext;
    use crate::miniscript::types;
    use crate::prelude::sync::Arc;
    use crate::{Error, MiniscriptKey, Terminal, MAX_RECURSION_DEPTH};

    /// The top-level miniscript abstract syntax tree (AST).
    pub struct Miniscript<Pk: MiniscriptKey, Ctx: ScriptContext> {
        /// A node in the AST.
        pub node: Terminal<Pk, Ctx>,
        /// The correctness and malleability type information for the AST node.
        pub ty: types::Type,
        /// Additional information helpful for extra analysis.
        pub ext: types::extra_props::ExtData,
        /// Context PhantomData. Only accessible inside this crate
        phantom: PhantomData<Ctx>,
    }

    impl<Pk: MiniscriptKey, Ctx: ScriptContext> Clone for Miniscript<Pk, Ctx> {
        /// We implement clone as a "deep clone" which reconstructs the entire tree.
        ///
        /// If users just want to clone Arcs they can use Arc::clone themselves.
        /// Note that if a Miniscript was constructed using shared Arcs, the result
        /// of calling `clone` will no longer have shared Arcs. So there is no
        /// pleasing everyone. But for the two common cases:
        ///
        /// * Users don't care about sharing at all, and they can call `Arc::clone`
        ///   on an `Arc<Miniscript>`.
        /// * Users want a deep copy which does not share any nodes with the original
        ///   (for example, because they have keys that have interior mutability),
        ///   and they can call `Miniscript::clone`.
        fn clone(&self) -> Self {
            let mut stack = vec![];
            for item in self.rtl_post_order_iter() {
                let new_term = match item.node.node {
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
                    Terminal::Alt(..) => Terminal::Alt(stack.pop().unwrap()),
                    Terminal::Swap(..) => Terminal::Swap(stack.pop().unwrap()),
                    Terminal::Check(..) => Terminal::Check(stack.pop().unwrap()),
                    Terminal::DupIf(..) => Terminal::DupIf(stack.pop().unwrap()),
                    Terminal::Verify(..) => Terminal::Verify(stack.pop().unwrap()),
                    Terminal::NonZero(..) => Terminal::NonZero(stack.pop().unwrap()),
                    Terminal::ZeroNotEqual(..) => Terminal::ZeroNotEqual(stack.pop().unwrap()),
                    Terminal::AndV(..) => {
                        Terminal::AndV(stack.pop().unwrap(), stack.pop().unwrap())
                    }
                    Terminal::AndB(..) => {
                        Terminal::AndB(stack.pop().unwrap(), stack.pop().unwrap())
                    }
                    Terminal::AndOr(..) => Terminal::AndOr(
                        stack.pop().unwrap(),
                        stack.pop().unwrap(),
                        stack.pop().unwrap(),
                    ),
                    Terminal::OrB(..) => Terminal::OrB(stack.pop().unwrap(), stack.pop().unwrap()),
                    Terminal::OrD(..) => Terminal::OrD(stack.pop().unwrap(), stack.pop().unwrap()),
                    Terminal::OrC(..) => Terminal::OrC(stack.pop().unwrap(), stack.pop().unwrap()),
                    Terminal::OrI(..) => Terminal::OrI(stack.pop().unwrap(), stack.pop().unwrap()),
                    Terminal::Thresh(ref thresh) => {
                        Terminal::Thresh(thresh.map_ref(|_| stack.pop().unwrap()))
                    }
                    Terminal::Multi(ref thresh) => Terminal::Multi(thresh.clone()),
                    Terminal::MultiA(ref thresh) => Terminal::MultiA(thresh.clone()),
                };

                stack.push(Arc::new(Miniscript {
                    node: new_term,
                    ty: item.node.ty,
                    ext: item.node.ext,
                    phantom: PhantomData,
                }));
            }

            assert_eq!(stack.len(), 1);
            Arc::try_unwrap(stack.pop().unwrap()).unwrap()
        }
    }

    impl<Pk: MiniscriptKey, Ctx: ScriptContext> Miniscript<Pk, Ctx> {
        /// The `1` combinator.
        pub const TRUE: Self = Miniscript {
            node: Terminal::True,
            ty: types::Type::TRUE,
            ext: types::extra_props::ExtData::TRUE,
            phantom: PhantomData,
        };

        /// The `0` combinator.
        pub const FALSE: Self = Miniscript {
            node: Terminal::False,
            ty: types::Type::FALSE,
            ext: types::extra_props::ExtData::FALSE,
            phantom: PhantomData,
        };

        /// Add type information(Type and Extdata) to Miniscript based on
        /// `AstElem` fragment. Dependent on display and clone because of Error
        /// Display code of type_check.
        pub fn from_ast(t: Terminal<Pk, Ctx>) -> Result<Miniscript<Pk, Ctx>, Error> {
            let res = Miniscript {
                ty: Type::type_check(&t)?,
                ext: ExtData::type_check(&t),
                node: t,
                phantom: PhantomData,
            };
            // TODO: This recursion depth is based on segwitv0.
            // We can relax this in tapscript, but this should be good for almost
            // all practical cases and we can revisit this if needed.
            // casting to u32 is safe because tree_height will never go more than u32::MAX
            if (res.ext.tree_height as u32) > MAX_RECURSION_DEPTH {
                return Err(Error::MaxRecursiveDepthExceeded);
            }
            Ctx::check_global_validity(&res)?;
            Ok(res)
        }

        /// Create a new `Miniscript` from a `Terminal` node and a `Type` annotation
        /// This does not check the typing rules. The user is responsible for ensuring
        /// that the type provided is correct.
        ///
        /// You should almost always use `Miniscript::from_ast` instead of this function.
        pub fn from_components_unchecked(
            node: Terminal<Pk, Ctx>,
            ty: types::Type,
            ext: types::extra_props::ExtData,
        ) -> Miniscript<Pk, Ctx> {
            Miniscript { node, ty, ext, phantom: PhantomData }
        }
    }
}

pub use private::Miniscript;

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Miniscript<Pk, Ctx> {
    /// Extracts the `AstElem` representing the root of the miniscript
    pub fn into_inner(self) -> Terminal<Pk, Ctx> { self.node }

    /// Get a reference to the inner `AstElem` representing the root of miniscript
    pub fn as_inner(&self) -> &Terminal<Pk, Ctx> { &self.node }

    /// Encode as a Bitcoin script
    pub fn encode(&self) -> script::ScriptBuf
    where
        Pk: ToPublicKey,
    {
        self.node.encode(script::Builder::new()).into_script()
    }

    /// Size, in bytes of the script-pubkey. If this Miniscript is used outside
    /// of segwit (e.g. in a bare or P2SH descriptor), this quantity should be
    /// multiplied by 4 to compute the weight.
    ///
    /// In general, it is not recommended to use this function directly, but
    /// to instead call the corresponding function on a `Descriptor`, which
    /// will handle the segwit/non-segwit technicalities for you.
    pub fn script_size(&self) -> usize {
        use Terminal::*;

        let mut len = 0;
        for ms in self.pre_order_iter() {
            len += match ms.node {
                AndV(..) => 0,
                True | False | Swap(..) | Check(..) | ZeroNotEqual(..) | AndB(..) | OrB(..) => 1,
                Alt(..) | OrC(..) => 2,
                DupIf(..) | AndOr(..) | OrD(..) | OrI(..) => 3,
                NonZero(..) => 4,
                PkH(..) | RawPkH(..) => 24,
                Ripemd160(..) | Hash160(..) => 21 + 6,
                Sha256(..) | Hash256(..) => 33 + 6,

                Terminal::PkK(ref pk) => Ctx::pk_len(pk),
                Terminal::After(n) => script_num_size(n.to_consensus_u32() as usize) + 1,
                Terminal::Older(n) => script_num_size(n.to_consensus_u32() as usize) + 1,
                Terminal::Verify(ref sub) => usize::from(!sub.ext.has_free_verify),
                Terminal::Thresh(ref thresh) => {
                    script_num_size(thresh.k()) // k
                        + 1 // EQUAL
                        + thresh.n() // ADD
                        - 1 // no ADD on first element
                }
                Terminal::Multi(ref thresh) => {
                    script_num_size(thresh.k())
                        + 1
                        + script_num_size(thresh.n())
                        + thresh.iter().map(|pk| Ctx::pk_len(pk)).sum::<usize>()
                }
                Terminal::MultiA(ref thresh) => {
                    script_num_size(thresh.k())
                        + 1 // NUMEQUAL
                        + thresh.iter().map(|pk| Ctx::pk_len(pk)).sum::<usize>() // n keys
                        + thresh.n() // n times CHECKSIGADD
                }
            }
        }
        len
    }

    /// Maximum number of witness elements used to satisfy the Miniscript
    /// fragment, including the witness script itself. Used to estimate
    /// the weight of the `VarInt` that specifies this number in a serialized
    /// transaction.
    ///
    /// This function may returns Error when the Miniscript is
    /// impossible to satisfy
    pub fn max_satisfaction_witness_elements(&self) -> Result<usize, Error> {
        self.ext
            .stack_elem_count_sat
            .map(|x| x + 1)
            .ok_or(Error::ImpossibleSatisfaction)
    }

    /// Maximum size, in bytes, of a satisfying witness. For Segwit outputs
    /// `one_cost` should be set to 2, since the number `1` requires two
    /// bytes to encode. For non-segwit outputs `one_cost` should be set to
    /// 1, since `OP_1` is available in scriptSigs.
    ///
    /// In general, it is not recommended to use this function directly, but
    /// to instead call the corresponding function on a `Descriptor`, which
    /// will handle the segwit/non-segwit technicalities for you.
    ///
    /// All signatures are assumed to be 73 bytes in size, including the
    /// length prefix (segwit) or push opcode (pre-segwit) and sighash
    /// postfix.
    pub fn max_satisfaction_size(&self) -> Result<usize, Error> {
        Ctx::max_satisfaction_size(self).ok_or(Error::ImpossibleSatisfaction)
    }

    /// Helper function to produce Taproot leaf hashes
    fn leaf_hash_internal(&self) -> TapLeafHash
    where
        Pk: ToPublicKey,
    {
        TapLeafHash::from_script(&self.encode(), LeafVersion::TapScript)
    }

    /// Attempt to produce non-malleable satisfying witness for the
    /// witness script represented by the parse tree
    pub fn satisfy<S: satisfy::Satisfier<Pk>>(&self, satisfier: S) -> Result<Vec<Vec<u8>>, Error>
    where
        Pk: ToPublicKey,
    {
        // Only satisfactions for default versions (0xc0) are allowed.
        let satisfaction = satisfy::Satisfaction::satisfy(
            &self.node,
            &satisfier,
            self.ty.mall.safe,
            &self.leaf_hash_internal(),
        );
        self._satisfy(satisfaction)
    }

    /// Attempt to produce a malleable satisfying witness for the
    /// witness script represented by the parse tree
    pub fn satisfy_malleable<S: satisfy::Satisfier<Pk>>(
        &self,
        satisfier: S,
    ) -> Result<Vec<Vec<u8>>, Error>
    where
        Pk: ToPublicKey,
    {
        let satisfaction = satisfy::Satisfaction::satisfy_mall(
            &self.node,
            &satisfier,
            self.ty.mall.safe,
            &self.leaf_hash_internal(),
        );
        self._satisfy(satisfaction)
    }

    fn _satisfy(&self, satisfaction: satisfy::Satisfaction<Vec<u8>>) -> Result<Vec<Vec<u8>>, Error>
    where
        Pk: ToPublicKey,
    {
        match satisfaction.stack {
            satisfy::Witness::Stack(stack) => {
                Ctx::check_witness(&stack)?;
                Ok(stack)
            }
            satisfy::Witness::Unavailable | satisfy::Witness::Impossible => {
                Err(Error::CouldNotSatisfy)
            }
        }
    }

    /// Attempt to produce a non-malleable witness template given the assets available
    pub fn build_template<P: plan::AssetProvider<Pk>>(
        &self,
        provider: &P,
    ) -> satisfy::Satisfaction<satisfy::Placeholder<Pk>>
    where
        Pk: ToPublicKey,
    {
        satisfy::Satisfaction::build_template(
            &self.node,
            provider,
            self.ty.mall.safe,
            &self.leaf_hash_internal(),
        )
    }

    /// Attempt to produce a malleable witness template given the assets available
    pub fn build_template_mall<P: plan::AssetProvider<Pk>>(
        &self,
        provider: &P,
    ) -> satisfy::Satisfaction<satisfy::Placeholder<Pk>>
    where
        Pk: ToPublicKey,
    {
        satisfy::Satisfaction::build_template_mall(
            &self.node,
            provider,
            self.ty.mall.safe,
            &self.leaf_hash_internal(),
        )
    }
}

impl Miniscript<<Tap as ScriptContext>::Key, Tap> {
    /// Returns the leaf hash used within a Taproot signature for this script.
    ///
    /// Note that this method is only implemented for Taproot Miniscripts.
    pub fn leaf_hash(&self) -> TapLeafHash { self.leaf_hash_internal() }
}

impl<Ctx: ScriptContext> Miniscript<Ctx::Key, Ctx> {
    /// Attempt to parse an insane(scripts don't clear sanity checks)
    /// script into a Miniscript representation.
    /// Use this to parse scripts with repeated pubkeys, timelock mixing, malleable
    /// scripts without sig or scripts that can exceed resource limits.
    /// Some of the analysis guarantees of miniscript are lost when dealing with
    /// insane scripts. In general, in a multi-party setting users should only
    /// accept sane scripts.
    pub fn parse_insane(script: &script::Script) -> Result<Miniscript<Ctx::Key, Ctx>, Error> {
        Miniscript::parse_with_ext(script, &ExtParams::insane())
    }

    /// Attempt to parse an miniscript with extra features that not yet specified in the spec.
    /// Users should not use this function unless they scripts can/will change in the future.
    /// Currently, this function supports the following features:
    ///     - Parsing all insane scripts
    ///     - Parsing miniscripts with raw pubkey hashes
    ///
    /// Allowed extra features can be specified by the ext [`ExtParams`] argument.
    pub fn parse_with_ext(
        script: &script::Script,
        ext: &ExtParams,
    ) -> Result<Miniscript<Ctx::Key, Ctx>, Error> {
        let tokens = lex(script)?;
        let mut iter = TokenIter::new(tokens);

        let top = decode::parse(&mut iter)?;
        Ctx::check_global_validity(&top)?;
        let type_check = types::Type::type_check(&top.node)?;
        if type_check.corr.base != types::Base::B {
            return Err(Error::NonTopLevel(format!("{:?}", top)));
        };
        if let Some(leading) = iter.next() {
            Err(Error::Trailing(leading.to_string()))
        } else {
            top.ext_check(ext)?;
            Ok(top)
        }
    }

    /// Attempt to parse a Script into Miniscript representation.
    ///
    /// This function will fail parsing for scripts that do not clear the
    /// [`Miniscript::sanity_check`] checks. Use [`Miniscript::parse_insane`] to
    /// parse such scripts.
    ///
    /// ## Decode/Parse a miniscript from script hex
    ///
    /// ```rust
    /// use miniscript::{Miniscript, Segwitv0, Tap};
    /// use miniscript::bitcoin::secp256k1::XOnlyPublicKey;
    /// use miniscript::bitcoin::hashes::hex::FromHex;
    ///
    /// type Segwitv0Script = Miniscript<bitcoin::PublicKey, Segwitv0>;
    /// type TapScript = Miniscript<XOnlyPublicKey, Tap>;
    ///
    /// // parse x-only miniscript in Taproot context
    /// let tapscript_ms = TapScript::parse(&bitcoin::ScriptBuf::from_hex(
    ///     "202788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99ac",
    /// ).expect("Even length hex"))
    ///     .expect("Xonly keys are valid only in taproot context");
    /// // tapscript fails decoding when we use them with compressed keys
    /// let err = TapScript::parse(&bitcoin::ScriptBuf::from_hex(
    ///     "21022788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99ac",
    /// ).expect("Even length hex"))
    ///     .expect_err("Compressed keys cannot be used in Taproot context");
    /// // Segwitv0 succeeds decoding with full keys.
    /// Segwitv0Script::parse(&bitcoin::ScriptBuf::from_hex(
    ///     "21022788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99ac",
    /// ).expect("Even length hex"))
    ///     .expect("Compressed keys are allowed in Segwit context");
    ///
    /// ```
    pub fn parse(script: &script::Script) -> Result<Miniscript<Ctx::Key, Ctx>, Error> {
        let ms = Self::parse_with_ext(script, &ExtParams::sane())?;
        Ok(ms)
    }
}

/// `PartialOrd` of `Miniscript` must depend only on node and not the type information.
///
/// The type information and extra properties are implied by the AST.
impl<Pk: MiniscriptKey, Ctx: ScriptContext> PartialOrd for Miniscript<Pk, Ctx> {
    fn partial_cmp(&self, other: &Miniscript<Pk, Ctx>) -> Option<cmp::Ordering> {
        Some(self.node.cmp(&other.node))
    }
}

/// `Ord` of `Miniscript` must depend only on node and not the type information.
///
/// The type information and extra properties are implied by the AST.
impl<Pk: MiniscriptKey, Ctx: ScriptContext> Ord for Miniscript<Pk, Ctx> {
    fn cmp(&self, other: &Miniscript<Pk, Ctx>) -> cmp::Ordering { self.node.cmp(&other.node) }
}

/// `PartialEq` of `Miniscript` must depend only on node and not the type information.
///
/// The type information and extra properties are implied by the AST.
impl<Pk: MiniscriptKey, Ctx: ScriptContext> PartialEq for Miniscript<Pk, Ctx> {
    fn eq(&self, other: &Miniscript<Pk, Ctx>) -> bool { self.node.eq(&other.node) }
}

/// `Eq` of `Miniscript` must depend only on node and not the type information.
///
/// The type information and extra properties are implied by the AST.
impl<Pk: MiniscriptKey, Ctx: ScriptContext> Eq for Miniscript<Pk, Ctx> {}

/// `Hash` of `Miniscript` must depend only on node and not the type information.
///
/// The type information and extra properties are implied by the AST.
impl<Pk: MiniscriptKey, Ctx: ScriptContext> hash::Hash for Miniscript<Pk, Ctx> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) { self.node.hash(state); }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> ForEachKey<Pk> for Miniscript<Pk, Ctx> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, mut pred: F) -> bool {
        for ms in self.pre_order_iter() {
            match ms.node {
                Terminal::PkK(ref p) => {
                    if !pred(p) {
                        return false;
                    }
                }
                Terminal::PkH(ref p) => {
                    if !pred(p) {
                        return false;
                    }
                }
                // These branches cannot be combined since technically the two `thresh`es
                // have different types (have different maximum values).
                Terminal::Multi(ref thresh) => {
                    if !thresh.iter().all(&mut pred) {
                        return false;
                    }
                }
                Terminal::MultiA(ref thresh) => {
                    if !thresh.iter().all(&mut pred) {
                        return false;
                    }
                }
                _ => {}
            }
        }
        true
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Miniscript<Pk, Ctx> {
    /// Translates a struct from one generic to another where the translation
    /// for Pk is provided by [`Translator`]
    pub fn translate_pk<T>(
        &self,
        t: &mut T,
    ) -> Result<Miniscript<T::TargetPk, Ctx>, TranslateErr<T::Error>>
    where
        T: Translator<Pk>,
    {
        self.translate_pk_ctx(t)
    }

    pub(super) fn translate_pk_ctx<CtxQ, T>(
        &self,
        t: &mut T,
    ) -> Result<Miniscript<T::TargetPk, CtxQ>, TranslateErr<T::Error>>
    where
        CtxQ: ScriptContext,
        T: Translator<Pk>,
    {
        let mut translated = vec![];
        for data in self.rtl_post_order_iter() {
            let new_term = match data.node.node {
                Terminal::PkK(ref p) => Terminal::PkK(t.pk(p)?),
                Terminal::PkH(ref p) => Terminal::PkH(t.pk(p)?),
                Terminal::RawPkH(ref p) => Terminal::RawPkH(*p),
                Terminal::After(n) => Terminal::After(n),
                Terminal::Older(n) => Terminal::Older(n),
                Terminal::Sha256(ref x) => Terminal::Sha256(t.sha256(x)?),
                Terminal::Hash256(ref x) => Terminal::Hash256(t.hash256(x)?),
                Terminal::Ripemd160(ref x) => Terminal::Ripemd160(t.ripemd160(x)?),
                Terminal::Hash160(ref x) => Terminal::Hash160(t.hash160(x)?),
                Terminal::True => Terminal::True,
                Terminal::False => Terminal::False,
                Terminal::Alt(..) => Terminal::Alt(translated.pop().unwrap()),
                Terminal::Swap(..) => Terminal::Swap(translated.pop().unwrap()),
                Terminal::Check(..) => Terminal::Check(translated.pop().unwrap()),
                Terminal::DupIf(..) => Terminal::DupIf(translated.pop().unwrap()),
                Terminal::Verify(..) => Terminal::Verify(translated.pop().unwrap()),
                Terminal::NonZero(..) => Terminal::NonZero(translated.pop().unwrap()),
                Terminal::ZeroNotEqual(..) => Terminal::ZeroNotEqual(translated.pop().unwrap()),
                Terminal::AndV(..) => {
                    Terminal::AndV(translated.pop().unwrap(), translated.pop().unwrap())
                }
                Terminal::AndB(..) => {
                    Terminal::AndB(translated.pop().unwrap(), translated.pop().unwrap())
                }
                Terminal::AndOr(..) => Terminal::AndOr(
                    translated.pop().unwrap(),
                    translated.pop().unwrap(),
                    translated.pop().unwrap(),
                ),
                Terminal::OrB(..) => {
                    Terminal::OrB(translated.pop().unwrap(), translated.pop().unwrap())
                }
                Terminal::OrD(..) => {
                    Terminal::OrD(translated.pop().unwrap(), translated.pop().unwrap())
                }
                Terminal::OrC(..) => {
                    Terminal::OrC(translated.pop().unwrap(), translated.pop().unwrap())
                }
                Terminal::OrI(..) => {
                    Terminal::OrI(translated.pop().unwrap(), translated.pop().unwrap())
                }
                Terminal::Thresh(ref thresh) => {
                    Terminal::Thresh(thresh.map_ref(|_| translated.pop().unwrap()))
                }
                Terminal::Multi(ref thresh) => Terminal::Multi(thresh.translate_ref(|k| t.pk(k))?),
                Terminal::MultiA(ref thresh) => {
                    Terminal::MultiA(thresh.translate_ref(|k| t.pk(k))?)
                }
            };
            let new_ms = Miniscript::from_ast(new_term).map_err(TranslateErr::OuterError)?;
            translated.push(Arc::new(new_ms));
        }

        Ok(Arc::try_unwrap(translated.pop().unwrap()).unwrap())
    }

    /// Substitutes raw public keys hashes with the public keys as provided by map.
    pub fn substitute_raw_pkh(&self, pk_map: &BTreeMap<hash160::Hash, Pk>) -> Miniscript<Pk, Ctx> {
        let mut stack = vec![];
        for item in self.rtl_post_order_iter() {
            let new_term = match item.node.node {
                Terminal::PkK(ref p) => Terminal::PkK(p.clone()),
                Terminal::PkH(ref p) => Terminal::PkH(p.clone()),
                // This algorithm is identical to Clone::clone except for this line.
                Terminal::RawPkH(ref hash) => match pk_map.get(hash) {
                    Some(p) => Terminal::PkH(p.clone()),
                    None => Terminal::RawPkH(*hash),
                },
                Terminal::After(ref n) => Terminal::After(*n),
                Terminal::Older(ref n) => Terminal::Older(*n),
                Terminal::Sha256(ref x) => Terminal::Sha256(x.clone()),
                Terminal::Hash256(ref x) => Terminal::Hash256(x.clone()),
                Terminal::Ripemd160(ref x) => Terminal::Ripemd160(x.clone()),
                Terminal::Hash160(ref x) => Terminal::Hash160(x.clone()),
                Terminal::True => Terminal::True,
                Terminal::False => Terminal::False,
                Terminal::Alt(..) => Terminal::Alt(stack.pop().unwrap()),
                Terminal::Swap(..) => Terminal::Swap(stack.pop().unwrap()),
                Terminal::Check(..) => Terminal::Check(stack.pop().unwrap()),
                Terminal::DupIf(..) => Terminal::DupIf(stack.pop().unwrap()),
                Terminal::Verify(..) => Terminal::Verify(stack.pop().unwrap()),
                Terminal::NonZero(..) => Terminal::NonZero(stack.pop().unwrap()),
                Terminal::ZeroNotEqual(..) => Terminal::ZeroNotEqual(stack.pop().unwrap()),
                Terminal::AndV(..) => Terminal::AndV(stack.pop().unwrap(), stack.pop().unwrap()),
                Terminal::AndB(..) => Terminal::AndB(stack.pop().unwrap(), stack.pop().unwrap()),
                Terminal::AndOr(..) => Terminal::AndOr(
                    stack.pop().unwrap(),
                    stack.pop().unwrap(),
                    stack.pop().unwrap(),
                ),
                Terminal::OrB(..) => Terminal::OrB(stack.pop().unwrap(), stack.pop().unwrap()),
                Terminal::OrD(..) => Terminal::OrD(stack.pop().unwrap(), stack.pop().unwrap()),
                Terminal::OrC(..) => Terminal::OrC(stack.pop().unwrap(), stack.pop().unwrap()),
                Terminal::OrI(..) => Terminal::OrI(stack.pop().unwrap(), stack.pop().unwrap()),
                Terminal::Thresh(ref thresh) => {
                    Terminal::Thresh(thresh.map_ref(|_| stack.pop().unwrap()))
                }
                Terminal::Multi(ref thresh) => Terminal::Multi(thresh.clone()),
                Terminal::MultiA(ref thresh) => Terminal::MultiA(thresh.clone()),
            };

            stack.push(Arc::new(Miniscript::from_components_unchecked(
                new_term,
                item.node.ty,
                item.node.ext,
            )));
        }

        assert_eq!(stack.len(), 1);
        Arc::try_unwrap(stack.pop().unwrap()).unwrap()
    }
}

/// Utility function used when parsing a script from an expression tree.
///
/// Once a Miniscript fragment has been parsed into a terminal, apply any
/// wrappers that were included in its name.
fn wrap_into_miniscript<Pk, Ctx>(
    term: Terminal<Pk, Ctx>,
    frag_wrap: &str,
) -> Result<Miniscript<Pk, Ctx>, Error>
where
    Pk: MiniscriptKey,
    Ctx: ScriptContext,
{
    let mut unwrapped = term;
    for ch in frag_wrap.chars().rev() {
        // Check whether the wrapper is valid under the current context
        let ms = Miniscript::from_ast(unwrapped)?;
        match ch {
            'a' => unwrapped = Terminal::Alt(Arc::new(ms)),
            's' => unwrapped = Terminal::Swap(Arc::new(ms)),
            'c' => unwrapped = Terminal::Check(Arc::new(ms)),
            'd' => unwrapped = Terminal::DupIf(Arc::new(ms)),
            'v' => unwrapped = Terminal::Verify(Arc::new(ms)),
            'j' => unwrapped = Terminal::NonZero(Arc::new(ms)),
            'n' => unwrapped = Terminal::ZeroNotEqual(Arc::new(ms)),
            't' => unwrapped = Terminal::AndV(Arc::new(ms), Arc::new(Miniscript::TRUE)),
            'u' => unwrapped = Terminal::OrI(Arc::new(ms), Arc::new(Miniscript::FALSE)),
            'l' => unwrapped = Terminal::OrI(Arc::new(Miniscript::FALSE), Arc::new(ms)),
            x => return Err(Error::UnknownWrapper(x)),
        }
    }
    // Check whether the unwrapped miniscript is valid under the current context
    let ms = Miniscript::from_ast(unwrapped)?;
    Ok(ms)
}

impl<Pk: FromStrKey, Ctx: ScriptContext> Miniscript<Pk, Ctx> {
    /// Attempt to parse an insane(scripts don't clear sanity checks)
    /// from string into a Miniscript representation.
    /// Use this to parse scripts with repeated pubkeys, timelock mixing, malleable
    /// scripts without sig or scripts that can exceed resource limits.
    /// Some of the analysis guarantees of miniscript are lost when dealing with
    /// insane scripts. In general, in a multi-party setting users should only
    /// accept sane scripts.
    pub fn from_str_insane(s: &str) -> Result<Miniscript<Pk, Ctx>, Error> {
        Miniscript::from_str_ext(s, &ExtParams::insane())
    }

    /// Attempt to parse an Miniscripts that don't follow the spec.
    /// Use this to parse scripts with repeated pubkeys, timelock mixing, malleable
    /// scripts, raw pubkey hashes without sig or scripts that can exceed resource limits.
    ///
    /// Use [`ExtParams`] builder to specify the types of non-sane rules to allow while parsing.
    pub fn from_str_ext(s: &str, ext: &ExtParams) -> Result<Miniscript<Pk, Ctx>, Error> {
        // This checks for invalid ASCII chars
        let top = expression::Tree::from_str(s)?;
        let ms: Miniscript<Pk, Ctx> = expression::FromTree::from_tree(top.root())?;
        ms.ext_check(ext)?;

        if ms.ty.corr.base != types::Base::B {
            Err(Error::NonTopLevel(format!("{:?}", ms)))
        } else {
            Ok(ms)
        }
    }
}

impl<Pk: FromStrKey, Ctx: ScriptContext> crate::expression::FromTree for Arc<Miniscript<Pk, Ctx>> {
    fn from_tree(root: expression::TreeIterItem) -> Result<Arc<Miniscript<Pk, Ctx>>, Error> {
        Ok(Arc::new(expression::FromTree::from_tree(root)?))
    }
}

impl<Pk: FromStrKey, Ctx: ScriptContext> crate::expression::FromTree for Miniscript<Pk, Ctx> {
    /// Parse an expression tree into a Miniscript. As a general rule, this
    /// should not be called directly; rather go through the descriptor API.
    fn from_tree(root: expression::TreeIterItem) -> Result<Miniscript<Pk, Ctx>, Error> {
        root.verify_no_curly_braces()
            .map_err(From::from)
            .map_err(Error::Parse)?;
        let inner: Terminal<Pk, Ctx> = expression::FromTree::from_tree(root)?;
        Miniscript::from_ast(inner)
    }
}

impl<Pk: FromStrKey, Ctx: ScriptContext> str::FromStr for Miniscript<Pk, Ctx> {
    type Err = Error;
    /// Parse a Miniscript from string and perform sanity checks
    /// See [Miniscript::from_str_insane] to parse scripts from string that
    /// do not clear the [Miniscript::sanity_check] checks.
    fn from_str(s: &str) -> Result<Miniscript<Pk, Ctx>, Error> {
        let ms = Self::from_str_ext(s, &ExtParams::sane())?;
        Ok(ms)
    }
}

serde_string_impl_pk!(Miniscript, "a miniscript", Ctx; ScriptContext);

/// Provides a Double SHA256 `Hash` type that displays forwards.
pub mod hash256 {
    use bitcoin::hashes::{hash_newtype, sha256d};

    hash_newtype! {
        /// A hash256 of preimage.
        #[hash_newtype(forward)]
        pub struct Hash(sha256d::Hash);
    }
}

#[cfg(test)]
mod tests {

    use core::str;
    use core::str::FromStr;

    use bitcoin::hashes::{hash160, sha256, Hash};
    use bitcoin::secp256k1::XOnlyPublicKey;
    use bitcoin::taproot::TapLeafHash;
    use sync::Arc;

    use super::{Miniscript, ScriptContext, Segwitv0, Tap};
    use crate::miniscript::{types, Terminal};
    use crate::policy::Liftable;
    use crate::prelude::*;
    use crate::test_utils::{StrKeyTranslator, StrXOnlyKeyTranslator};
    use crate::{
        hex_script, BareCtx, Error, ExtParams, Legacy, RelLockTime, Satisfier, ToPublicKey,
    };

    type Segwitv0Script = Miniscript<bitcoin::PublicKey, Segwitv0>;
    type Tapscript = Miniscript<bitcoin::secp256k1::XOnlyPublicKey, Tap>;

    fn pubkeys(n: usize) -> Vec<bitcoin::PublicKey> {
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
                    &secp256k1::SecretKey::from_slice(&sk[..]).expect("secret key"),
                ),
                compressed: true,
            };
            ret.push(pk);
        }
        ret
    }

    fn string_rtt<Ctx: ScriptContext>(
        script: Miniscript<bitcoin::PublicKey, Ctx>,
        expected_debug: &str,
        expected_display: &str,
    ) {
        assert_eq!(script.ty.corr.base, types::Base::B);
        let debug = format!("{:?}", script);
        let display = format!("{}", script);
        if let Some(expected) = expected_debug.into() {
            assert_eq!(debug, expected);
        }
        if let Some(expected) = expected_display.into() {
            assert_eq!(display, expected);
        }
        let roundtrip = Miniscript::from_str(&display).expect("parse string serialization");
        assert_eq!(roundtrip, script);
        assert_eq!(roundtrip.clone(), script);
    }

    fn string_display_debug_test<Ctx: ScriptContext>(
        script: Miniscript<bitcoin::PublicKey, Ctx>,
        expected_debug: &str,
        expected_display: &str,
    ) {
        assert_eq!(script.ty.corr.base, types::Base::B);
        let debug = format!("{:?}", script);
        let display = format!("{}", script);
        if let Some(expected) = expected_debug.into() {
            assert_eq!(debug, expected);
        }
        if let Some(expected) = expected_display.into() {
            assert_eq!(display, expected);
        }
    }

    fn dummy_string_rtt<Ctx: ScriptContext>(
        script: Miniscript<String, Ctx>,
        expected_debug: &str,
        expected_display: &str,
    ) {
        assert_eq!(script.ty.corr.base, types::Base::B);
        let debug = format!("{:?}", script);
        let display = format!("{}", script);
        if let Some(expected) = expected_debug.into() {
            assert_eq!(debug, expected);
        }
        if let Some(expected) = expected_display.into() {
            assert_eq!(display, expected);
        }
        let roundtrip = Miniscript::from_str(&display).expect("parse string serialization");
        assert_eq!(roundtrip, script);
    }

    fn script_rtt<Str1: Into<Option<&'static str>>>(script: Segwitv0Script, expected_hex: Str1) {
        assert_eq!(script.ty.corr.base, types::Base::B);
        let bitcoin_script = script.encode();
        assert_eq!(bitcoin_script.len(), script.script_size());
        if let Some(expected) = expected_hex.into() {
            assert_eq!(format!("{:x}", bitcoin_script), expected);
        }
        // Parse scripts with all extensions
        let roundtrip = Segwitv0Script::parse_with_ext(&bitcoin_script, &ExtParams::allow_all())
            .expect("parse string serialization");
        assert_eq!(roundtrip, script);
    }

    fn roundtrip(tree: &Segwitv0Script, s: &str) {
        assert_eq!(tree.ty.corr.base, types::Base::B);
        let ser = tree.encode();
        assert_eq!(ser.len(), tree.script_size());
        assert_eq!(ser.to_string(), s);
        let deser = Segwitv0Script::parse_insane(&ser).expect("deserialize result of serialize");
        assert_eq!(*tree, deser);
    }

    fn ms_attributes_test(
        ms: &str,
        expected_hex: &str,
        valid: bool,
        non_mal: bool,
        need_sig: bool,
        ops: usize,
        _stack: usize,
    ) {
        let ms: Result<Segwitv0Script, _> = Miniscript::from_str_insane(ms);
        match (ms, valid) {
            (Ok(ms), true) => {
                assert_eq!(format!("{:x}", ms.encode()), expected_hex);
                assert_eq!(ms.ty.mall.non_malleable, non_mal);
                assert_eq!(ms.ty.mall.safe, need_sig);
                assert_eq!(ms.ext.ops.op_count().unwrap(), ops);
            }
            (Err(_), false) => {}
            _ => unreachable!(),
        }
    }

    #[test]
    fn all_attribute_tests() {
        ms_attributes_test(
            "lltvln:after(1231488000)",
            "6300676300676300670400046749b1926869516868",
            true,
            true,
            false,
            12,
            3,
        );
        ms_attributes_test("uuj:and_v(v:multi(2,03d01115d548e7561b15c38f004d734633687cf4419620095bc5b0f47070afe85a,025601570cb47f238d2b0286db4a990fa0f3ba28d1a319f5e7cf55c2a2444da7cc),after(1231488000))", "6363829263522103d01115d548e7561b15c38f004d734633687cf4419620095bc5b0f47070afe85a21025601570cb47f238d2b0286db4a990fa0f3ba28d1a319f5e7cf55c2a2444da7cc52af0400046749b168670068670068", true, true, true, 14, 5);
        ms_attributes_test("or_b(un:multi(2,03daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729,024ce119c96e2fa357200b559b2f7dd5a5f02d5290aff74b03f3e471b273211c97),al:older(16))", "63522103daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee872921024ce119c96e2fa357200b559b2f7dd5a5f02d5290aff74b03f3e471b273211c9752ae926700686b63006760b2686c9b", true, false, false, 14, 5);
        ms_attributes_test(
            "j:and_v(vdv:after(1567547623),older(2016))",
            "829263766304e7e06e5db169686902e007b268",
            true,
            true,
            false,
            11,
            1,
        );
        ms_attributes_test("t:and_v(vu:hash256(131772552c01444cd81360818376a040b7c3b2b7b0a53550ee3edde216cec61b),v:sha256(ec4916dd28fc4c10d78e287ca5d9cc51ee1ae73cbfde08c6b37324cbfaac8bc5))", "6382012088aa20131772552c01444cd81360818376a040b7c3b2b7b0a53550ee3edde216cec61b876700686982012088a820ec4916dd28fc4c10d78e287ca5d9cc51ee1ae73cbfde08c6b37324cbfaac8bc58851", true, true, false, 12, 3);
        ms_attributes_test("t:andor(multi(3,02d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e,03fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a1460297556,02e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd13),v:older(4194305),v:sha256(9267d3dbed802941483f1afa2a6bc68de5f653128aca9bf1461c5d0a3ad36ed2))", "532102d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e2103fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a14602975562102e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd1353ae6482012088a8209267d3dbed802941483f1afa2a6bc68de5f653128aca9bf1461c5d0a3ad36ed2886703010040b2696851", true, true, false, 13, 5);
        ms_attributes_test("or_d(multi(1,02f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9),or_b(multi(3,022f01e5e15cca351daff3843fb70f3c2f0a1bdd05e5af888a67784ef3e10a2a01,032fa2104d6b38d11b0230010559879124e42ab8dfeff5ff29dc9cdadd4ecacc3f,03d01115d548e7561b15c38f004d734633687cf4419620095bc5b0f47070afe85a),su:after(500000)))", "512102f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f951ae73645321022f01e5e15cca351daff3843fb70f3c2f0a1bdd05e5af888a67784ef3e10a2a0121032fa2104d6b38d11b0230010559879124e42ab8dfeff5ff29dc9cdadd4ecacc3f2103d01115d548e7561b15c38f004d734633687cf4419620095bc5b0f47070afe85a53ae7c630320a107b16700689b68", true, true, false, 15, 7);
        ms_attributes_test("or_d(sha256(38df1c1f64a24a77b23393bca50dff872e31edc4f3b5aa3b90ad0b82f4f089b6),and_n(un:after(499999999),older(4194305)))", "82012088a82038df1c1f64a24a77b23393bca50dff872e31edc4f3b5aa3b90ad0b82f4f089b68773646304ff64cd1db19267006864006703010040b26868", true, false, false, 16, 1);
        ms_attributes_test("and_v(or_i(v:multi(2,02c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5,03774ae7f858a9411e5ef4246b70c65aac5649980be5c17891bbec17895da008cb),v:multi(2,03e60fce93b59e9ec53011aabc21c23e97b2a31369b87a5ae9c44ee89e2a6dec0a,025cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc)),sha256(d1ec675902ef1633427ca360b290b0b3045a0d9058ddb5e648b4c3c3224c5c68))", "63522102c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee52103774ae7f858a9411e5ef4246b70c65aac5649980be5c17891bbec17895da008cb52af67522103e60fce93b59e9ec53011aabc21c23e97b2a31369b87a5ae9c44ee89e2a6dec0a21025cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc52af6882012088a820d1ec675902ef1633427ca360b290b0b3045a0d9058ddb5e648b4c3c3224c5c6887", true, true, true, 11, 5);
        ms_attributes_test("j:and_b(multi(2,0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,024ce119c96e2fa357200b559b2f7dd5a5f02d5290aff74b03f3e471b273211c97),s:or_i(older(1),older(4252898)))", "82926352210279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f8179821024ce119c96e2fa357200b559b2f7dd5a5f02d5290aff74b03f3e471b273211c9752ae7c6351b26703e2e440b2689a68", true, false, true, 14, 4);
        ms_attributes_test("and_b(older(16),s:or_d(sha256(e38990d0c7fc009880a9c07c23842e886c6bbdc964ce6bdd5817ad357335ee6f),n:after(1567547623)))", "60b27c82012088a820e38990d0c7fc009880a9c07c23842e886c6bbdc964ce6bdd5817ad357335ee6f87736404e7e06e5db192689a", true, false, false, 12, 1);
        ms_attributes_test("j:and_v(v:hash160(20195b5a3d650c17f0f29f91c33f8f6335193d07),or_d(sha256(96de8fc8c256fa1e1556d41af431cace7dca68707c78dd88c3acab8b17164c47),older(16)))", "82926382012088a91420195b5a3d650c17f0f29f91c33f8f6335193d078882012088a82096de8fc8c256fa1e1556d41af431cace7dca68707c78dd88c3acab8b17164c4787736460b26868", true, false, false, 16, 2);
        ms_attributes_test("and_b(hash256(32ba476771d01e37807990ead8719f08af494723de1d228f2c2c07cc0aa40bac),a:and_b(hash256(131772552c01444cd81360818376a040b7c3b2b7b0a53550ee3edde216cec61b),a:older(1)))", "82012088aa2032ba476771d01e37807990ead8719f08af494723de1d228f2c2c07cc0aa40bac876b82012088aa20131772552c01444cd81360818376a040b7c3b2b7b0a53550ee3edde216cec61b876b51b26c9a6c9a", true, true, false, 15, 2);
        ms_attributes_test("thresh(2,multi(2,03a0434d9e47f3c86235477c7b1ae6ae5d3442d49b1943c2b752a68e2a47e247c7,036d2b085e9e382ed10b69fc311a03f8641ccfff21574de0927513a49d9a688a00),a:multi(1,036d2b085e9e382ed10b69fc311a03f8641ccfff21574de0927513a49d9a688a00),ac:pk_k(022f01e5e15cca351daff3843fb70f3c2f0a1bdd05e5af888a67784ef3e10a2a01))", "522103a0434d9e47f3c86235477c7b1ae6ae5d3442d49b1943c2b752a68e2a47e247c721036d2b085e9e382ed10b69fc311a03f8641ccfff21574de0927513a49d9a688a0052ae6b5121036d2b085e9e382ed10b69fc311a03f8641ccfff21574de0927513a49d9a688a0051ae6c936b21022f01e5e15cca351daff3843fb70f3c2f0a1bdd05e5af888a67784ef3e10a2a01ac6c935287", true, true, true, 13, 6);
        ms_attributes_test("and_n(sha256(d1ec675902ef1633427ca360b290b0b3045a0d9058ddb5e648b4c3c3224c5c68),t:or_i(v:older(4252898),v:older(144)))", "82012088a820d1ec675902ef1633427ca360b290b0b3045a0d9058ddb5e648b4c3c3224c5c68876400676303e2e440b26967029000b269685168", true, false, false, 14, 2);
        ms_attributes_test("or_d(nd:and_v(v:older(4252898),v:older(4252898)),sha256(38df1c1f64a24a77b23393bca50dff872e31edc4f3b5aa3b90ad0b82f4f089b6))", "766303e2e440b26903e2e440b2696892736482012088a82038df1c1f64a24a77b23393bca50dff872e31edc4f3b5aa3b90ad0b82f4f089b68768", true, false, false, 15, 2);
        ms_attributes_test("c:and_v(or_c(sha256(9267d3dbed802941483f1afa2a6bc68de5f653128aca9bf1461c5d0a3ad36ed2),v:multi(1,02c44d12c7065d812e8acf28d7cbb19f9011ecd9e9fdf281b0e6a3b5e87d22e7db)),pk_k(03acd484e2f0c7f65309ad178a9f559abde09796974c57e714c35f110dfc27ccbe))", "82012088a8209267d3dbed802941483f1afa2a6bc68de5f653128aca9bf1461c5d0a3ad36ed28764512102c44d12c7065d812e8acf28d7cbb19f9011ecd9e9fdf281b0e6a3b5e87d22e7db51af682103acd484e2f0c7f65309ad178a9f559abde09796974c57e714c35f110dfc27ccbeac", true, false, true, 9, 2);
        ms_attributes_test("c:and_v(or_c(multi(2,036d2b085e9e382ed10b69fc311a03f8641ccfff21574de0927513a49d9a688a00,02352bbf4a4cdd12564f93fa332ce333301d9ad40271f8107181340aef25be59d5),v:ripemd160(1b0f3c404d12075c68c938f9f60ebea4f74941a0)),pk_k(03fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a1460297556))", "5221036d2b085e9e382ed10b69fc311a03f8641ccfff21574de0927513a49d9a688a002102352bbf4a4cdd12564f93fa332ce333301d9ad40271f8107181340aef25be59d552ae6482012088a6141b0f3c404d12075c68c938f9f60ebea4f74941a088682103fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a1460297556ac", true, true, true, 10, 5);
        ms_attributes_test("and_v(andor(hash256(8a35d9ca92a48eaade6f53a64985e9e2afeb74dcf8acb4c3721e0dc7e4294b25),v:hash256(939894f70e6c3a25da75da0cc2071b4076d9b006563cf635986ada2e93c0d735),v:older(50000)),after(499999999))", "82012088aa208a35d9ca92a48eaade6f53a64985e9e2afeb74dcf8acb4c3721e0dc7e4294b2587640350c300b2696782012088aa20939894f70e6c3a25da75da0cc2071b4076d9b006563cf635986ada2e93c0d735886804ff64cd1db1", true, false, false, 14, 2);
        ms_attributes_test("andor(hash256(5f8d30e655a7ba0d7596bb3ddfb1d2d20390d23b1845000e1e118b3be1b3f040),j:and_v(v:hash160(3a2bff0da9d96868e66abc4427bea4691cf61ccd),older(4194305)),ripemd160(44d90e2d3714c8663b632fcf0f9d5f22192cc4c8))", "82012088aa205f8d30e655a7ba0d7596bb3ddfb1d2d20390d23b1845000e1e118b3be1b3f040876482012088a61444d90e2d3714c8663b632fcf0f9d5f22192cc4c8876782926382012088a9143a2bff0da9d96868e66abc4427bea4691cf61ccd8803010040b26868", true, false, false, 20, 2);
        ms_attributes_test("or_i(c:and_v(v:after(500000),pk_k(02c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5)),sha256(d9147961436944f43cd99d28b2bbddbf452ef872b30c8279e255e7daafc7f946))", "630320a107b1692102c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5ac6782012088a820d9147961436944f43cd99d28b2bbddbf452ef872b30c8279e255e7daafc7f9468768", true, true, false, 10, 2);
        ms_attributes_test("thresh(2,c:pk_h(03daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729),s:sha256(e38990d0c7fc009880a9c07c23842e886c6bbdc964ce6bdd5817ad357335ee6f),a:hash160(dd69735817e0e3f6f826a9238dc2e291184f0131))", "76a91420d637c1a6404d2227f3561fdbaff5a680dba64888ac7c82012088a820e38990d0c7fc009880a9c07c23842e886c6bbdc964ce6bdd5817ad357335ee6f87936b82012088a914dd69735817e0e3f6f826a9238dc2e291184f0131876c935287", true, false, false, 18, 4);
        ms_attributes_test("and_n(sha256(9267d3dbed802941483f1afa2a6bc68de5f653128aca9bf1461c5d0a3ad36ed2),uc:and_v(v:older(144),pk_k(03fe72c435413d33d48ac09c9161ba8b09683215439d62b7940502bda8b202e6ce)))", "82012088a8209267d3dbed802941483f1afa2a6bc68de5f653128aca9bf1461c5d0a3ad36ed28764006763029000b2692103fe72c435413d33d48ac09c9161ba8b09683215439d62b7940502bda8b202e6ceac67006868", true, false, true, 13, 3);
        ms_attributes_test("and_n(c:pk_k(03daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729),and_b(l:older(4252898),a:older(16)))", "2103daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729ac64006763006703e2e440b2686b60b26c9a68", true, true, true, 12, 2);
        ms_attributes_test("c:or_i(and_v(v:older(16),pk_h(03daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729)),pk_h(02352bbf4a4cdd12564f93fa332ce333301d9ad40271f8107181340aef25be59d5))", "6360b26976a91420d637c1a6404d2227f3561fdbaff5a680dba648886776a9148f9dff39a81ee4abcbad2ad8bafff090415a2be88868ac", true, true, true, 12, 3);
        ms_attributes_test("or_d(c:pk_h(02352bbf4a4cdd12564f93fa332ce333301d9ad40271f8107181340aef25be59d5),andor(c:pk_k(024ce119c96e2fa357200b559b2f7dd5a5f02d5290aff74b03f3e471b273211c97),older(2016),after(1567547623)))", "76a9148f9dff39a81ee4abcbad2ad8bafff090415a2be888ac736421024ce119c96e2fa357200b559b2f7dd5a5f02d5290aff74b03f3e471b273211c97ac6404e7e06e5db16702e007b26868", true, true, false, 13, 3);
        ms_attributes_test("c:andor(ripemd160(6ad07d21fd5dfc646f0b30577045ce201616b9ba),pk_h(03daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729),and_v(v:hash256(8a35d9ca92a48eaade6f53a64985e9e2afeb74dcf8acb4c3721e0dc7e4294b25),pk_h(02352bbf4a4cdd12564f93fa332ce333301d9ad40271f8107181340aef25be59d5)))", "82012088a6146ad07d21fd5dfc646f0b30577045ce201616b9ba876482012088aa208a35d9ca92a48eaade6f53a64985e9e2afeb74dcf8acb4c3721e0dc7e4294b258876a9148f9dff39a81ee4abcbad2ad8bafff090415a2be8886776a91420d637c1a6404d2227f3561fdbaff5a680dba6488868ac", true, false, true, 18, 3);
        ms_attributes_test("c:andor(u:ripemd160(6ad07d21fd5dfc646f0b30577045ce201616b9ba),pk_h(03daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729),or_i(pk_h(024ce119c96e2fa357200b559b2f7dd5a5f02d5290aff74b03f3e471b273211c97),pk_h(02352bbf4a4cdd12564f93fa332ce333301d9ad40271f8107181340aef25be59d5)))", "6382012088a6146ad07d21fd5dfc646f0b30577045ce201616b9ba87670068646376a914385defb0ed10fe95817943ed37b4984f8f4255d6886776a9148f9dff39a81ee4abcbad2ad8bafff090415a2be888686776a91420d637c1a6404d2227f3561fdbaff5a680dba6488868ac", true, false, true, 23, 4);
        ms_attributes_test("c:or_i(andor(c:pk_h(02352bbf4a4cdd12564f93fa332ce333301d9ad40271f8107181340aef25be59d5),pk_h(024ce119c96e2fa357200b559b2f7dd5a5f02d5290aff74b03f3e471b273211c97),pk_h(03daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729)),pk_k(03fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a1460297556))", "6376a9148f9dff39a81ee4abcbad2ad8bafff090415a2be888ac6476a91420d637c1a6404d2227f3561fdbaff5a680dba648886776a914385defb0ed10fe95817943ed37b4984f8f4255d68868672103fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a146029755668ac", true, true, true, 17, 5);
    }

    #[test]
    fn basic() {
        let pk = bitcoin::PublicKey::from_str(
            "\
             020202020202020202020202020202020202020202020202020202020202020202\
             ",
        )
        .unwrap();
        let hash = hash160::Hash::from_byte_array([17; 20]);

        let pk_node = Terminal::Check(Arc::new(
            Miniscript::from_ast(Terminal::PkK(String::from(""))).unwrap(),
        ));
        let pkk_ms: Miniscript<String, Segwitv0> = Miniscript::from_ast(pk_node).unwrap();
        dummy_string_rtt(pkk_ms, "[B/onduesm]pk(\"\")", "pk()");

        let pkh_node = Terminal::Check(Arc::new(
            Miniscript::from_ast(Terminal::PkH(String::from(""))).unwrap(),
        ));
        let pkh_ms: Miniscript<String, Segwitv0> = Miniscript::from_ast(pkh_node).unwrap();

        let expected_debug = "[B/nduesm]pkh(\"\")";
        let expected_display = "pkh()";

        assert_eq!(pkh_ms.ty.corr.base, types::Base::B);
        let debug = format!("{:?}", pkh_ms);
        let display = format!("{}", pkh_ms);
        if let Some(expected) = expected_debug.into() {
            assert_eq!(debug, expected);
        }
        if let Some(expected) = expected_display.into() {
            assert_eq!(display, expected);
        }

        let pkk_node = Terminal::Check(Arc::new(Miniscript::from_ast(Terminal::PkK(pk)).unwrap()));
        let pkk_ms: Segwitv0Script = Miniscript::from_ast(pkk_node).unwrap();

        script_rtt(
            pkk_ms,
            "21020202020202020202020202020202020202020202020202020202020\
             202020202ac",
        );

        let pkh_ms: Segwitv0Script = Miniscript::from_ast(Terminal::Check(Arc::new(
            Miniscript::from_ast(Terminal::RawPkH(hash)).unwrap(),
        )))
        .unwrap();

        script_rtt(pkh_ms, "76a914111111111111111111111111111111111111111188ac");
    }

    #[test]
    fn true_false() {
        roundtrip(&ms_str!("1"), "OP_PUSHNUM_1");
        roundtrip(&ms_str!("tv:1"), "OP_PUSHNUM_1 OP_VERIFY OP_PUSHNUM_1");
        roundtrip(&ms_str!("0"), "OP_0");
        roundtrip(&ms_str!("andor(0,1,0)"), "OP_0 OP_NOTIF OP_0 OP_ELSE OP_PUSHNUM_1 OP_ENDIF");

        assert!(Segwitv0Script::from_str("1()").is_err());
        assert!(Segwitv0Script::from_str("tv:1()").is_err());
    }

    #[test]
    fn verify_parse() {
        let ms = "and_v(v:hash160(20195b5a3d650c17f0f29f91c33f8f6335193d07),or_d(sha256(96de8fc8c256fa1e1556d41af431cace7dca68707c78dd88c3acab8b17164c47),older(16)))";
        let ms: Segwitv0Script = Miniscript::from_str_insane(ms).unwrap();
        assert_eq!(ms, Segwitv0Script::parse_insane(&ms.encode()).unwrap());

        let ms = "and_v(v:sha256(96de8fc8c256fa1e1556d41af431cace7dca68707c78dd88c3acab8b17164c47),or_d(sha256(96de8fc8c256fa1e1556d41af431cace7dca68707c78dd88c3acab8b17164c47),older(16)))";
        let ms: Segwitv0Script = Miniscript::from_str_insane(ms).unwrap();
        assert_eq!(ms, Segwitv0Script::parse_insane(&ms.encode()).unwrap());

        let ms = "and_v(v:ripemd160(20195b5a3d650c17f0f29f91c33f8f6335193d07),or_d(sha256(96de8fc8c256fa1e1556d41af431cace7dca68707c78dd88c3acab8b17164c47),older(16)))";
        let ms: Segwitv0Script = Miniscript::from_str_insane(ms).unwrap();
        assert_eq!(ms, Segwitv0Script::parse_insane(&ms.encode()).unwrap());

        let ms = "and_v(v:hash256(96de8fc8c256fa1e1556d41af431cace7dca68707c78dd88c3acab8b17164c47),or_d(sha256(96de8fc8c256fa1e1556d41af431cace7dca68707c78dd88c3acab8b17164c47),older(16)))";
        let ms: Segwitv0Script = Miniscript::from_str_insane(ms).unwrap();
        assert_eq!(ms, Segwitv0Script::parse_insane(&ms.encode()).unwrap());
    }

    #[test]
    fn pk_alias() {
        let pubkey = pubkeys(1)[0];

        let script: Segwitv0Script = ms_str!("c:pk_k({})", pubkey.to_string());

        string_rtt(
            script,
            "[B/onduesm]pk(PublicKey { compressed: true, inner: PublicKey(aa4c32e50fb34a95a372940ae3654b692ea35294748c3dd2c08b29f87ba9288c8294efcb73dc719e45b91c45f084e77aebc07c1ff3ed8f37935130a36304a340) })",
            "pk(028c28a97bf8298bc0d23d8c749452a32e694b65e30a9472a3954ab30fe5324caa)"
        );

        let script: Segwitv0Script = ms_str!("pk({})", pubkey.to_string());

        string_rtt(
            script,
            "[B/onduesm]pk(PublicKey { compressed: true, inner: PublicKey(aa4c32e50fb34a95a372940ae3654b692ea35294748c3dd2c08b29f87ba9288c8294efcb73dc719e45b91c45f084e77aebc07c1ff3ed8f37935130a36304a340) })",
            "pk(028c28a97bf8298bc0d23d8c749452a32e694b65e30a9472a3954ab30fe5324caa)"
        );

        let script: Segwitv0Script = ms_str!("tv:pk({})", pubkey.to_string());

        string_rtt(
            script,
            "[B/onufsm]t[V/onfsm]v:[B/onduesm]pk(PublicKey { compressed: true, inner: PublicKey(aa4c32e50fb34a95a372940ae3654b692ea35294748c3dd2c08b29f87ba9288c8294efcb73dc719e45b91c45f084e77aebc07c1ff3ed8f37935130a36304a340) })",
            "tv:pk(028c28a97bf8298bc0d23d8c749452a32e694b65e30a9472a3954ab30fe5324caa)"
        );

        let script: Segwitv0Script = ms_str!("c:pk_h({})", pubkey.to_string());

        string_display_debug_test(
            script,
            "[B/nduesm]pkh(PublicKey { compressed: true, inner: PublicKey(aa4c32e50fb34a95a372940ae3654b692ea35294748c3dd2c08b29f87ba9288c8294efcb73dc719e45b91c45f084e77aebc07c1ff3ed8f37935130a36304a340) })",
            "pkh(028c28a97bf8298bc0d23d8c749452a32e694b65e30a9472a3954ab30fe5324caa)",
        );

        let script: Segwitv0Script = ms_str!("pkh({})", pubkey.to_string());

        string_display_debug_test(
            script,
            "[B/nduesm]pkh(PublicKey { compressed: true, inner: PublicKey(aa4c32e50fb34a95a372940ae3654b692ea35294748c3dd2c08b29f87ba9288c8294efcb73dc719e45b91c45f084e77aebc07c1ff3ed8f37935130a36304a340) })",
            "pkh(028c28a97bf8298bc0d23d8c749452a32e694b65e30a9472a3954ab30fe5324caa)",
        );

        let script: Segwitv0Script = ms_str!("tv:pkh({})", pubkey.to_string());

        string_display_debug_test(
            script,
            "[B/nufsm]t[V/nfsm]v:[B/nduesm]pkh(PublicKey { compressed: true, inner: PublicKey(aa4c32e50fb34a95a372940ae3654b692ea35294748c3dd2c08b29f87ba9288c8294efcb73dc719e45b91c45f084e77aebc07c1ff3ed8f37935130a36304a340) })",
            "tv:pkh(028c28a97bf8298bc0d23d8c749452a32e694b65e30a9472a3954ab30fe5324caa)",
        );
    }

    #[test]
    fn serialize() {
        let keys = pubkeys(6);

        let tree: &Segwitv0Script = &ms_str!("c:pk_h({})", keys[5]);
        assert_eq!(tree.ty.corr.base, types::Base::B);
        let ser = tree.encode();
        let s = "\
             OP_DUP OP_HASH160 OP_PUSHBYTES_20 \
             7e5a2a6a7610ca4ea78bd65a087bd75b1870e319 \
             OP_EQUALVERIFY OP_CHECKSIG\
             ";
        assert_eq!(ser.len(), tree.script_size());
        assert_eq!(ser.to_string(), s);

        roundtrip(
            &ms_str!("pk({})", keys[0]),
            "OP_PUSHBYTES_33 028c28a97bf8298bc0d23d8c749452a32e694b65e30a9472a3954ab30fe5324caa OP_CHECKSIG"
        );
        roundtrip(
            &ms_str!("multi(3,{},{},{},{},{})", keys[0], keys[1], keys[2], keys[3], keys[4]),
            "OP_PUSHNUM_3 OP_PUSHBYTES_33 028c28a97bf8298bc0d23d8c749452a32e694b65e30a9472a3954ab30fe5324caa OP_PUSHBYTES_33 03ab1ac1872a38a2f196bed5a6047f0da2c8130fe8de49fc4d5dfb201f7611d8e2 OP_PUSHBYTES_33 039729247032c0dfcf45b4841fcd72f6e9a2422631fc3466cf863e87154754dd40 OP_PUSHBYTES_33 032564fe9b5beef82d3703a607253f31ef8ea1b365772df434226aee642651b3fa OP_PUSHBYTES_33 0289637f97580a796e050791ad5a2f27af1803645d95df021a3c2d82eb8c2ca7ff OP_PUSHNUM_5 OP_CHECKMULTISIG"
        );

        // Liquid policy
        roundtrip(
            &ms_str!("or_d(multi(2,{},{}),and_v(v:multi(2,{},{}),older(10000)))",
                      keys[0].to_string(),
                      keys[1].to_string(),
                      keys[3].to_string(),
                      keys[4].to_string()),
            "OP_PUSHNUM_2 OP_PUSHBYTES_33 028c28a97bf8298bc0d23d8c749452a32e694b65e30a9472a3954ab30fe5324caa \
                                  OP_PUSHBYTES_33 03ab1ac1872a38a2f196bed5a6047f0da2c8130fe8de49fc4d5dfb201f7611d8e2 \
                                  OP_PUSHNUM_2 OP_CHECKMULTISIG \
                     OP_IFDUP OP_NOTIF \
                         OP_PUSHNUM_2 OP_PUSHBYTES_33 032564fe9b5beef82d3703a607253f31ef8ea1b365772df434226aee642651b3fa \
                                      OP_PUSHBYTES_33 0289637f97580a796e050791ad5a2f27af1803645d95df021a3c2d82eb8c2ca7ff \
                                      OP_PUSHNUM_2 OP_CHECKMULTISIGVERIFY \
                         OP_PUSHBYTES_2 1027 OP_CSV \
                     OP_ENDIF"
        );

        let miniscript: Segwitv0Script = ms_str!(
            "or_d(multi(3,{},{},{}),and_v(v:multi(2,{},{}),older(10000)))",
            keys[0].to_string(),
            keys[1].to_string(),
            keys[2].to_string(),
            keys[3].to_string(),
            keys[4].to_string(),
        );

        let mut abs = miniscript.lift().unwrap();
        assert_eq!(abs.n_keys(), 5);
        assert_eq!(abs.minimum_n_keys(), Some(2));
        abs = abs.at_age(RelLockTime::from_height(10000).into());
        assert_eq!(abs.n_keys(), 5);
        assert_eq!(abs.minimum_n_keys(), Some(2));
        abs = abs.at_age(RelLockTime::from_height(9999).into());
        assert_eq!(abs.n_keys(), 3);
        assert_eq!(abs.minimum_n_keys(), Some(3));
        abs = abs.at_age(RelLockTime::ZERO.into());
        assert_eq!(abs.n_keys(), 3);
        assert_eq!(abs.minimum_n_keys(), Some(3));

        roundtrip(&ms_str!("older(921)"), "OP_PUSHBYTES_2 9903 OP_CSV");

        roundtrip(
            &ms_str!("sha256({})",sha256::Hash::hash(&[])),
            "OP_SIZE OP_PUSHBYTES_1 20 OP_EQUALVERIFY OP_SHA256 OP_PUSHBYTES_32 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 OP_EQUAL"
        );

        roundtrip(
            &ms_str!("multi(3,{},{},{},{},{})", keys[0], keys[1], keys[2], keys[3], keys[4]),
            "OP_PUSHNUM_3 \
             OP_PUSHBYTES_33 028c28a97bf8298bc0d23d8c749452a32e694b65e30a9472a3954ab30fe5324caa \
             OP_PUSHBYTES_33 03ab1ac1872a38a2f196bed5a6047f0da2c8130fe8de49fc4d5dfb201f7611d8e2 \
             OP_PUSHBYTES_33 039729247032c0dfcf45b4841fcd72f6e9a2422631fc3466cf863e87154754dd40 \
             OP_PUSHBYTES_33 032564fe9b5beef82d3703a607253f31ef8ea1b365772df434226aee642651b3fa \
             OP_PUSHBYTES_33 0289637f97580a796e050791ad5a2f27af1803645d95df021a3c2d82eb8c2ca7ff \
             OP_PUSHNUM_5 OP_CHECKMULTISIG",
        );

        roundtrip(
            &ms_str!(
                "t:and_v(\
                     vu:hash256(131772552c01444cd81360818376a040b7c3b2b7b0a53550ee3edde216cec61b),\
                     v:sha256(ec4916dd28fc4c10d78e287ca5d9cc51ee1ae73cbfde08c6b37324cbfaac8bc5)\
                 )"),
            "OP_IF OP_SIZE OP_PUSHBYTES_1 20 OP_EQUALVERIFY OP_HASH256 OP_PUSHBYTES_32 131772552c01444cd81360818376a040b7c3b2b7b0a53550ee3edde216cec61b OP_EQUAL OP_ELSE OP_0 OP_ENDIF OP_VERIFY OP_SIZE OP_PUSHBYTES_1 20 OP_EQUALVERIFY OP_SHA256 OP_PUSHBYTES_32 ec4916dd28fc4c10d78e287ca5d9cc51ee1ae73cbfde08c6b37324cbfaac8bc5 OP_EQUALVERIFY OP_PUSHNUM_1"
        );
        roundtrip(
            &ms_str!("and_n(pk(03daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729),and_b(l:older(4252898),a:older(16)))"),
            "OP_PUSHBYTES_33 03daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729 OP_CHECKSIG OP_NOTIF OP_0 OP_ELSE OP_IF OP_0 OP_ELSE OP_PUSHBYTES_3 e2e440 OP_CSV OP_ENDIF OP_TOALTSTACK OP_PUSHNUM_16 OP_CSV OP_FROMALTSTACK OP_BOOLAND OP_ENDIF"
        );
        roundtrip(
            &ms_str!(
                "t:andor(multi(\
                    3,\
                    02d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e,\
                    03fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a1460297556,\
                    02e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd13\
                 ),\
                 v:older(4194305),\
                 v:sha256(9267d3dbed802941483f1afa2a6bc68de5f653128aca9bf1461c5d0a3ad36ed2)\
                 )"),
            "OP_PUSHNUM_3 OP_PUSHBYTES_33 02d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e \
             OP_PUSHBYTES_33 03fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a1460297556 \
             OP_PUSHBYTES_33 02e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd13 \
             OP_PUSHNUM_3 OP_CHECKMULTISIG OP_NOTIF OP_SIZE OP_PUSHBYTES_1 20 OP_EQUALVERIFY OP_SHA256 \
             OP_PUSHBYTES_32 9267d3dbed802941483f1afa2a6bc68de5f653128aca9bf1461c5d0a3ad36ed2 OP_EQUALVERIFY \
             OP_ELSE OP_PUSHBYTES_3 010040 OP_CSV OP_VERIFY OP_ENDIF OP_PUSHNUM_1"
        );
        roundtrip(
            &ms_str!(
                "t:and_v(\
                    vu:hash256(131772552c01444cd81360818376a040b7c3b2b7b0a53550ee3edde216cec61b),\
                    v:sha256(ec4916dd28fc4c10d78e287ca5d9cc51ee1ae73cbfde08c6b37324cbfaac8bc5)\
                 )"),
            "\
             OP_IF OP_SIZE OP_PUSHBYTES_1 20 OP_EQUALVERIFY OP_HASH256 OP_PUSHBYTES_32 131772552c01444cd81360818376a040b7c3b2b7b0a53550ee3edde216cec61b OP_EQUAL \
             OP_ELSE OP_0 OP_ENDIF OP_VERIFY OP_SIZE OP_PUSHBYTES_1 20 OP_EQUALVERIFY OP_SHA256 OP_PUSHBYTES_32 ec4916dd28fc4c10d78e287ca5d9cc51ee1ae73cbfde08c6b37324cbfaac8bc5 OP_EQUALVERIFY \
             OP_PUSHNUM_1\
             "
        );

        // Thresh bug with equal verify roundtrip
        roundtrip(
            &ms_str!("tv:thresh(1,pk(02d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e))", ),
            "OP_PUSHBYTES_33 02d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e OP_CHECKSIG OP_PUSHNUM_1 OP_EQUALVERIFY OP_PUSHNUM_1",
        );
    }

    #[test]
    fn deserialize() {
        // Most of these came from fuzzing, hence the increasing lengths
        assert!(Segwitv0Script::parse_insane(&hex_script("")).is_err()); // empty
        assert!(Segwitv0Script::parse_insane(&hex_script("00")).is_ok()); // FALSE
        assert!(Segwitv0Script::parse_insane(&hex_script("51")).is_ok()); // TRUE
        assert!(Segwitv0Script::parse_insane(&hex_script("69")).is_err()); // VERIFY
        assert!(Segwitv0Script::parse_insane(&hex_script("0000")).is_err()); //and_v(FALSE,FALSE)
        assert!(Segwitv0Script::parse_insane(&hex_script("1001")).is_err()); // incomplete push
        assert!(Segwitv0Script::parse_insane(&hex_script("03990300b2")).is_err()); // non-minimal #
        assert!(Segwitv0Script::parse_insane(&hex_script("8559b2")).is_err()); // leading bytes
        assert!(Segwitv0Script::parse_insane(&hex_script("4c0169b2")).is_err()); // non-minimal push
        assert!(Segwitv0Script::parse_insane(&hex_script("0000af0000ae85")).is_err()); // OR not BOOLOR

        // misc fuzzer problems
        assert!(Segwitv0Script::parse_insane(&hex_script("0000000000af")).is_err());
        assert!(Segwitv0Script::parse_insane(&hex_script("04009a2970af00")).is_err()); // giant CMS key num
        assert!(Segwitv0Script::parse_insane(&hex_script(
            "2102ffffffffffffffefefefefefefefefefefef394c0fe5b711179e124008584753ac6900"
        ))
        .is_err());
    }

    #[test]
    fn non_ascii() {
        assert!(Segwitv0Script::from_str_insane("🌏")
            .unwrap_err()
            .to_string()
            .contains("invalid character"));
    }

    #[test]
    fn test_tapscript_rtt() {
        // Test x-only invalid under segwitc0 context
        Segwitv0Script::from_str_insane(
            "pk(2788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99)",
        )
        .unwrap_err();
        Tapscript::from_str_insane(
            "pk(2788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99)",
        )
        .unwrap();

        // Now test that bitcoin::PublicKey works with Taproot context
        Miniscript::<bitcoin::PublicKey, Tap>::from_str_insane(
            "pk(022788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99)",
        )
        .unwrap();

        // uncompressed keys should not be allowed
        Miniscript::<bitcoin::PublicKey, Tap>::from_str_insane(
            "pk(04eed24a081bf1b1e49e3300df4bebe04208ac7e516b6f3ea8eb6e094584267c13483f89dcf194132e12238cc5a34b6b286fc7990d68ed1db86b69ebd826c63b29)"
        )
        .unwrap_err();

        //---------------- test script <-> miniscript ---------------
        // Test parsing from scripts: x-only fails decoding in segwitv0 ctx
        Segwitv0Script::parse_insane(&hex_script(
            "202788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99ac",
        ))
        .unwrap_err();
        // x-only succeeds in tap ctx
        Tapscript::parse_insane(&hex_script(
            "202788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99ac",
        ))
        .unwrap();
        // tapscript fails decoding with compressed
        Tapscript::parse_insane(&hex_script(
            "21022788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99ac",
        ))
        .unwrap_err();
        // Segwitv0 succeeds decoding with tapscript.
        Segwitv0Script::parse_insane(&hex_script(
            "21022788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99ac",
        ))
        .unwrap();

        // multi not allowed in tapscript
        Tapscript::from_str_insane(
            "multi(1,2788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99)",
        )
        .unwrap_err();
        // but allowed in segwit
        Segwitv0Script::from_str_insane(
            "multi(1,022788ee41e76f4f3af603da5bc8fa22997bc0344bb0f95666ba6aaff0242baa99)",
        )
        .unwrap();
    }

    #[test]
    fn multi_a_tests() {
        // Test from string tests
        type Segwitv0Ms = Miniscript<String, Segwitv0>;
        type TapMs = Miniscript<String, Tap>;
        let segwit_multi_a_ms = Segwitv0Ms::from_str_insane("multi_a(1,A,B,C)");
        assert_eq!(
            segwit_multi_a_ms.unwrap_err().to_string(),
            "Multi a(CHECKSIGADD) only allowed post tapscript"
        );
        let tap_multi_a_ms = TapMs::from_str_insane("multi_a(1,A,B,C)").unwrap();
        assert_eq!(tap_multi_a_ms.to_string(), "multi_a(1,A,B,C)");

        // Test encode/decode and translation tests
        let tap_ms = tap_multi_a_ms
            .translate_pk(&mut StrXOnlyKeyTranslator::new())
            .unwrap();
        // script rtt test
        assert_eq!(
            Miniscript::<XOnlyPublicKey, Tap>::parse_insane(&tap_ms.encode()).unwrap(),
            tap_ms
        );
        assert_eq!(tap_ms.script_size(), 104);
        assert_eq!(tap_ms.encode().len(), tap_ms.script_size());

        // Test satisfaction code
        struct SimpleSatisfier(secp256k1::schnorr::Signature);

        // a simple satisfier that always outputs the same signature
        impl<Pk: ToPublicKey> Satisfier<Pk> for SimpleSatisfier {
            fn lookup_tap_leaf_script_sig(
                &self,
                _pk: &Pk,
                _h: &TapLeafHash,
            ) -> Option<bitcoin::taproot::Signature> {
                Some(bitcoin::taproot::Signature {
                    signature: self.0,
                    sighash_type: bitcoin::sighash::TapSighashType::Default,
                })
            }
        }

        let schnorr_sig = secp256k1::schnorr::Signature::from_str("84526253c27c7aef56c7b71a5cd25bebb66dddda437826defc5b2568bde81f0784526253c27c7aef56c7b71a5cd25bebb66dddda437826defc5b2568bde81f07").unwrap();
        let s = SimpleSatisfier(schnorr_sig);
        let template = tap_ms.build_template(&s);
        assert_eq!(template.absolute_timelock, None);
        assert_eq!(template.relative_timelock, None);

        let wit = tap_ms.satisfy(&s).unwrap();
        assert_eq!(wit, vec![schnorr_sig.as_ref().to_vec(), vec![], vec![]]);
    }

    #[test]
    fn decode_bug_cpp_review() {
        let ms = Miniscript::<String, Segwitv0>::from_str_insane(
            "and_b(1,s:and_v(v:older(9),c:pk_k(A)))",
        )
        .unwrap();
        let ms_trans = ms.translate_pk(&mut StrKeyTranslator::new()).unwrap();
        let enc = ms_trans.encode();
        let ms = Miniscript::<bitcoin::PublicKey, Segwitv0>::parse_insane(&enc).unwrap();
        assert_eq!(ms_trans.encode(), ms.encode());
    }

    #[test]
    fn expr_features() {
        // test that parsing raw hash160 does not work with
        let pk = bitcoin::PublicKey::from_str(
            "02c2fd50ceae468857bb7eb32ae9cd4083e6c7e42fbbec179d81134b3e3830586c",
        )
        .unwrap();
        let hash160 = pk.pubkey_hash().to_raw_hash();
        let ms_str = &format!("c:expr_raw_pkh({})", hash160);
        type SegwitMs = Miniscript<bitcoin::PublicKey, Segwitv0>;

        // Test that parsing raw hash160 from string does not work without extra features
        SegwitMs::from_str(ms_str).unwrap_err();
        SegwitMs::from_str_insane(ms_str).unwrap_err();
        let ms = SegwitMs::from_str_ext(ms_str, &ExtParams::allow_all()).unwrap();

        let script = ms.encode();
        // The same test, but parsing from script
        SegwitMs::parse(&script).unwrap_err();
        SegwitMs::parse_insane(&script).unwrap_err();
        SegwitMs::parse_with_ext(&script, &ExtParams::allow_all()).unwrap();

        // Try replacing the raw_pkh with a pkh
        let mut map = BTreeMap::new();
        map.insert(hash160, pk);
        let ms_no_raw = ms.substitute_raw_pkh(&map);
        assert_eq!(ms_no_raw.to_string(), format!("pkh({})", pk),);
    }

    #[test]
    fn tr_multi_a_j_wrapper() {
        // Reported by darosior
        // `multi_a` fragment may require the top stack element to be the empty vector.
        // Previous version had incorrectly copied this code from multi.
        type TapMs = Miniscript<String, Tap>;
        let ms_str = TapMs::from_str_insane("j:multi_a(1,A,B,C)");
        assert!(ms_str.is_err());
    }

    #[test]
    fn translate_tests() {
        let ms = Miniscript::<String, Segwitv0>::from_str("pk(A)").unwrap();
        let mut t = StrKeyTranslator::new();
        let uncompressed = bitcoin::PublicKey::from_str("0400232a2acfc9b43fa89f1b4f608fde335d330d7114f70ea42bfb4a41db368a3e3be6934a4097dd25728438ef73debb1f2ffdb07fec0f18049df13bdc5285dc5b").unwrap();
        t.pk_map.insert(String::from("A"), uncompressed);
        ms.translate_pk(&mut t).unwrap_err();
    }

    #[test]
    fn duplicate_keys() {
        // You cannot parse a Miniscript that has duplicate keys
        let err = Miniscript::<String, Segwitv0>::from_str("and_v(v:pk(A),pk(A))").unwrap_err();
        assert!(matches!(err, Error::AnalysisError(crate::AnalysisError::RepeatedPubkeys)));

        // ...though you can parse one with from_str_insane
        let ok_insane =
            Miniscript::<String, Segwitv0>::from_str_insane("and_v(v:pk(A),pk(A))").unwrap();
        // ...but this cannot be sanity checked.
        assert!(matches!(
            ok_insane.sanity_check().unwrap_err(),
            crate::AnalysisError::RepeatedPubkeys
        ));
        // ...it can be lifted, though it's unclear whether this is a deliberate
        // choice or just an accident. It seems weird given that duplicate public
        // keys are forbidden in several other places.
        ok_insane.lift().unwrap();
    }

    #[test]
    fn mixed_timelocks() {
        // You cannot parse a Miniscript that mixes timelocks.
        let err = Miniscript::<String, Segwitv0>::from_str(
            "and_v(v:and_v(v:older(4194304),pk(A)),and_v(v:older(1),pk(B)))",
        )
        .unwrap_err();
        assert!(matches!(
            err,
            Error::AnalysisError(crate::AnalysisError::HeightTimelockCombination)
        ));

        // Though you can in an or() rather than and()
        let ok_or = Miniscript::<String, Segwitv0>::from_str(
            "or_i(and_v(v:older(4194304),pk(A)),and_v(v:older(1),pk(B)))",
        )
        .unwrap();
        ok_or.sanity_check().unwrap();
        ok_or.lift().unwrap();

        // ...and you can parse one with from_str_insane
        let ok_insane = Miniscript::<String, Segwitv0>::from_str_insane(
            "and_v(v:and_v(v:older(4194304),pk(A)),and_v(v:older(1),pk(B)))",
        )
        .unwrap();
        // ...but this cannot be sanity checked or lifted
        assert_eq!(
            ok_insane.sanity_check().unwrap_err(),
            crate::AnalysisError::HeightTimelockCombination
        );
        assert!(matches!(
            ok_insane.lift().unwrap_err(),
            Error::LiftError(crate::policy::LiftError::HeightTimelockCombination)
        ));
    }

    #[test]
    fn template_timelocks() {
        use crate::{AbsLockTime, RelLockTime};
        let key_present = bitcoin::PublicKey::from_str(
            "0327a6ed0e71b451c79327aa9e4a6bb26ffb1c0056abc02c25e783f6096b79bb4f",
        )
        .unwrap();
        let key_missing = bitcoin::PublicKey::from_str(
            "03e4d788718644a59030b1d234d8bb8fff28314720b9a1a237874b74b089c638da",
        )
        .unwrap();

        // ms, absolute_timelock, relative_timelock
        let test_cases = vec![
            (format!("t:or_c(pk({}),v:pkh({}))", key_present, key_missing), None, None),
            (
                format!("thresh(2,pk({}),s:pk({}),snl:after(1))", key_present, key_missing),
                Some(AbsLockTime::from_consensus(1).unwrap()),
                None,
            ),
            (
                format!("or_d(pk({}),and_v(v:pk({}),older(12960)))", key_present, key_missing),
                None,
                None,
            ),
            (
                format!("or_d(pk({}),and_v(v:pk({}),older(12960)))", key_missing, key_present),
                None,
                Some(RelLockTime::from_height(12960)),
            ),
            (
                format!(
                    "thresh(3,pk({}),s:pk({}),snl:older(10),snl:after(11))",
                    key_present, key_missing
                ),
                Some(AbsLockTime::from_consensus(11).unwrap()),
                Some(RelLockTime::from_height(10)),
            ),
            (
                format!("and_v(v:and_v(v:pk({}),older(10)),older(20))", key_present),
                None,
                Some(RelLockTime::from_height(20)),
            ),
            (
                format!(
                    "andor(pk({}),older(10),and_v(v:pk({}),older(20)))",
                    key_present, key_missing
                ),
                None,
                Some(RelLockTime::from_height(10)),
            ),
        ];

        // Test satisfaction code
        struct SimpleSatisfier(secp256k1::schnorr::Signature, bitcoin::PublicKey);

        // a simple satisfier that always outputs the same signature
        impl Satisfier<bitcoin::PublicKey> for SimpleSatisfier {
            fn lookup_tap_leaf_script_sig(
                &self,
                pk: &bitcoin::PublicKey,
                _h: &TapLeafHash,
            ) -> Option<bitcoin::taproot::Signature> {
                if pk == &self.1 {
                    Some(bitcoin::taproot::Signature {
                        signature: self.0,
                        sighash_type: bitcoin::sighash::TapSighashType::Default,
                    })
                } else {
                    None
                }
            }

            fn check_older(&self, _: bitcoin::relative::LockTime) -> bool { true }

            fn check_after(&self, _: bitcoin::absolute::LockTime) -> bool { true }
        }

        let schnorr_sig = secp256k1::schnorr::Signature::from_str("84526253c27c7aef56c7b71a5cd25bebb66dddda437826defc5b2568bde81f0784526253c27c7aef56c7b71a5cd25bebb66dddda437826defc5b2568bde81f07").unwrap();
        let s = SimpleSatisfier(schnorr_sig, key_present);

        for (ms_str, absolute_timelock, relative_timelock) in test_cases {
            let ms = Miniscript::<bitcoin::PublicKey, Tap>::from_str(&ms_str).unwrap();
            let template = ms.build_template(&s);
            match template.stack {
                crate::miniscript::satisfy::Witness::Stack(_) => {}
                _ => panic!("All testcases should be possible"),
            }
            assert_eq!(template.absolute_timelock, absolute_timelock, "{}", ms_str);
            assert_eq!(template.relative_timelock, relative_timelock, "{}", ms_str);
        }
    }

    #[test]
    fn test_dos() {
        let ms = "slnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn:0";
        matches!(
            Miniscript::<String, Tap>::from_str_insane(ms),
            Err(Error::MaxRecursiveDepthExceeded)
        );
    }

    #[test]
    fn test_script_parse_dos() {
        let mut script = bitcoin::script::Builder::new().push_opcode(bitcoin::opcodes::OP_TRUE);
        for _ in 0..10000 {
            script = script.push_opcode(bitcoin::opcodes::all::OP_0NOTEQUAL);
        }
        Tapscript::parse_insane(&script.into_script()).unwrap_err();
    }

    #[test]
    fn test_context_global_consensus() {
        // Test from string tests
        type LegacyMs = Miniscript<String, Legacy>;
        type Segwitv0Ms = Miniscript<String, Segwitv0>;
        type BareMs = Miniscript<String, BareCtx>;

        // multisig script of 20 pubkeys exceeds 520 bytes
        let pubkey_vec_20: Vec<String> = (0..20).map(|x| x.to_string()).collect();
        // multisig script of 300 pubkeys exceeds 10,000 bytes
        let pubkey_vec_300: Vec<String> = (0..300).map(|x| x.to_string()).collect();

        // wrong multi_a for non-tapscript, while exceeding consensus size limit
        let legacy_multi_a_ms =
            LegacyMs::from_str(&format!("multi_a(20,{})", pubkey_vec_20.join(",")));
        let segwit_multi_a_ms =
            Segwitv0Ms::from_str(&format!("multi_a(300,{})", pubkey_vec_300.join(",")));
        let bare_multi_a_ms =
            BareMs::from_str(&format!("multi_a(300,{})", pubkey_vec_300.join(",")));

        // Should panic for wrong multi_a, even if it exceeds the max consensus size
        assert_eq!(
            legacy_multi_a_ms.unwrap_err().to_string(),
            "Multi a(CHECKSIGADD) only allowed post tapscript"
        );
        assert_eq!(
            segwit_multi_a_ms.unwrap_err().to_string(),
            "Multi a(CHECKSIGADD) only allowed post tapscript"
        );
        assert_eq!(
            bare_multi_a_ms.unwrap_err().to_string(),
            "Multi a(CHECKSIGADD) only allowed post tapscript"
        );

        // multisig script of 20 pubkeys exceeds 520 bytes
        let multi_ms = format!("multi(20,{})", pubkey_vec_20.join(","));
        // other than legacy, and_v to build 15 nested 20-of-20 multisig script
        // to exceed 10,000 bytes without violation of threshold limit(max: 20)
        let and_v_nested_multi_ms =
            format!("and_v(v:{},", multi_ms).repeat(14) + &multi_ms + "))))))))))))))";

        // correct multi for non-tapscript, but exceeding consensus size limit
        let legacy_multi_ms = LegacyMs::from_str(&multi_ms);
        let segwit_multi_ms = Segwitv0Ms::from_str(&and_v_nested_multi_ms);
        let bare_multi_ms = BareMs::from_str(&and_v_nested_multi_ms);

        // Should panic for exceeding the max consensus size, as multi properly used
        assert_eq!(
            legacy_multi_ms.unwrap_err().to_string(),
            "The Miniscript corresponding Script cannot be larger than 520 bytes, but got 685 bytes."
        );
        assert_eq!(
            segwit_multi_ms.unwrap_err().to_string(),
            "The Miniscript corresponding Script cannot be larger than 3600 bytes, but got 4110 bytes."
        );
        assert_eq!(
            bare_multi_ms.unwrap_err().to_string(),
            "The Miniscript corresponding Script cannot be larger than 10000 bytes, but got 10275 bytes."
        );
    }
}
