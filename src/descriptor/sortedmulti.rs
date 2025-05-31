// SPDX-License-Identifier: CC0-1.0

//! # Sorted Multi
//!
//! Implementation of sorted multi primitive for descriptors
//!

use core::fmt;
use core::marker::PhantomData;

use bitcoin::script;

use crate::blanket_traits::FromStrKey;
use crate::miniscript::context::ScriptContext;
use crate::miniscript::decode::Terminal;
use crate::miniscript::limits::MAX_PUBKEYS_PER_MULTISIG;
use crate::miniscript::satisfy::{Placeholder, Satisfaction};
use crate::plan::AssetProvider;
use crate::prelude::*;
use crate::sync::Arc;
use crate::{
    expression, policy, script_num_size, Error, ForEachKey, Miniscript, MiniscriptKey,
    ParseMiniscriptError, Satisfier, Threshold, ToPublicKey, TranslateErr, Translator,
    ValidationError, ValidationParams,
};

/// Contents of a "sortedmulti" descriptor
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SortedMultiVec<Pk: MiniscriptKey, Ctx: ScriptContext> {
    inner: Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>,
    /// The validation parameters used when constructing the object.
    validated: ValidationParams,
    /// The current ScriptContext for sortedmulti
    phantom: PhantomData<Ctx>,
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> SortedMultiVec<Pk, Ctx> {
    fn constructor_check(mut self, params: ValidationParams) -> Result<Self, ValidationError> {
        let ms = Miniscript::<Pk, Ctx>::multi(self.inner);
        // Check the limits before creating a new SortedMultiVec
        // For example, under p2sh context the scriptlen can only be
        // upto 520 bytes.
        ms.validate(&params)?;
        self.validated = params;
        if let Terminal::Multi(inner) = ms.node {
            self.inner = inner;
            Ok(self)
        } else {
            unreachable!()
        }
    }

    /// Create a new instance of `SortedMultiVec` given a list of keys and the threshold
    ///
    /// Internally checks all the applicable size limits and pubkey types limitations according to the current `Ctx`.
    pub fn new(thresh: Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>) -> Result<Self, ValidationError> {
        let ret = Self { inner: thresh, validated: ValidationParams::MAX, phantom: PhantomData };
        ret.constructor_check(Ctx::SANE)
    }

    /// Parse an expression tree into a SortedMultiVec
    pub fn from_tree(
        tree: expression::TreeIterItem,
        params: &ValidationParams,
    ) -> Result<Self, ParseMiniscriptError>
    where
        Pk: FromStrKey,
    {
        tree.verify_toplevel("sortedmulti", 1..)?;

        let ret = Self {
            inner: tree.verify_threshold(|sub| sub.verify_terminal("public_key"))?,
            validated: ValidationParams::MAX,
            phantom: PhantomData,
        };
        Ok(ret.constructor_check(Ctx::CONSENSUS.intersect(params))?)
    }

    /// This will panic if fpk returns an uncompressed key when
    /// converting to a Segwit descriptor. To prevent this panic, ensure
    /// fpk returns an error in this case instead.
    pub fn translate_pk<T>(
        &self,
        t: &mut T,
    ) -> Result<SortedMultiVec<T::TargetPk, Ctx>, TranslateErr<T::Error>>
    where
        T: Translator<Pk>,
    {
        let ret = SortedMultiVec {
            inner: self.inner.translate_ref(|pk| t.pk(pk))?,
            validated: self.validated,
            phantom: PhantomData,
        };
        ret.constructor_check(self.validated)
            .map_err(TranslateErr::OuterError)
    }

    /// The threshold value for the multisig.
    pub fn k(&self) -> usize { self.inner.k() }

    /// The number of keys in the multisig.
    pub fn n(&self) -> usize { self.inner.n() }

    /// Accessor for the public keys in the multisig.
    ///
    /// The keys in this structure might **not** be sorted. In general, they cannot be
    /// sorted until they are converted to consensus-encoded public keys, which may not
    /// be possible (for example for BIP32 paths with unfilled wildcards).
    pub fn pks(&self) -> &[Pk] { self.inner.data() }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> ForEachKey<Pk> for SortedMultiVec<Pk, Ctx> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, pred: F) -> bool {
        self.pks().iter().all(pred)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> SortedMultiVec<Pk, Ctx> {
    /// Sort the keys and return the internal [`Threshold`] object.
    ///
    /// This function computes the sorted list and its return value should be
    /// cached if it is needed multiple times. (Because the sorting is only
    /// possible when `Pk` implements the [`ToPublicKey`] trait, it cannot
    /// be done when `self` is constructed.)
    pub fn sorted_threshold(&self) -> Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>
    where
        Pk: ToPublicKey,
    {
        let mut thresh = self.inner.clone();
        // Sort pubkeys lexicographically according to BIP 67
        thresh.data_mut().sort_by(|a, b| {
            a.to_public_key()
                .inner
                .serialize()
                .partial_cmp(&b.to_public_key().inner.serialize())
                .unwrap()
        });
        thresh
    }

    #[deprecated(
        since = "TBD",
        note = "Use Self::sorted_threshold followed by Terminal::Multi or Miniscript::multi"
    )]
    /// Create Terminal::Multi containing sorted pubkeys
    pub fn sorted_node(&self) -> Terminal<Pk, Ctx>
    where
        Pk: ToPublicKey,
    {
        Terminal::Multi(self.sorted_threshold())
    }

    /// Encode as a Bitcoin script
    pub fn encode(&self) -> script::ScriptBuf
    where
        Pk: ToPublicKey,
    {
        Miniscript::<_, Ctx>::multi(self.sorted_threshold()).encode()
    }

    /// Attempt to produce a satisfying witness for the
    /// witness script represented by the parse tree
    pub fn satisfy<S>(&self, satisfier: S) -> Result<Vec<Vec<u8>>, Error>
    where
        Pk: ToPublicKey,
        S: Satisfier<Pk>,
    {
        let ms = Miniscript::<_, Ctx>::multi(self.sorted_threshold());
        ms.satisfy(satisfier)
    }

    /// Attempt to produce a witness template given the assets available
    pub fn build_template<P>(&self, provider: &P) -> Satisfaction<Placeholder<Pk>>
    where
        Pk: ToPublicKey,
        P: AssetProvider<Pk>,
    {
        let ms = Miniscript::<_, Ctx>::multi(self.sorted_threshold());
        ms.build_template(provider)
    }

    /// Size, in bytes of the script-pubkey. If this Miniscript is used outside
    /// of segwit (e.g. in a bare or P2SH descriptor), this quantity should be
    /// multiplied by 4 to compute the weight.
    ///
    /// In general, it is not recommended to use this function directly, but
    /// to instead call the corresponding function on a `Descriptor`, which
    /// will handle the segwit/non-segwit technicalities for you.
    pub fn script_size(&self) -> usize {
        script_num_size(self.k())
            + 1
            + script_num_size(self.n())
            + self.pks().iter().map(|pk| Ctx::pk_len(pk)).sum::<usize>()
    }

    /// Maximum number of witness elements used to satisfy the Miniscript
    /// fragment, including the witness script itself. Used to estimate
    /// the weight of the `VarInt` that specifies this number in a serialized
    /// transaction.
    ///
    /// This function may panic on malformed `Miniscript` objects which do
    /// not correspond to semantically sane Scripts. (Such scripts should be
    /// rejected at parse time. Any exceptions are bugs.)
    pub fn max_satisfaction_witness_elements(&self) -> usize { 2 + self.k() }

    /// Maximum size, in bytes, of a satisfying witness.
    /// In general, it is not recommended to use this function directly, but
    /// to instead call the corresponding function on a `Descriptor`, which
    /// will handle the segwit/non-segwit technicalities for you.
    ///
    /// All signatures are assumed to be 73 bytes in size, including the
    /// length prefix (segwit) or push opcode (pre-segwit) and sighash
    /// postfix.
    pub fn max_satisfaction_size(&self) -> usize { 1 + 73 * self.k() }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> policy::Liftable<Pk> for SortedMultiVec<Pk, Ctx> {
    fn lift(&self) -> Result<policy::semantic::Policy<Pk>, ValidationError> {
        Ok(policy::semantic::Policy::Thresh(
            self.inner
                .map_ref(|pk| Arc::new(policy::semantic::Policy::Key(pk.clone())))
                .forget_maximum(),
        ))
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> fmt::Debug for SortedMultiVec<Pk, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Display::fmt(self, f) }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> fmt::Display for SortedMultiVec<Pk, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.inner.display("sortedmulti", true), f)
    }
}

#[cfg(test)]
mod tests {
    use bitcoin::PublicKey;

    use super::*;
    use crate::miniscript::context::Legacy;

    #[test]
    fn too_many_pubkeys_for_p2sh() {
        // Arbitrary 65-byte public keys (66 with length prefix). We need distinct ones
        // to avoid getting DuplicateKey errors.
        let pks: Vec<PublicKey> = vec![
            "0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798b7c52588d95c3b9aa25b0403f1eef75702e84bb7597aabe663b82f6f04ef2777".parse().unwrap(),
            "04c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5e51e970159c23cc65c3a7be6b99315110809cd9acd992f1edc9bce55af301705".parse().unwrap(),
            "04f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9c77084f09cd217ebf01cc819d5c80ca99aff5666cb3ddce4934602897b4715bd".parse().unwrap(),
            "04e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd13ae1266c15f2baa48a9bd1df6715aebb7269851cc404201bf30168422b88c630d".parse().unwrap(),
            "042f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe42753ddd9c91a1c292b24562259363bd90877d8e454f297bf235782c459539959".parse().unwrap(),
            "04fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a146029755651ed8885530449df0c4169fe80ba3a9f217f0f09ae701b5fc378f3c84f8a0998".parse().unwrap(),
            "045cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc951435bf45daa69f5ce8729279e5ab2457ec2f47ec02184a5af7d9d6f78d9755".parse().unwrap(),
            "042f01e5e15cca351daff3843fb70f3c2f0a1bdd05e5af888a67784ef3e10a2a01a3b25758beac66b6d6c2f7d5ecd2ec4b3d1dec2945a489e84a25d3479342132b".parse().unwrap(),
        ];

        // This is legal for CHECKMULTISIG, but the 8 keys consume the whole 520 bytes
        // allowed by P2SH, meaning that the full script goes over the limit.
        let thresh = Threshold::new(2, pks).expect("the thresh is ok..");
        let res: Result<SortedMultiVec<PublicKey, Legacy>, ValidationError> =
            SortedMultiVec::new(thresh);
        let error = res.expect_err("constructor should err");

        match error {
            ValidationError::MaxScriptSizeExceeded { .. } => {} // ok
            other => panic!("unexpected error: {:?}", other),
        }
    }
}
