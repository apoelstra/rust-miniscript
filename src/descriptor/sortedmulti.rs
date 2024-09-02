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
    expression, policy, script_num_size, Error, ForEachKey, Miniscript, MiniscriptKey, Satisfier,
    Threshold, ToPublicKey, TranslateErr, Translator,
};

/// Contents of a "sortedmulti" descriptor
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SortedMultiVec<Pk: MiniscriptKey, Ctx: ScriptContext> {
    inner: Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>,
    /// The current ScriptContext for sortedmulti
    phantom: PhantomData<Ctx>,
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> SortedMultiVec<Pk, Ctx> {
    fn constructor_check(mut self) -> Result<Self, Error> {
        // Check the limits before creating a new SortedMultiVec
        // For example, under p2sh context the scriptlen can only be
        // upto 520 bytes.
        let term: Terminal<Pk, Ctx> = Terminal::Multi(self.inner);
        let ms = Miniscript::from_ast(term)?;
        // This would check all the consensus rules for p2sh/p2wsh and
        // even tapscript in future
        Ctx::check_local_validity(&ms)?;
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
    pub fn new(k: usize, pks: Vec<Pk>) -> Result<Self, Error> {
        let ret =
            Self { inner: Threshold::new(k, pks).map_err(Error::Threshold)?, phantom: PhantomData };
        ret.constructor_check()
    }

    /// Parse an expression tree into a SortedMultiVec
    pub fn from_tree(tree: expression::TreeIterItem) -> Result<Self, Error>
    where
        Pk: FromStrKey,
    {
        tree.verify_toplevel("sortedmulti", 1..)
            .map_err(From::from)
            .map_err(Error::Parse)?;

        let ret = Self {
            inner: tree
                .verify_threshold(|sub| sub.verify_terminal("public_key").map_err(Error::Parse))?,
            phantom: PhantomData,
        };
        ret.constructor_check()
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
            phantom: PhantomData,
        };
        ret.constructor_check().map_err(TranslateErr::OuterError)
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
    /// utility function to sanity a sorted multi vec
    pub fn sanity_check(&self) -> Result<(), Error> {
        let ms: Miniscript<Pk, Ctx> =
            Miniscript::from_ast(Terminal::Multi(self.inner.clone())).expect("Must typecheck");
        ms.sanity_check().map_err(From::from)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> SortedMultiVec<Pk, Ctx> {
    /// Create Terminal::Multi containing sorted pubkeys
    pub fn sorted_node(&self) -> Terminal<Pk, Ctx>
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
        Terminal::Multi(thresh)
    }

    /// Encode as a Bitcoin script
    pub fn encode(&self) -> script::ScriptBuf
    where
        Pk: ToPublicKey,
    {
        self.sorted_node()
            .encode(script::Builder::new())
            .into_script()
    }

    /// Attempt to produce a satisfying witness for the
    /// witness script represented by the parse tree
    pub fn satisfy<S>(&self, satisfier: S) -> Result<Vec<Vec<u8>>, Error>
    where
        Pk: ToPublicKey,
        S: Satisfier<Pk>,
    {
        let ms = Miniscript::from_ast(self.sorted_node()).expect("Multi node typecheck");
        ms.satisfy(satisfier)
    }

    /// Attempt to produce a witness template given the assets available
    pub fn build_template<P>(&self, provider: &P) -> Satisfaction<Placeholder<Pk>>
    where
        Pk: ToPublicKey,
        P: AssetProvider<Pk>,
    {
        let ms = Miniscript::from_ast(self.sorted_node()).expect("Multi node typecheck");
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
    fn lift(&self) -> Result<policy::semantic::Policy<Pk>, Error> {
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
    use core::str::FromStr as _;

    use bitcoin::secp256k1::PublicKey;

    use super::*;
    use crate::miniscript::context::Legacy;

    #[test]
    fn too_many_pubkeys() {
        // Arbitrary pubic key.
        let pk = PublicKey::from_str(
            "02e6642fd69bd211f93f7f1f36ca51a26a5290eb2dd1b0d8279a87bb0d480c8443",
        )
        .unwrap();

        let over = 1 + MAX_PUBKEYS_PER_MULTISIG;

        let mut pks = Vec::new();
        for _ in 0..over {
            pks.push(pk);
        }

        let res: Result<SortedMultiVec<PublicKey, Legacy>, Error> = SortedMultiVec::new(0, pks);
        let error = res.expect_err("constructor should err");

        match error {
            Error::Threshold(_) => {} // ok
            other => panic!("unexpected error: {:?}", other),
        }
    }
}
