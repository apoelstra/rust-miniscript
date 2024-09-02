// SPDX-License-Identifier: CC0-1.0

//! # Bare Output Descriptors
//!
//! Implementation of Bare Descriptors (i.e descriptors that are)
//! wrapped inside wsh, or sh fragments.
//! Also includes pk, and pkh descriptors
//!

use core::fmt;

use bitcoin::script::{self, PushBytes};
use bitcoin::{Address, Network, ScriptBuf, Weight};

use crate::descriptor::{write_descriptor, DefiniteDescriptorKey};
use crate::expression::{self, FromTree};
use crate::miniscript::context::{ScriptContext, ScriptContextError};
use crate::miniscript::satisfy::{Placeholder, Satisfaction, Witness};
use crate::plan::AssetProvider;
use crate::policy::{semantic, Liftable};
use crate::prelude::*;
use crate::util::{varint_len, witness_to_scriptsig};
use crate::{
    BareCtx, Error, ForEachKey, FromStrKey, Miniscript, MiniscriptKey, Satisfier, ToPublicKey,
    TranslateErr, Translator,
};

/// Create a Bare Descriptor. That is descriptor that is
/// not wrapped in sh or wsh. This covers the Pk descriptor
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Bare<Pk: MiniscriptKey> {
    /// underlying miniscript
    ms: Miniscript<Pk, BareCtx>,
}

impl<Pk: MiniscriptKey> Bare<Pk> {
    /// Create a new raw descriptor
    pub fn new(ms: Miniscript<Pk, BareCtx>) -> Result<Self, Error> {
        // do the top-level checks
        BareCtx::top_level_checks(&ms)?;
        Ok(Self { ms })
    }

    /// get the inner
    pub fn into_inner(self) -> Miniscript<Pk, BareCtx> { self.ms }

    /// get the inner
    pub fn as_inner(&self) -> &Miniscript<Pk, BareCtx> { &self.ms }

    /// Checks whether the descriptor is safe.
    pub fn sanity_check(&self) -> Result<(), Error> {
        self.ms.sanity_check()?;
        Ok(())
    }

    /// Computes an upper bound on the difference between a non-satisfied
    /// `TxIn`'s `segwit_weight` and a satisfied `TxIn`'s `segwit_weight`
    ///
    /// Since this method uses `segwit_weight` instead of `legacy_weight`,
    /// if you want to include only legacy inputs in your transaction,
    /// you should remove 1WU from each input's `max_weight_to_satisfy`
    /// for a more accurate estimate.
    ///
    /// Assumes all ECDSA signatures are 73 bytes, including push opcode and
    /// sighash suffix.
    ///
    /// # Errors
    /// When the descriptor is impossible to safisfy (ex: sh(OP_FALSE)).
    pub fn max_weight_to_satisfy(&self) -> Result<Weight, Error> {
        let scriptsig_size = self.ms.max_satisfaction_size()?;
        // scriptSig varint difference between non-satisfied (0) and satisfied
        let scriptsig_varint_diff = varint_len(scriptsig_size) - varint_len(0);
        Weight::from_vb((scriptsig_varint_diff + scriptsig_size) as u64)
            .ok_or(Error::CouldNotSatisfy)
    }

    /// Computes an upper bound on the weight of a satisfying witness to the
    /// transaction.
    ///
    /// Assumes all ec-signatures are 73 bytes, including push opcode and
    /// sighash suffix. Includes the weight of the VarInts encoding the
    /// scriptSig and witness stack length.
    ///
    /// # Errors
    /// When the descriptor is impossible to safisfy (ex: sh(OP_FALSE)).
    #[deprecated(
        since = "10.0.0",
        note = "Use max_weight_to_satisfy instead. The method to count bytes was redesigned and the results will differ from max_weight_to_satisfy. For more details check rust-bitcoin/rust-miniscript#476."
    )]
    pub fn max_satisfaction_weight(&self) -> Result<usize, Error> {
        let scriptsig_len = self.ms.max_satisfaction_size()?;
        Ok(4 * (varint_len(scriptsig_len) + scriptsig_len))
    }

    /// Converts the keys in the script from one type to another.
    pub fn translate_pk<T>(&self, t: &mut T) -> Result<Bare<T::TargetPk>, TranslateErr<T::Error>>
    where
        T: Translator<Pk>,
    {
        Bare::new(self.ms.translate_pk(t)?).map_err(TranslateErr::OuterError)
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Bare<Pk> {
    /// Obtains the corresponding script pubkey for this descriptor.
    pub fn script_pubkey(&self) -> ScriptBuf { self.ms.encode() }

    /// Obtains the underlying miniscript for this descriptor.
    pub fn inner_script(&self) -> ScriptBuf { self.script_pubkey() }

    /// Obtains the pre bip-340 signature script code for this descriptor.
    pub fn ecdsa_sighash_script_code(&self) -> ScriptBuf { self.script_pubkey() }

    /// Returns satisfying non-malleable witness and scriptSig with minimum
    /// weight to spend an output controlled by the given descriptor if it is
    /// possible to construct one using the `satisfier`.
    pub fn get_satisfaction<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        let ms = self.ms.satisfy(satisfier)?;
        let script_sig = witness_to_scriptsig(&ms);
        let witness = vec![];
        Ok((witness, script_sig))
    }

    /// Returns satisfying, possibly malleable, witness and scriptSig with
    /// minimum weight to spend an output controlled by the given descriptor if
    /// it is possible to construct one using the `satisfier`.
    pub fn get_satisfaction_mall<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        let ms = self.ms.satisfy_malleable(satisfier)?;
        let script_sig = witness_to_scriptsig(&ms);
        let witness = vec![];
        Ok((witness, script_sig))
    }
}

impl Bare<DefiniteDescriptorKey> {
    /// Returns a plan if the provided assets are sufficient to produce a non-malleable satisfaction
    pub fn plan_satisfaction<P>(
        &self,
        provider: &P,
    ) -> Satisfaction<Placeholder<DefiniteDescriptorKey>>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        self.ms.build_template(provider)
    }

    /// Returns a plan if the provided assets are sufficient to produce a malleable satisfaction
    pub fn plan_satisfaction_mall<P>(
        &self,
        provider: &P,
    ) -> Satisfaction<Placeholder<DefiniteDescriptorKey>>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        self.ms.build_template_mall(provider)
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Bare<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{:?}", self.ms) }
}

impl<Pk: MiniscriptKey> fmt::Display for Bare<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write_descriptor!(f, "{}", self.ms) }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Bare<Pk> {
    fn lift(&self) -> Result<semantic::Policy<Pk>, Error> { self.ms.lift() }
}

impl<Pk: FromStrKey> FromTree for Bare<Pk> {
    fn from_tree(root: expression::TreeIterItem) -> Result<Self, Error> {
        let sub = Miniscript::<Pk, BareCtx>::from_tree(root)?;
        BareCtx::top_level_checks(&sub)?;
        Bare::new(sub)
    }
}

impl<Pk: FromStrKey> core::str::FromStr for Bare<Pk> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let top = expression::Tree::from_str(s)?;
        Self::from_tree(top.root())
    }
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Bare<Pk> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, pred: F) -> bool {
        self.ms.for_each_key(pred)
    }
}

/// A bare PkH descriptor at top level
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Pkh<Pk: MiniscriptKey> {
    /// underlying publickey
    pk: Pk,
}

impl<Pk: MiniscriptKey> Pkh<Pk> {
    /// Create a new Pkh descriptor
    pub fn new(pk: Pk) -> Result<Self, ScriptContextError> {
        // do the top-level checks
        match BareCtx::check_pk(&pk) {
            Ok(()) => Ok(Pkh { pk }),
            Err(e) => Err(e),
        }
    }

    /// Get a reference to the inner key
    pub fn as_inner(&self) -> &Pk { &self.pk }

    /// Get the inner key
    pub fn into_inner(self) -> Pk { self.pk }

    /// Computes an upper bound on the difference between a non-satisfied
    /// `TxIn`'s `segwit_weight` and a satisfied `TxIn`'s `segwit_weight`
    ///
    /// Since this method uses `segwit_weight` instead of `legacy_weight`,
    /// if you want to include only legacy inputs in your transaction,
    /// you should remove 1WU from each input's `max_weight_to_satisfy`
    /// for a more accurate estimate.
    ///
    /// Assumes all ECDSA signatures are 73 bytes, including push opcode and
    /// sighash suffix.
    ///
    /// # Errors
    /// When the descriptor is impossible to safisfy (ex: sh(OP_FALSE)).
    pub fn max_weight_to_satisfy(&self) -> Weight {
        // OP_72 + <sig(71)+sigHash(1)> + OP_33 + <pubkey>
        let scriptsig_size = 73 + BareCtx::pk_len(&self.pk);
        // scriptSig varint different between non-satisfied (0) and satisfied
        let scriptsig_varint_diff = varint_len(scriptsig_size) - varint_len(0);
        Weight::from_vb((scriptsig_varint_diff + scriptsig_size) as u64).unwrap()
    }

    /// Computes an upper bound on the weight of a satisfying witness to the
    /// transaction.
    ///
    /// Assumes all ec-signatures are 73 bytes, including push opcode and
    /// sighash suffix. Includes the weight of the VarInts encoding the
    /// scriptSig and witness stack length.
    #[deprecated(
        since = "10.0.0",
        note = "Use max_weight_to_satisfy instead. The method to count bytes was redesigned and the results will differ from max_weight_to_satisfy. For more details check rust-bitcoin/rust-miniscript#476."
    )]
    pub fn max_satisfaction_weight(&self) -> usize { 4 * (1 + 73 + BareCtx::pk_len(&self.pk)) }

    /// Converts the keys in a script from one type to another.
    pub fn translate_pk<T>(&self, t: &mut T) -> Result<Pkh<T::TargetPk>, TranslateErr<T::Error>>
    where
        T: Translator<Pk>,
    {
        let res = Pkh::new(t.pk(&self.pk)?);
        match res {
            Ok(pk) => Ok(pk),
            Err(e) => Err(TranslateErr::OuterError(Error::from(e))),
        }
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Pkh<Pk> {
    /// Obtains the corresponding script pubkey for this descriptor.
    pub fn script_pubkey(&self) -> ScriptBuf {
        // Fine to hard code the `Network` here because we immediately call
        // `script_pubkey` which does not use the `network` field of `Address`.
        let addr = self.address(Network::Bitcoin);
        addr.script_pubkey()
    }

    /// Obtains the corresponding script pubkey for this descriptor.
    pub fn address(&self, network: Network) -> Address {
        Address::p2pkh(self.pk.to_public_key(), network)
    }

    /// Obtains the underlying miniscript for this descriptor.
    pub fn inner_script(&self) -> ScriptBuf { self.script_pubkey() }

    /// Obtains the pre bip-340 signature script code for this descriptor.
    pub fn ecdsa_sighash_script_code(&self) -> ScriptBuf { self.script_pubkey() }

    /// Returns satisfying non-malleable witness and scriptSig with minimum
    /// weight to spend an output controlled by the given descriptor if it is
    /// possible to construct one using the `satisfier`.
    pub fn get_satisfaction<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        if let Some(sig) = satisfier.lookup_ecdsa_sig(&self.pk) {
            let script_sig = script::Builder::new()
                .push_slice::<&PushBytes>(
                    // serialize() does not allocate here
                    sig.serialize().as_ref(),
                )
                .push_key(&self.pk.to_public_key())
                .into_script();
            let witness = vec![];
            Ok((witness, script_sig))
        } else {
            Err(Error::MissingSig(self.pk.to_public_key()))
        }
    }

    /// Returns satisfying, possibly malleable, witness and scriptSig with
    /// minimum weight to spend an output controlled by the given descriptor if
    /// it is possible to construct one using the `satisfier`.
    pub fn get_satisfaction_mall<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        self.get_satisfaction(satisfier)
    }
}

impl Pkh<DefiniteDescriptorKey> {
    /// Returns a plan if the provided assets are sufficient to produce a non-malleable satisfaction
    pub fn plan_satisfaction<P>(
        &self,
        provider: &P,
    ) -> Satisfaction<Placeholder<DefiniteDescriptorKey>>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        let stack = if provider.provider_lookup_ecdsa_sig(&self.pk) {
            let stack = vec![
                Placeholder::EcdsaSigPk(self.pk.clone()),
                Placeholder::Pubkey(self.pk.clone(), BareCtx::pk_len(&self.pk)),
            ];
            Witness::Stack(stack)
        } else {
            Witness::Unavailable
        };

        Satisfaction { stack, has_sig: true, relative_timelock: None, absolute_timelock: None }
    }

    /// Returns a plan if the provided assets are sufficient to produce a malleable satisfaction
    pub fn plan_satisfaction_mall<P>(
        &self,
        provider: &P,
    ) -> Satisfaction<Placeholder<DefiniteDescriptorKey>>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        self.plan_satisfaction(provider)
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Pkh<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "pkh({:?})", self.pk) }
}

impl<Pk: MiniscriptKey> fmt::Display for Pkh<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write_descriptor!(f, "pkh({})", self.pk)
    }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Pkh<Pk> {
    fn lift(&self) -> Result<semantic::Policy<Pk>, Error> {
        Ok(semantic::Policy::Key(self.pk.clone()))
    }
}

impl<Pk: FromStrKey> FromTree for Pkh<Pk> {
    fn from_tree(root: expression::TreeIterItem) -> Result<Self, Error> {
        let pk = root
            .verify_terminal_parent("pkh", "public key")
            .map_err(Error::Parse)?;
        Pkh::new(pk).map_err(Error::ContextError)
    }
}

impl<Pk: FromStrKey> core::str::FromStr for Pkh<Pk> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let top = expression::Tree::from_str(s)?;
        Self::from_tree(top.root())
    }
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Pkh<Pk> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, mut pred: F) -> bool { pred(&self.pk) }
}
