// SPDX-License-Identifier: CC0-1.0

//! # Segwit Output Descriptors
//!
//! Implementation of Segwit Descriptors. Contains the implementation
//! of wsh, wpkh and sortedmulti inside wsh.

use core::convert::TryFrom;
use core::fmt;

use bitcoin::{Address, Network, ScriptBuf, Weight};

use super::SortedMultiVec;
use crate::descriptor::{write_descriptor, DefiniteDescriptorKey};
use crate::miniscript::context::ScriptContext;
use crate::miniscript::limits::MAX_PUBKEYS_PER_MULTISIG;
use crate::miniscript::satisfy::{Placeholder, Satisfaction, Witness};
use crate::plan::AssetProvider;
use crate::policy::{semantic, Liftable};
use crate::prelude::*;
use crate::util::varint_len;
use crate::{
    expression, Error, ForEachKey, FromStrKey, Miniscript, MiniscriptKey, ParseMiniscriptError,
    Satisfier, Segwitv0, Threshold, ToPublicKey, TranslateErr, Translator, ValidationError,
    ValidationParams,
};
/// A Segwitv0 wsh descriptor
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Wsh<Pk: MiniscriptKey> {
    /// underlying miniscript
    inner: WshInner<Pk>,
}

impl<Pk: MiniscriptKey> Wsh<Pk> {
    /// Get the Inner
    pub fn into_inner(self) -> WshInner<Pk> { self.inner }

    /// Get a reference to inner
    pub fn as_inner(&self) -> &WshInner<Pk> { &self.inner }

    /// Create a new wsh descriptor
    pub fn new(mut ms: Miniscript<Pk, Segwitv0>) -> Result<Self, ValidationError> {
        ms.validate(&Segwitv0::SANE)?;
        Ok(Self { inner: WshInner::Ms(ms) })
    }

    /// Create a new sortedmulti wsh descriptor
    pub fn new_sortedmulti(
        thresh: Threshold<Pk, MAX_PUBKEYS_PER_MULTISIG>,
    ) -> Result<Self, ValidationError> {
        // The context checks will be carried out inside new function for
        // sortedMultiVec
        Ok(Self { inner: WshInner::SortedMulti(SortedMultiVec::new(thresh)?) })
    }

    /// Get the descriptor without the checksum
    #[deprecated(since = "8.0.0", note = "use format!(\"{:#}\") instead")]
    pub fn to_string_no_checksum(&self) -> String { format!("{:#}", self) }

    /// Computes an upper bound on the difference between a non-satisfied
    /// `TxIn`'s `segwit_weight` and a satisfied `TxIn`'s `segwit_weight`
    ///
    /// Assumes all ECDSA signatures are 73 bytes, including push opcode and
    /// sighash suffix.
    ///
    /// # Errors
    /// When the descriptor is impossible to safisfy (ex: sh(OP_FALSE)).
    pub fn max_weight_to_satisfy(&self) -> Result<Weight, crate::SatisfactionImpossibleError> {
        let (redeem_script_size, max_sat_elems, max_sat_size) = match self.inner {
            WshInner::SortedMulti(ref smv) => (
                smv.maximum_script_size(&Segwitv0::SANE),
                smv.max_satisfaction_witness_elements(),
                smv.max_satisfaction_size(),
            ),
            WshInner::Ms(ref ms) => (
                ms.maximum_script_size(&Segwitv0::SANE),
                ms.max_satisfaction_witness_elements()?,
                ms.max_satisfaction_size()?,
            ),
        };
        // stack size varint difference between non-satisfied (0) and satisfied
        // `max_sat_elems` is inclusive of the "witness script" (redeem script)
        let stack_varint_diff = varint_len(max_sat_elems) - varint_len(0);

        Ok(Weight::from_wu(
            (stack_varint_diff + varint_len(redeem_script_size) + redeem_script_size + max_sat_size)
                as u64,
        ))
    }

    /// Converts the keys in a script from one type to another.
    pub fn translate_pk<T>(&self, t: &mut T) -> Result<Wsh<T::TargetPk>, TranslateErr<T::Error>>
    where
        T: Translator<Pk>,
    {
        let inner = match self.inner {
            WshInner::SortedMulti(ref smv) => WshInner::SortedMulti(smv.translate_pk(t)?),
            WshInner::Ms(ref ms) => WshInner::Ms(ms.translate_pk(t)?),
        };
        Ok(Wsh { inner })
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Wsh<Pk> {
    /// Obtains the corresponding script pubkey for this descriptor.
    pub fn script_pubkey(&self) -> ScriptBuf { self.inner_script().to_p2wsh() }

    /// Obtains the corresponding script pubkey for this descriptor.
    pub fn address(&self, network: Network) -> Address {
        match self.inner {
            WshInner::SortedMulti(ref smv) => Address::p2wsh(&smv.encode(), network),
            WshInner::Ms(ref ms) => Address::p2wsh(&ms.encode(), network),
        }
    }

    /// Obtains the underlying miniscript for this descriptor.
    pub fn inner_script(&self) -> ScriptBuf {
        match self.inner {
            WshInner::SortedMulti(ref smv) => smv.encode(),
            WshInner::Ms(ref ms) => ms.encode(),
        }
    }

    /// Obtains the pre bip-340 signature script code for this descriptor.
    pub fn ecdsa_sighash_script_code(&self) -> ScriptBuf { self.inner_script() }

    /// Returns satisfying non-malleable witness and scriptSig with minimum
    /// weight to spend an output controlled by the given descriptor if it is
    /// possible to construct one using the `satisfier`.
    pub fn get_satisfaction<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        let mut witness = match self.inner {
            WshInner::SortedMulti(ref smv) => smv.satisfy(satisfier)?,
            WshInner::Ms(ref ms) => ms.satisfy(satisfier)?,
        };
        let witness_script = self.inner_script();
        witness.push(witness_script.into_bytes());
        let script_sig = ScriptBuf::new();
        Ok((witness, script_sig))
    }

    /// Returns satisfying, possibly malleable, witness and scriptSig with
    /// minimum weight to spend an output controlled by the given descriptor if
    /// it is possible to construct one using the `satisfier`.
    pub fn get_satisfaction_mall<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        let mut witness = match self.inner {
            WshInner::SortedMulti(ref smv) => smv.satisfy(satisfier)?,
            WshInner::Ms(ref ms) => ms.satisfy_malleable(satisfier)?,
        };
        witness.push(self.inner_script().into_bytes());
        let script_sig = ScriptBuf::new();
        Ok((witness, script_sig))
    }
}

impl Wsh<DefiniteDescriptorKey> {
    /// Returns a plan if the provided assets are sufficient to produce a non-malleable satisfaction
    pub fn plan_satisfaction<P>(
        &self,
        provider: &P,
    ) -> Satisfaction<Placeholder<DefiniteDescriptorKey>>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        match &self.inner {
            WshInner::SortedMulti(sm) => sm.build_template(provider),
            WshInner::Ms(ms) => ms.build_template(provider),
        }
    }

    /// Returns a plan if the provided assets are sufficient to produce a malleable satisfaction
    pub fn plan_satisfaction_mall<P>(
        &self,
        provider: &P,
    ) -> Satisfaction<Placeholder<DefiniteDescriptorKey>>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        match &self.inner {
            WshInner::SortedMulti(sm) => sm.build_template(provider),
            WshInner::Ms(ms) => ms.build_template_mall(provider),
        }
    }
}

/// Wsh Inner
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum WshInner<Pk: MiniscriptKey> {
    /// Sorted Multi
    SortedMulti(SortedMultiVec<Pk, Segwitv0>),
    /// Wsh Miniscript
    Ms(Miniscript<Pk, Segwitv0>),
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Wsh<Pk> {
    fn lift(&self) -> Result<semantic::Policy<Pk>, ValidationError> {
        match self.inner {
            WshInner::SortedMulti(ref smv) => smv.lift(),
            WshInner::Ms(ref ms) => ms.lift(),
        }
    }
}

impl<Pk: FromStrKey> Wsh<Pk> {
    /// Parse from an expression tree.
    pub fn from_tree(
        top: expression::TreeIterItem,
        params: &ValidationParams,
    ) -> Result<Self, ParseMiniscriptError> {
        let params = &Segwitv0::CONSENSUS.intersect(params);
        let top = top.verify_toplevel("wsh", 1..=1)?;

        if top.name() == "sortedmulti" {
            return Ok(Wsh {
                inner: WshInner::SortedMulti(SortedMultiVec::from_tree(top, params)?),
            });
        }
        let sub = Miniscript::from_tree(top, params)?;
        Ok(Wsh { inner: WshInner::Ms(sub) })
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Wsh<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            WshInner::SortedMulti(ref smv) => write!(f, "wsh({:?})", smv),
            WshInner::Ms(ref ms) => write!(f, "wsh({:?})", ms),
        }
    }
}

impl<Pk: MiniscriptKey> fmt::Display for Wsh<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            WshInner::SortedMulti(ref smv) => write_descriptor!(f, "wsh({})", smv),
            WshInner::Ms(ref ms) => write_descriptor!(f, "wsh({})", ms),
        }
    }
}

impl<Pk: FromStrKey> core::str::FromStr for Wsh<Pk> {
    type Err = ParseMiniscriptError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let top = expression::Tree::from_str(s)?;
        Self::from_tree(top.root(), &Segwitv0::SANE)
    }
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Wsh<Pk> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, pred: F) -> bool {
        match self.inner {
            WshInner::SortedMulti(ref smv) => smv.for_each_key(pred),
            WshInner::Ms(ref ms) => ms.for_each_key(pred),
        }
    }
}

/// A bare Wpkh descriptor at top level
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Wpkh<Pk: MiniscriptKey> {
    /// underlying publickey
    pk: Pk,
}

impl<Pk: MiniscriptKey> Wpkh<Pk> {
    /// Create a new Wpkh descriptor
    pub fn new(pk: Pk) -> Result<Self, ValidationError> {
        Segwitv0::SANE
            .validate_pk(&pk)
            .map_err(ValidationError::Key)?;
        Ok(Wpkh { pk })
    }

    /// Get the inner key
    pub fn into_inner(self) -> Pk { self.pk }

    /// Get the inner key
    pub fn as_inner(&self) -> &Pk { &self.pk }

    /// Get the descriptor without the checksum
    #[deprecated(since = "8.0.0", note = "use format!(\"{:#}\") instead")]
    pub fn to_string_no_checksum(&self) -> String { format!("{:#}", self) }

    /// Computes an upper bound on the difference between a non-satisfied
    /// `TxIn`'s `segwit_weight` and a satisfied `TxIn`'s `segwit_weight`
    ///
    /// Assumes all ec-signatures are 73 bytes, including push opcode and
    /// sighash suffix.
    pub fn max_weight_to_satisfy(&self) -> Weight {
        // stack items: <varint(sig+sigHash)> <sig(71)+sigHash(1)> <varint(pubkey)> <pubkey>
        let stack_items_size = 73 + self.pk.full_encoded_length();
        // stackLen varint difference between non-satisfied (0) and satisfied
        let stack_varint_diff = varint_len(2) - varint_len(0);
        Weight::from_wu((stack_varint_diff + stack_items_size) as u64)
    }

    /// Converts the keys in a script from one type to another.
    pub fn translate_pk<T>(&self, t: &mut T) -> Result<Wpkh<T::TargetPk>, TranslateErr<T::Error>>
    where
        T: Translator<Pk>,
    {
        // In theory we should be caching the original validation parameters here
        // rather than calling `Wpkh::new` and re-validating with Segwitv0::SANE.
        // In practice it doesn't matter because the only validation rule that
        // applies is "no uncompressed keys" which is a consensus rule and enforced
        // by our constructors no matter what the user tries to specify.
        let res = Wpkh::new(t.pk(&self.pk)?);
        match res {
            Ok(pk) => Ok(pk),
            Err(e) => Err(TranslateErr::OuterError(e)),
        }
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Wpkh<Pk> {
    /// Obtains the corresponding script pubkey for this descriptor.
    pub fn script_pubkey(&self) -> ScriptBuf {
        let pk = self.pk.to_public_key();
        let compressed = bitcoin::key::CompressedPublicKey::try_from(pk)
            .expect("wpkh descriptors have compressed keys");

        let addr = Address::p2wpkh(&compressed, Network::Bitcoin);
        addr.script_pubkey()
    }

    /// Obtains the corresponding script pubkey for this descriptor.
    pub fn address(&self, network: Network) -> Address {
        let pk = self.pk.to_public_key();
        let compressed = bitcoin::key::CompressedPublicKey::try_from(pk)
            .expect("Rust Miniscript types don't allow uncompressed pks in segwit descriptors");

        Address::p2wpkh(&compressed, network)
    }

    /// Obtains the underlying miniscript for this descriptor.
    pub fn inner_script(&self) -> ScriptBuf { self.script_pubkey() }

    /// Obtains the pre bip-340 signature script code for this descriptor.
    pub fn ecdsa_sighash_script_code(&self) -> ScriptBuf {
        // For SegWit outputs, it is defined by bip-0143 (quoted below) and is different from
        // the previous txo's scriptPubKey.
        // The item 5:
        //     - For P2WPKH witness program, the scriptCode is `0x1976a914{20-byte-pubkey-hash}88ac`.
        let addr = Address::p2pkh(self.pk.to_public_key(), Network::Bitcoin);
        addr.script_pubkey()
    }

    /// Returns satisfying non-malleable witness and scriptSig with minimum
    /// weight to spend an output controlled by the given descriptor if it is
    /// possible to construct one using the `satisfier`.
    pub fn get_satisfaction<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        if let Some(sig) = satisfier.lookup_ecdsa_sig(&self.pk) {
            let sig_vec = sig.to_vec();
            let script_sig = ScriptBuf::new();
            let witness = vec![sig_vec, self.pk.to_public_key().to_bytes()];
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

impl Wpkh<DefiniteDescriptorKey> {
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
                Placeholder::Pubkey(self.pk.clone(), self.pk.full_encoded_length()),
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

impl<Pk: MiniscriptKey> fmt::Debug for Wpkh<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "wpkh({:?})", self.pk) }
}

impl<Pk: MiniscriptKey> fmt::Display for Wpkh<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write_descriptor!(f, "wpkh({})", self.pk)
    }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Wpkh<Pk> {
    fn lift(&self) -> Result<semantic::Policy<Pk>, ValidationError> {
        Ok(semantic::Policy::Key(self.pk.clone()))
    }
}

impl<Pk: FromStrKey> Wpkh<Pk> {
    /// Parse from an expression tree.
    pub fn from_tree(
        top: expression::TreeIterItem,
        params: &ValidationParams,
    ) -> Result<Self, ParseMiniscriptError> {
        let pk = top.verify_terminal_parent("wpkh", "public key")?;
        Segwitv0::CONSENSUS
            .intersect(params)
            .validate_pk(&pk)
            .map_err(ValidationError::Key)?;
        Ok(Wpkh { pk })
    }
}

impl<Pk: FromStrKey> core::str::FromStr for Wpkh<Pk> {
    type Err = ParseMiniscriptError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let top = expression::Tree::from_str(s)?;
        Self::from_tree(top.root(), &Segwitv0::SANE)
    }
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Wpkh<Pk> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, mut pred: F) -> bool { pred(&self.pk) }
}
