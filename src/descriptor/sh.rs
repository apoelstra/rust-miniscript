// SPDX-License-Identifier: CC0-1.0

//! # P2SH Descriptors
//!
//! Implementation of p2sh descriptors. Contains the implementation
//! of sh, wrapped fragments for sh which include wsh, sortedmulti
//! sh(miniscript), and sh(wpkh)
//!

use core::convert::TryFrom;
use core::fmt;

use bitcoin::script::PushBytes;
use bitcoin::{script, Address, Network, ScriptBuf, Weight};

use super::{SortedMultiVec, Wpkh, Wsh};
use crate::descriptor::{write_descriptor, DefiniteDescriptorKey};
use crate::expression::{self, FromTree};
use crate::miniscript::context::ScriptContext;
use crate::miniscript::satisfy::{Placeholder, Satisfaction};
use crate::plan::AssetProvider;
use crate::policy::{semantic, Liftable};
use crate::prelude::*;
use crate::util::{varint_len, witness_to_scriptsig};
use crate::{
    push_opcode_size, Error, ForEachKey, FromStrKey, Legacy, Miniscript, MiniscriptKey, Satisfier,
    Segwitv0, ToPublicKey, TranslateErr, Translator,
};

/// A Legacy p2sh Descriptor
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Sh<Pk: MiniscriptKey> {
    /// underlying miniscript
    inner: ShInner<Pk>,
}

/// Sh Inner
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum ShInner<Pk: MiniscriptKey> {
    /// Nested Wsh
    Wsh(Wsh<Pk>),
    /// Nested Wpkh
    Wpkh(Wpkh<Pk>),
    /// Inner Sorted Multi
    SortedMulti(SortedMultiVec<Pk, Legacy>),
    /// p2sh miniscript
    Ms(Miniscript<Pk, Legacy>),
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Sh<Pk> {
    fn lift(&self) -> Result<semantic::Policy<Pk>, Error> {
        match self.inner {
            ShInner::Wsh(ref wsh) => wsh.lift(),
            ShInner::Wpkh(ref pk) => Ok(semantic::Policy::Key(pk.as_inner().clone())),
            ShInner::SortedMulti(ref smv) => smv.lift(),
            ShInner::Ms(ref ms) => ms.lift(),
        }
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Sh<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            ShInner::Wsh(ref wsh_inner) => write!(f, "sh({:?})", wsh_inner),
            ShInner::Wpkh(ref pk) => write!(f, "sh({:?})", pk),
            ShInner::SortedMulti(ref smv) => write!(f, "sh({:?})", smv),
            ShInner::Ms(ref ms) => write!(f, "sh({:?})", ms),
        }
    }
}

impl<Pk: MiniscriptKey> fmt::Display for Sh<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            ShInner::Wsh(ref wsh) => write_descriptor!(f, "sh({:#})", wsh),
            ShInner::Wpkh(ref pk) => write_descriptor!(f, "sh({:#})", pk),
            ShInner::SortedMulti(ref smv) => write_descriptor!(f, "sh({})", smv),
            ShInner::Ms(ref ms) => write_descriptor!(f, "sh({})", ms),
        }
    }
}

impl<Pk: FromStrKey> crate::expression::FromTree for Sh<Pk> {
    fn from_tree(top: expression::TreeIterItem) -> Result<Self, Error> {
        let top = top
            .verify_toplevel("sh", 1..=1)
            .map_err(From::from)
            .map_err(Error::Parse)?;

        let inner = match top.name() {
            "wsh" => ShInner::Wsh(Wsh::from_tree(top)?),
            "wpkh" => ShInner::Wpkh(Wpkh::from_tree(top)?),
            "sortedmulti" => ShInner::SortedMulti(SortedMultiVec::from_tree(top)?),
            _ => {
                let sub = Miniscript::from_tree(top)?;
                Legacy::top_level_checks(&sub)?;
                ShInner::Ms(sub)
            }
        };
        Ok(Sh { inner })
    }
}

impl<Pk: FromStrKey> core::str::FromStr for Sh<Pk> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let top = expression::Tree::from_str(s)?;
        Self::from_tree(top.root())
    }
}

impl<Pk: MiniscriptKey> Sh<Pk> {
    /// Get the Inner
    pub fn into_inner(self) -> ShInner<Pk> { self.inner }

    /// Get a reference to inner
    pub fn as_inner(&self) -> &ShInner<Pk> { &self.inner }

    /// Create a new p2sh descriptor with the raw miniscript
    pub fn new(ms: Miniscript<Pk, Legacy>) -> Result<Self, Error> {
        // do the top-level checks
        Legacy::top_level_checks(&ms)?;
        Ok(Self { inner: ShInner::Ms(ms) })
    }

    /// Create a new p2sh sortedmulti descriptor with threshold `k`
    /// and Vec of `pks`.
    pub fn new_sortedmulti(k: usize, pks: Vec<Pk>) -> Result<Self, Error> {
        // The context checks will be carried out inside new function for
        // sortedMultiVec
        Ok(Self { inner: ShInner::SortedMulti(SortedMultiVec::new(k, pks)?) })
    }

    /// Create a new p2sh wrapped wsh descriptor with the raw miniscript
    pub fn new_wsh(ms: Miniscript<Pk, Segwitv0>) -> Result<Self, Error> {
        Ok(Self { inner: ShInner::Wsh(Wsh::new(ms)?) })
    }

    /// Create a new p2sh wrapper for the given wsh descriptor
    pub fn new_with_wsh(wsh: Wsh<Pk>) -> Self { Self { inner: ShInner::Wsh(wsh) } }

    /// Checks whether the descriptor is safe.
    pub fn sanity_check(&self) -> Result<(), Error> {
        match self.inner {
            ShInner::Wsh(ref wsh) => wsh.sanity_check()?,
            ShInner::Wpkh(ref wpkh) => wpkh.sanity_check()?,
            ShInner::SortedMulti(ref smv) => smv.sanity_check()?,
            ShInner::Ms(ref ms) => ms.sanity_check()?,
        }
        Ok(())
    }

    /// Create a new p2sh wrapped wsh sortedmulti descriptor from threshold
    /// `k` and Vec of `pks`
    pub fn new_wsh_sortedmulti(k: usize, pks: Vec<Pk>) -> Result<Self, Error> {
        // The context checks will be carried out inside new function for
        // sortedMultiVec
        Ok(Self { inner: ShInner::Wsh(Wsh::new_sortedmulti(k, pks)?) })
    }

    /// Create a new p2sh wrapped wpkh from `Pk`
    pub fn new_wpkh(pk: Pk) -> Result<Self, Error> {
        Ok(Self { inner: ShInner::Wpkh(Wpkh::new(pk)?) })
    }

    /// Create a new p2sh wrapper for the given wpkh descriptor
    pub fn new_with_wpkh(wpkh: Wpkh<Pk>) -> Self { Self { inner: ShInner::Wpkh(wpkh) } }

    /// Computes an upper bound on the difference between a non-satisfied
    /// `TxIn`'s `segwit_weight` and a satisfied `TxIn`'s `segwit_weight`
    ///
    /// Since this method uses `segwit_weight` instead of `legacy_weight`,
    /// if you want to include only legacy inputs in your transaction,
    /// you should remove 1WU from each input's `max_weight_to_satisfy`
    /// for a more accurate estimate.
    ///
    /// Assumes all ec-signatures are 73 bytes, including push opcode and
    /// sighash suffix.
    ///
    /// # Errors
    /// When the descriptor is impossible to safisfy (ex: sh(OP_FALSE)).
    pub fn max_weight_to_satisfy(&self) -> Result<Weight, Error> {
        let (scriptsig_size, witness_size) = match self.inner {
            // add weighted script sig, len byte stays the same
            ShInner::Wsh(ref wsh) => {
                // scriptSig: OP_34 <OP_0 OP_32 <32-byte-hash>>
                let scriptsig_size = 1 + 1 + 1 + 32;
                let witness_size = wsh.max_weight_to_satisfy()?;
                (scriptsig_size, witness_size)
            }
            ShInner::SortedMulti(ref smv) => {
                let ss = smv.script_size();
                let ps = push_opcode_size(ss);
                let scriptsig_size = ps + ss + smv.max_satisfaction_size();
                (scriptsig_size, Weight::ZERO)
            }
            // add weighted script sig, len byte stays the same
            ShInner::Wpkh(ref wpkh) => {
                // scriptSig: OP_22 <OP_0 OP_20 <20-byte-hash>>
                let scriptsig_size = 1 + 1 + 1 + 20;
                let witness_size = wpkh.max_weight_to_satisfy();
                (scriptsig_size, witness_size)
            }
            ShInner::Ms(ref ms) => {
                let ss = ms.script_size();
                let ps = push_opcode_size(ss);
                let scriptsig_size = ps + ss + ms.max_satisfaction_size()?;
                (scriptsig_size, Weight::ZERO)
            }
        };

        // scriptSigLen varint difference between non-satisfied (0) and satisfied
        let scriptsig_varint_diff = varint_len(scriptsig_size) - varint_len(0);

        let wu = Weight::from_vb((scriptsig_varint_diff + scriptsig_size) as u64);
        match wu {
            Some(w) => Ok(w + witness_size),
            None => Err(Error::CouldNotSatisfy),
        }
    }

    /// Computes an upper bound on the weight of a satisfying witness to the
    /// transaction.
    ///
    /// Assumes all ECDSA signatures are 73 bytes, including push opcode and
    /// sighash suffix. Includes the weight of the VarInts encoding the
    /// scriptSig and witness stack length.
    ///
    /// # Errors
    /// When the descriptor is impossible to safisfy (ex: sh(OP_FALSE)).
    #[deprecated(
        since = "10.0.0",
        note = "Use max_weight_to_satisfy instead. The method to count bytes was redesigned and the results will differ from max_weight_to_satisfy. For more details check rust-bitcoin/rust-miniscript#476."
    )]
    #[allow(deprecated)]
    pub fn max_satisfaction_weight(&self) -> Result<usize, Error> {
        Ok(match self.inner {
            // add weighted script sig, len byte stays the same
            ShInner::Wsh(ref wsh) => 4 * 35 + wsh.max_satisfaction_weight()?,
            ShInner::SortedMulti(ref smv) => {
                let ss = smv.script_size();
                let ps = push_opcode_size(ss);
                let scriptsig_len = ps + ss + smv.max_satisfaction_size();
                4 * (varint_len(scriptsig_len) + scriptsig_len)
            }
            // add weighted script sig, len byte stays the same
            ShInner::Wpkh(ref wpkh) => 4 * 23 + wpkh.max_satisfaction_weight(),
            ShInner::Ms(ref ms) => {
                let ss = ms.script_size();
                let ps = push_opcode_size(ss);
                let scriptsig_len = ps + ss + ms.max_satisfaction_size()?;
                4 * (varint_len(scriptsig_len) + scriptsig_len)
            }
        })
    }

    /// Converts the keys in a script from one type to another.
    pub fn translate_pk<T>(&self, t: &mut T) -> Result<Sh<T::TargetPk>, TranslateErr<T::Error>>
    where
        T: Translator<Pk>,
    {
        let inner = match self.inner {
            ShInner::Wsh(ref wsh) => ShInner::Wsh(wsh.translate_pk(t)?),
            ShInner::Wpkh(ref wpkh) => ShInner::Wpkh(wpkh.translate_pk(t)?),
            ShInner::SortedMulti(ref smv) => ShInner::SortedMulti(smv.translate_pk(t)?),
            ShInner::Ms(ref ms) => ShInner::Ms(ms.translate_pk(t)?),
        };
        Ok(Sh { inner })
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Sh<Pk> {
    /// Obtains the corresponding script pubkey for this descriptor.
    pub fn script_pubkey(&self) -> ScriptBuf {
        match self.inner {
            ShInner::Wsh(ref wsh) => wsh.script_pubkey().to_p2sh(),
            ShInner::Wpkh(ref wpkh) => wpkh.script_pubkey().to_p2sh(),
            ShInner::SortedMulti(ref smv) => smv.encode().to_p2sh(),
            ShInner::Ms(ref ms) => ms.encode().to_p2sh(),
        }
    }

    /// Obtains the corresponding address for this descriptor.
    pub fn address(&self, network: Network) -> Address {
        let addr = self.address_fallible(network);

        // Size is checked in `check_global_consensus_validity`.
        assert!(addr.is_ok());
        addr.expect("only fails if size > MAX_SCRIPT_ELEMENT_SIZE")
    }

    fn address_fallible(&self, network: Network) -> Result<Address, Error> {
        let script = match self.inner {
            ShInner::Wsh(ref wsh) => wsh.script_pubkey(),
            ShInner::Wpkh(ref wpkh) => wpkh.script_pubkey(),
            ShInner::SortedMulti(ref smv) => smv.encode(),
            ShInner::Ms(ref ms) => ms.encode(),
        };
        let address = Address::p2sh(&script, network)?;

        Ok(address)
    }

    /// Obtain the underlying miniscript for this descriptor
    pub fn inner_script(&self) -> ScriptBuf {
        match self.inner {
            ShInner::Wsh(ref wsh) => wsh.inner_script(),
            ShInner::Wpkh(ref wpkh) => wpkh.script_pubkey(),
            ShInner::SortedMulti(ref smv) => smv.encode(),
            ShInner::Ms(ref ms) => ms.encode(),
        }
    }

    /// Obtains the pre bip-340 signature script code for this descriptor.
    pub fn ecdsa_sighash_script_code(&self) -> ScriptBuf {
        match self.inner {
            //     - For P2WSH witness program, if the witnessScript does not contain any `OP_CODESEPARATOR`,
            //       the `scriptCode` is the `witnessScript` serialized as scripts inside CTxOut.
            ShInner::Wsh(ref wsh) => wsh.ecdsa_sighash_script_code(),
            ShInner::SortedMulti(ref smv) => smv.encode(),
            ShInner::Wpkh(ref wpkh) => wpkh.ecdsa_sighash_script_code(),
            // For "legacy" P2SH outputs, it is defined as the txo's redeemScript.
            ShInner::Ms(ref ms) => ms.encode(),
        }
    }

    /// Computes the scriptSig that will be in place for an unsigned input
    /// spending an output with this descriptor. For pre-segwit descriptors,
    /// which use the scriptSig for signatures, this returns the empty script.
    ///
    /// This is used in Segwit transactions to produce an unsigned transaction
    /// whose txid will not change during signing (since only the witness data
    /// will change).
    pub fn unsigned_script_sig(&self) -> ScriptBuf {
        match self.inner {
            ShInner::Wsh(ref wsh) => {
                // wsh explicit must contain exactly 1 element
                let witness_script = wsh.inner_script().to_p2wsh();
                let push_bytes = <&PushBytes>::try_from(witness_script.as_bytes())
                    .expect("Witness script is not too large");
                script::Builder::new().push_slice(push_bytes).into_script()
            }
            ShInner::Wpkh(ref wpkh) => {
                let redeem_script = wpkh.script_pubkey();
                let push_bytes: &PushBytes =
                    <&PushBytes>::try_from(redeem_script.as_bytes()).expect("Script not too large");
                script::Builder::new().push_slice(push_bytes).into_script()
            }
            ShInner::SortedMulti(..) | ShInner::Ms(..) => ScriptBuf::new(),
        }
    }

    /// Returns satisfying non-malleable witness and scriptSig with minimum
    /// weight to spend an output controlled by the given descriptor if it is
    /// possible to construct one using the `satisfier`.
    pub fn get_satisfaction<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        let script_sig = self.unsigned_script_sig();
        match self.inner {
            ShInner::Wsh(ref wsh) => {
                let (witness, _) = wsh.get_satisfaction(satisfier)?;
                Ok((witness, script_sig))
            }
            ShInner::Wpkh(ref wpkh) => {
                let (witness, _) = wpkh.get_satisfaction(satisfier)?;
                Ok((witness, script_sig))
            }
            ShInner::SortedMulti(ref smv) => {
                let mut script_witness = smv.satisfy(satisfier)?;
                script_witness.push(smv.encode().into_bytes());
                let script_sig = witness_to_scriptsig(&script_witness);
                let witness = vec![];
                Ok((witness, script_sig))
            }
            ShInner::Ms(ref ms) => {
                let mut script_witness = ms.satisfy(satisfier)?;
                script_witness.push(ms.encode().into_bytes());
                let script_sig = witness_to_scriptsig(&script_witness);
                let witness = vec![];
                Ok((witness, script_sig))
            }
        }
    }

    /// Returns satisfying, possibly malleable, witness and scriptSig with
    /// minimum weight to spend an output controlled by the given descriptor if
    /// it is possible to construct one using the `satisfier`.
    pub fn get_satisfaction_mall<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        let script_sig = self.unsigned_script_sig();
        match self.inner {
            ShInner::Wsh(ref wsh) => {
                let (witness, _) = wsh.get_satisfaction_mall(satisfier)?;
                Ok((witness, script_sig))
            }
            ShInner::Ms(ref ms) => {
                let mut script_witness = ms.satisfy_malleable(satisfier)?;
                script_witness.push(ms.encode().into_bytes());
                let script_sig = witness_to_scriptsig(&script_witness);
                let witness = vec![];
                Ok((witness, script_sig))
            }
            _ => self.get_satisfaction(satisfier),
        }
    }
}

impl Sh<DefiniteDescriptorKey> {
    /// Returns a plan if the provided assets are sufficient to produce a non-malleable satisfaction
    pub fn plan_satisfaction<P>(
        &self,
        provider: &P,
    ) -> Satisfaction<Placeholder<DefiniteDescriptorKey>>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        match &self.inner {
            ShInner::Wsh(ref wsh) => wsh.plan_satisfaction(provider),
            ShInner::Wpkh(ref wpkh) => wpkh.plan_satisfaction(provider),
            ShInner::SortedMulti(ref smv) => smv.build_template(provider),
            ShInner::Ms(ref ms) => ms.build_template(provider),
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
            ShInner::Wsh(ref wsh) => wsh.plan_satisfaction_mall(provider),
            ShInner::Ms(ref ms) => ms.build_template_mall(provider),
            _ => self.plan_satisfaction(provider),
        }
    }
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Sh<Pk> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, pred: F) -> bool {
        match self.inner {
            ShInner::Wsh(ref wsh) => wsh.for_each_key(pred),
            ShInner::SortedMulti(ref smv) => smv.for_each_key(pred),
            ShInner::Wpkh(ref wpkh) => wpkh.for_each_key(pred),
            ShInner::Ms(ref ms) => ms.for_each_key(pred),
        }
    }
}
