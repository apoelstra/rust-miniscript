// SPDX-License-Identifier: CC0-1.0

//! # Output Descriptors
//!
//! Tools for representing Bitcoin output's scriptPubKeys as abstract spending
//! policies known as "output descriptors". These include a Miniscript which
//! describes the actual signing policy, as well as the blockchain format (P2SH,
//! Segwit v0, etc.)
//!
//! The format represents EC public keys abstractly to allow wallets to replace
//! these with BIP32 paths, pay-to-contract instructions, etc.
//!

use core::fmt;
use core::ops::Range;
use core::str::{self, FromStr};

use bitcoin::hashes::{hash160, ripemd160, sha256};
use bitcoin::{
    secp256k1, Address, Network, Script, ScriptBuf, TxIn, Weight, Witness, WitnessVersion,
};
use sync::Arc;

use crate::expression::FromTree as _;
use crate::miniscript::decode::Terminal;
use crate::miniscript::{satisfy, Legacy, Miniscript, Segwitv0};
use crate::plan::{AssetProvider, Plan};
use crate::prelude::*;
use crate::{
    expression, hash256, BareCtx, Error, ForEachKey, FromStrKey, MiniscriptKey, ParseError,
    Satisfier, ToPublicKey, TranslateErr, Translator,
};

mod bare;
mod segwitv0;
mod sh;
mod sortedmulti;
mod tr;

// Descriptor Exports
pub use self::bare::{Bare, Pkh};
pub use self::segwitv0::{Wpkh, Wsh, WshInner};
pub use self::sh::{Sh, ShInner};
pub use self::sortedmulti::SortedMultiVec;
pub use self::tr::{TapTree, Tr};

pub mod checksum;
mod key;

pub use self::key::{
    ConversionError, DefiniteDescriptorKey, DerivPaths, DescriptorKeyParseError,
    DescriptorMultiXKey, DescriptorPublicKey, DescriptorSecretKey, DescriptorXKey, InnerXKey,
    SinglePriv, SinglePub, SinglePubKey, Wildcard,
};

/// Alias type for a map of public key to secret key
///
/// This map is returned whenever a descriptor that contains secrets is parsed using
/// [`Descriptor::parse_descriptor`], since the descriptor will always only contain
/// public keys. This map allows looking up the corresponding secret key given a
/// public key from the descriptor.
pub type KeyMap = BTreeMap<DescriptorPublicKey, DescriptorSecretKey>;

/// Script descriptor
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Descriptor<Pk: MiniscriptKey> {
    /// A raw scriptpubkey (including pay-to-pubkey) under Legacy context
    Bare(Bare<Pk>),
    /// Pay-to-PubKey-Hash
    Pkh(Pkh<Pk>),
    /// Pay-to-Witness-PubKey-Hash
    Wpkh(Wpkh<Pk>),
    /// Pay-to-ScriptHash(includes nested wsh/wpkh/sorted multi)
    Sh(Sh<Pk>),
    /// Pay-to-Witness-ScriptHash with Segwitv0 context
    Wsh(Wsh<Pk>),
    /// Pay-to-Taproot
    Tr(Tr<Pk>),
}

impl<Pk: MiniscriptKey> From<Bare<Pk>> for Descriptor<Pk> {
    #[inline]
    fn from(inner: Bare<Pk>) -> Self { Descriptor::Bare(inner) }
}

impl<Pk: MiniscriptKey> From<Pkh<Pk>> for Descriptor<Pk> {
    #[inline]
    fn from(inner: Pkh<Pk>) -> Self { Descriptor::Pkh(inner) }
}

impl<Pk: MiniscriptKey> From<Wpkh<Pk>> for Descriptor<Pk> {
    #[inline]
    fn from(inner: Wpkh<Pk>) -> Self { Descriptor::Wpkh(inner) }
}

impl<Pk: MiniscriptKey> From<Sh<Pk>> for Descriptor<Pk> {
    #[inline]
    fn from(inner: Sh<Pk>) -> Self { Descriptor::Sh(inner) }
}

impl<Pk: MiniscriptKey> From<Wsh<Pk>> for Descriptor<Pk> {
    #[inline]
    fn from(inner: Wsh<Pk>) -> Self { Descriptor::Wsh(inner) }
}

impl<Pk: MiniscriptKey> From<Tr<Pk>> for Descriptor<Pk> {
    #[inline]
    fn from(inner: Tr<Pk>) -> Self { Descriptor::Tr(inner) }
}

/// Descriptor Type of the descriptor
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum DescriptorType {
    /// Bare descriptor(Contains the native P2pk)
    Bare,
    /// Pure Sh Descriptor. Does not contain nested Wsh/Wpkh
    Sh,
    /// Pkh Descriptor
    Pkh,
    /// Wpkh Descriptor
    Wpkh,
    /// Wsh
    Wsh,
    /// Sh Wrapped Wsh
    ShWsh,
    /// Sh wrapped Wpkh
    ShWpkh,
    /// Sh Sorted Multi
    ShSortedMulti,
    /// Wsh Sorted Multi
    WshSortedMulti,
    /// Sh Wsh Sorted Multi
    ShWshSortedMulti,
    /// Tr Descriptor
    Tr,
}

impl DescriptorType {
    /// Returns the segwit version implied by the descriptor type.
    ///
    /// This will return `Some(WitnessVersion::V0)` whether it is "native" segwitv0 or "wrapped" p2sh segwit.
    pub fn segwit_version(&self) -> Option<WitnessVersion> {
        use self::DescriptorType::*;
        match self {
            Tr => Some(WitnessVersion::V1),
            Wpkh | ShWpkh | Wsh | ShWsh | ShWshSortedMulti | WshSortedMulti => {
                Some(WitnessVersion::V0)
            }
            Bare | Sh | Pkh | ShSortedMulti => None,
        }
    }
}

impl<Pk: MiniscriptKey> Descriptor<Pk> {
    // Keys

    /// Create a new pk descriptor
    pub fn new_pk(pk: Pk) -> Self {
        // roundabout way to constuct `c:pk_k(pk)`
        let ms: Miniscript<Pk, BareCtx> = Miniscript::from_ast(Terminal::Check(Arc::new(
            Miniscript::from_ast(Terminal::PkK(pk)).expect("Type check cannot fail"),
        )))
        .expect("Type check cannot fail");
        Descriptor::Bare(Bare::new(ms).expect("Context checks cannot fail for p2pk"))
    }

    /// Create a new PkH descriptor
    pub fn new_pkh(pk: Pk) -> Result<Self, Error> { Ok(Descriptor::Pkh(Pkh::new(pk)?)) }

    /// Create a new Wpkh descriptor
    /// Will return Err if uncompressed key is used
    pub fn new_wpkh(pk: Pk) -> Result<Self, Error> { Ok(Descriptor::Wpkh(Wpkh::new(pk)?)) }

    /// Create a new sh wrapped wpkh from `Pk`.
    /// Errors when uncompressed keys are supplied
    pub fn new_sh_wpkh(pk: Pk) -> Result<Self, Error> { Ok(Descriptor::Sh(Sh::new_wpkh(pk)?)) }

    // Miniscripts

    /// Create a new sh for a given redeem script
    /// Errors when miniscript exceeds resource limits under p2sh context
    /// or does not type check at the top level
    pub fn new_sh(ms: Miniscript<Pk, Legacy>) -> Result<Self, Error> {
        Ok(Descriptor::Sh(Sh::new(ms)?))
    }

    /// Create a new wsh descriptor from witness script
    /// Errors when miniscript exceeds resource limits under p2sh context
    /// or does not type check at the top level
    pub fn new_wsh(ms: Miniscript<Pk, Segwitv0>) -> Result<Self, Error> {
        Ok(Descriptor::Wsh(Wsh::new(ms)?))
    }

    /// Create a new sh wrapped wsh descriptor with witness script
    /// Errors when miniscript exceeds resource limits under wsh context
    /// or does not type check at the top level
    pub fn new_sh_wsh(ms: Miniscript<Pk, Segwitv0>) -> Result<Self, Error> {
        Ok(Descriptor::Sh(Sh::new_wsh(ms)?))
    }

    /// Create a new bare descriptor from witness script
    /// Errors when miniscript exceeds resource limits under bare context
    /// or does not type check at the top level
    pub fn new_bare(ms: Miniscript<Pk, BareCtx>) -> Result<Self, Error> {
        Ok(Descriptor::Bare(Bare::new(ms)?))
    }

    // Wrap with sh

    /// Create a new sh wrapper for the given wpkh descriptor
    pub fn new_sh_with_wpkh(wpkh: Wpkh<Pk>) -> Self { Descriptor::Sh(Sh::new_with_wpkh(wpkh)) }

    /// Create a new sh wrapper for the given wsh descriptor
    pub fn new_sh_with_wsh(wsh: Wsh<Pk>) -> Self { Descriptor::Sh(Sh::new_with_wsh(wsh)) }

    // sorted multi

    /// Create a new sh sortedmulti descriptor with threshold `k`
    /// and Vec of `pks`.
    /// Errors when miniscript exceeds resource limits under p2sh context
    pub fn new_sh_sortedmulti(k: usize, pks: Vec<Pk>) -> Result<Self, Error> {
        Ok(Descriptor::Sh(Sh::new_sortedmulti(k, pks)?))
    }

    /// Create a new sh wrapped wsh sortedmulti descriptor from threshold
    /// `k` and Vec of `pks`
    /// Errors when miniscript exceeds resource limits under segwit context
    pub fn new_sh_wsh_sortedmulti(k: usize, pks: Vec<Pk>) -> Result<Self, Error> {
        Ok(Descriptor::Sh(Sh::new_wsh_sortedmulti(k, pks)?))
    }

    /// Create a new wsh sorted multi descriptor
    /// Errors when miniscript exceeds resource limits under p2sh context
    pub fn new_wsh_sortedmulti(k: usize, pks: Vec<Pk>) -> Result<Self, Error> {
        Ok(Descriptor::Wsh(Wsh::new_sortedmulti(k, pks)?))
    }

    /// Create new tr descriptor
    /// Errors when miniscript exceeds resource limits under Tap context
    pub fn new_tr(key: Pk, script: Option<tr::TapTree<Pk>>) -> Result<Self, Error> {
        Ok(Descriptor::Tr(Tr::new(key, script)?))
    }

    /// For a Taproot descriptor, returns the internal key.
    pub fn internal_key(&self) -> Option<&Pk> {
        if let Descriptor::Tr(ref tr) = self {
            Some(tr.internal_key())
        } else {
            None
        }
    }

    /// For a Taproot descriptor, returns the [`TapTree`] describing the Taproot tree.
    ///
    /// To obtain the individual leaves of the tree, call [`TapTree::iter`] on the
    /// returned value.
    pub fn tap_tree(&self) -> Option<&TapTree<Pk>> {
        if let Descriptor::Tr(ref tr) = self {
            tr.tap_tree().as_ref()
        } else {
            None
        }
    }

    /// For a Taproot descriptor, returns an iterator over the scripts in the Taptree.
    ///
    /// If the descriptor is not a Taproot descriptor, **or** if the descriptor is a
    /// Taproot descriptor containing only a keyspend, returns an empty iterator.
    pub fn tap_tree_iter(&self) -> tr::TapTreeIter<Pk> {
        if let Descriptor::Tr(ref tr) = self {
            if let Some(ref tree) = tr.tap_tree() {
                return tree.iter();
            }
        }
        tr::TapTreeIter::empty()
    }

    /// Get the [DescriptorType] of [Descriptor]
    pub fn desc_type(&self) -> DescriptorType {
        match *self {
            Descriptor::Bare(ref _bare) => DescriptorType::Bare,
            Descriptor::Pkh(ref _pkh) => DescriptorType::Pkh,
            Descriptor::Wpkh(ref _wpkh) => DescriptorType::Wpkh,
            Descriptor::Sh(ref sh) => match sh.as_inner() {
                ShInner::Wsh(ref wsh) => match wsh.as_inner() {
                    WshInner::SortedMulti(ref _smv) => DescriptorType::ShWshSortedMulti,
                    WshInner::Ms(ref _ms) => DescriptorType::ShWsh,
                },
                ShInner::Wpkh(ref _wpkh) => DescriptorType::ShWpkh,
                ShInner::SortedMulti(ref _smv) => DescriptorType::ShSortedMulti,
                ShInner::Ms(ref _ms) => DescriptorType::Sh,
            },
            Descriptor::Wsh(ref wsh) => match wsh.as_inner() {
                WshInner::SortedMulti(ref _smv) => DescriptorType::WshSortedMulti,
                WshInner::Ms(ref _ms) => DescriptorType::Wsh,
            },
            Descriptor::Tr(ref _tr) => DescriptorType::Tr,
        }
    }

    /// Checks whether the descriptor is safe.
    ///
    /// Checks whether all the spend paths in the descriptor are possible on the
    /// bitcoin network under the current standardness and consensus rules. Also
    /// checks whether the descriptor requires signatures on all spend paths and
    /// whether the script is malleable.
    ///
    /// In general, all the guarantees of miniscript hold only for safe scripts.
    /// The signer may not be able to find satisfactions even if one exists.
    pub fn sanity_check(&self) -> Result<(), Error> {
        match *self {
            Descriptor::Bare(ref bare) => bare.sanity_check(),
            Descriptor::Pkh(_) => Ok(()),
            Descriptor::Wpkh(ref wpkh) => wpkh.sanity_check(),
            Descriptor::Wsh(ref wsh) => wsh.sanity_check(),
            Descriptor::Sh(ref sh) => sh.sanity_check(),
            Descriptor::Tr(ref tr) => tr.sanity_check(),
        }
    }

    /// Computes an upper bound on the difference between a non-satisfied
    /// `TxIn`'s `segwit_weight` and a satisfied `TxIn`'s `segwit_weight`
    ///
    /// Since this method uses `segwit_weight` instead of `legacy_weight`,
    /// if you want to include only legacy inputs in your transaction,
    /// you should remove 1WU from each input's `max_weight_to_satisfy`
    /// for a more accurate estimate.
    ///
    /// In other words, for segwit inputs or legacy inputs included in
    /// segwit transactions, the following will hold for each input if
    /// that input was satisfied with the largest possible witness:
    /// ```ignore
    /// for i in 0..transaction.input.len() {
    ///     assert_eq!(
    ///         descriptor_for_input[i].max_weight_to_satisfy(),
    ///         transaction.input[i].segwit_weight() - TxIn::default().segwit_weight()
    ///     );
    /// }
    /// ```
    ///
    /// Instead, for legacy transactions, the following will hold for each input
    /// if that input was satisfied with the largest possible witness:
    /// ```ignore
    /// for i in 0..transaction.input.len() {
    ///     assert_eq!(
    ///         descriptor_for_input[i].max_weight_to_satisfy(),
    ///         transaction.input[i].legacy_weight() - TxIn::default().legacy_weight()
    ///     );
    /// }
    /// ```
    ///
    /// Assumes all ECDSA signatures are 73 bytes, including push opcode and
    /// sighash suffix.
    /// Assumes all Schnorr signatures are 66 bytes, including push opcode and
    /// sighash suffix.
    ///
    /// # Errors
    /// When the descriptor is impossible to safisfy (ex: sh(OP_FALSE)).
    pub fn max_weight_to_satisfy(&self) -> Result<Weight, Error> {
        let weight = match *self {
            Descriptor::Bare(ref bare) => bare.max_weight_to_satisfy()?,
            Descriptor::Pkh(ref pkh) => pkh.max_weight_to_satisfy(),
            Descriptor::Wpkh(ref wpkh) => wpkh.max_weight_to_satisfy(),
            Descriptor::Wsh(ref wsh) => wsh.max_weight_to_satisfy()?,
            Descriptor::Sh(ref sh) => sh.max_weight_to_satisfy()?,
            Descriptor::Tr(ref tr) => tr.max_weight_to_satisfy()?,
        };
        Ok(weight)
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
    #[allow(deprecated)]
    pub fn max_satisfaction_weight(&self) -> Result<usize, Error> {
        let weight = match *self {
            Descriptor::Bare(ref bare) => bare.max_satisfaction_weight()?,
            Descriptor::Pkh(ref pkh) => pkh.max_satisfaction_weight(),
            Descriptor::Wpkh(ref wpkh) => wpkh.max_satisfaction_weight(),
            Descriptor::Wsh(ref wsh) => wsh.max_satisfaction_weight()?,
            Descriptor::Sh(ref sh) => sh.max_satisfaction_weight()?,
            Descriptor::Tr(ref tr) => tr.max_satisfaction_weight()?,
        };
        Ok(weight)
    }

    /// Converts a descriptor using one kind of keys to another kind of key.
    pub fn translate_pk<T>(
        &self,
        t: &mut T,
    ) -> Result<Descriptor<T::TargetPk>, TranslateErr<T::Error>>
    where
        T: Translator<Pk>,
    {
        let desc = match *self {
            Descriptor::Bare(ref bare) => Descriptor::Bare(bare.translate_pk(t)?),
            Descriptor::Pkh(ref pk) => Descriptor::Pkh(pk.translate_pk(t)?),
            Descriptor::Wpkh(ref pk) => Descriptor::Wpkh(pk.translate_pk(t)?),
            Descriptor::Sh(ref sh) => Descriptor::Sh(sh.translate_pk(t)?),
            Descriptor::Wsh(ref wsh) => Descriptor::Wsh(wsh.translate_pk(t)?),
            Descriptor::Tr(ref tr) => Descriptor::Tr(tr.translate_pk(t)?),
        };
        Ok(desc)
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Descriptor<Pk> {
    /// Computes the Bitcoin address of the descriptor, if one exists
    ///
    /// Some descriptors like pk() don't have an address.
    ///
    /// # Errors
    /// For raw/bare descriptors that don't have an address.
    pub fn address(&self, network: Network) -> Result<Address, Error> {
        match *self {
            Descriptor::Bare(_) => Err(Error::BareDescriptorAddr),
            Descriptor::Pkh(ref pkh) => Ok(pkh.address(network)),
            Descriptor::Wpkh(ref wpkh) => Ok(wpkh.address(network)),
            Descriptor::Wsh(ref wsh) => Ok(wsh.address(network)),
            Descriptor::Sh(ref sh) => Ok(sh.address(network)),
            Descriptor::Tr(ref tr) => Ok(tr.address(network)),
        }
    }

    /// Computes the scriptpubkey of the descriptor.
    pub fn script_pubkey(&self) -> ScriptBuf {
        match *self {
            Descriptor::Bare(ref bare) => bare.script_pubkey(),
            Descriptor::Pkh(ref pkh) => pkh.script_pubkey(),
            Descriptor::Wpkh(ref wpkh) => wpkh.script_pubkey(),
            Descriptor::Wsh(ref wsh) => wsh.script_pubkey(),
            Descriptor::Sh(ref sh) => sh.script_pubkey(),
            Descriptor::Tr(ref tr) => tr.script_pubkey(),
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
        match *self {
            Descriptor::Bare(_) => ScriptBuf::new(),
            Descriptor::Pkh(_) => ScriptBuf::new(),
            Descriptor::Wpkh(_) => ScriptBuf::new(),
            Descriptor::Wsh(_) => ScriptBuf::new(),
            Descriptor::Sh(ref sh) => sh.unsigned_script_sig(),
            Descriptor::Tr(_) => ScriptBuf::new(),
        }
    }

    /// Computes the the underlying script before any hashing is done. For
    /// `Bare`, `Pkh` and `Wpkh` this is the scriptPubkey; for `ShWpkh` and `Sh`
    /// this is the redeemScript; for the others it is the witness script.
    ///
    /// # Errors
    /// If the descriptor is a taproot descriptor.
    pub fn explicit_script(&self) -> Result<ScriptBuf, Error> {
        match *self {
            Descriptor::Bare(ref bare) => Ok(bare.script_pubkey()),
            Descriptor::Pkh(ref pkh) => Ok(pkh.script_pubkey()),
            Descriptor::Wpkh(ref wpkh) => Ok(wpkh.script_pubkey()),
            Descriptor::Wsh(ref wsh) => Ok(wsh.inner_script()),
            Descriptor::Sh(ref sh) => Ok(sh.inner_script()),
            Descriptor::Tr(_) => Err(Error::TrNoScriptCode),
        }
    }

    /// Computes the `scriptCode` of a transaction output.
    ///
    /// The `scriptCode` is the Script of the previous transaction output being
    /// serialized in the sighash when evaluating a `CHECKSIG` & co. OP code.
    ///
    /// # Errors
    /// If the descriptor is a taproot descriptor.
    pub fn script_code(&self) -> Result<ScriptBuf, Error> {
        match *self {
            Descriptor::Bare(ref bare) => Ok(bare.ecdsa_sighash_script_code()),
            Descriptor::Pkh(ref pkh) => Ok(pkh.ecdsa_sighash_script_code()),
            Descriptor::Wpkh(ref wpkh) => Ok(wpkh.ecdsa_sighash_script_code()),
            Descriptor::Wsh(ref wsh) => Ok(wsh.ecdsa_sighash_script_code()),
            Descriptor::Sh(ref sh) => Ok(sh.ecdsa_sighash_script_code()),
            Descriptor::Tr(_) => Err(Error::TrNoScriptCode),
        }
    }

    /// Returns satisfying non-malleable witness and scriptSig to spend an
    /// output controlled by the given descriptor if it possible to
    /// construct one using the satisfier S.
    pub fn get_satisfaction<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        match *self {
            Descriptor::Bare(ref bare) => bare.get_satisfaction(satisfier),
            Descriptor::Pkh(ref pkh) => pkh.get_satisfaction(satisfier),
            Descriptor::Wpkh(ref wpkh) => wpkh.get_satisfaction(satisfier),
            Descriptor::Wsh(ref wsh) => wsh.get_satisfaction(satisfier),
            Descriptor::Sh(ref sh) => sh.get_satisfaction(satisfier),
            Descriptor::Tr(ref tr) => tr.get_satisfaction(&satisfier),
        }
    }

    /// Returns a possilbly mallable satisfying non-malleable witness and scriptSig to spend an
    /// output controlled by the given descriptor if it possible to
    /// construct one using the satisfier S.
    pub fn get_satisfaction_mall<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        match *self {
            Descriptor::Bare(ref bare) => bare.get_satisfaction_mall(satisfier),
            Descriptor::Pkh(ref pkh) => pkh.get_satisfaction_mall(satisfier),
            Descriptor::Wpkh(ref wpkh) => wpkh.get_satisfaction_mall(satisfier),
            Descriptor::Wsh(ref wsh) => wsh.get_satisfaction_mall(satisfier),
            Descriptor::Sh(ref sh) => sh.get_satisfaction_mall(satisfier),
            Descriptor::Tr(ref tr) => tr.get_satisfaction_mall(&satisfier),
        }
    }

    /// Attempts to produce a non-malleable satisfying witness and scriptSig to spend an
    /// output controlled by the given descriptor; add the data to a given
    /// `TxIn` output.
    pub fn satisfy<S>(&self, txin: &mut TxIn, satisfier: S) -> Result<(), Error>
    where
        S: Satisfier<Pk>,
    {
        let (witness, script_sig) = self.get_satisfaction(satisfier)?;
        txin.witness = Witness::from_slice(&witness);
        txin.script_sig = script_sig;
        Ok(())
    }
}

impl Descriptor<DefiniteDescriptorKey> {
    /// Returns a plan if the provided assets are sufficient to produce a non-malleable satisfaction
    ///
    /// If the assets aren't sufficient for generating a Plan, the descriptor is returned
    pub fn plan<P>(self, provider: &P) -> Result<Plan, Self>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        let satisfaction = match self {
            Descriptor::Bare(ref bare) => bare.plan_satisfaction(provider),
            Descriptor::Pkh(ref pkh) => pkh.plan_satisfaction(provider),
            Descriptor::Wpkh(ref wpkh) => wpkh.plan_satisfaction(provider),
            Descriptor::Wsh(ref wsh) => wsh.plan_satisfaction(provider),
            Descriptor::Sh(ref sh) => sh.plan_satisfaction(provider),
            Descriptor::Tr(ref tr) => tr.plan_satisfaction(provider),
        };

        if let satisfy::Witness::Stack(stack) = satisfaction.stack {
            Ok(Plan {
                descriptor: self,
                template: stack,
                absolute_timelock: satisfaction.absolute_timelock.map(Into::into),
                relative_timelock: satisfaction.relative_timelock.map(Into::into),
            })
        } else {
            Err(self)
        }
    }

    /// Returns a plan if the provided assets are sufficient to produce a malleable satisfaction
    ///
    /// If the assets aren't sufficient for generating a Plan, the descriptor is returned
    pub fn plan_mall<P>(self, provider: &P) -> Result<Plan, Self>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        let satisfaction = match self {
            Descriptor::Bare(ref bare) => bare.plan_satisfaction_mall(provider),
            Descriptor::Pkh(ref pkh) => pkh.plan_satisfaction_mall(provider),
            Descriptor::Wpkh(ref wpkh) => wpkh.plan_satisfaction_mall(provider),
            Descriptor::Wsh(ref wsh) => wsh.plan_satisfaction_mall(provider),
            Descriptor::Sh(ref sh) => sh.plan_satisfaction_mall(provider),
            Descriptor::Tr(ref tr) => tr.plan_satisfaction_mall(provider),
        };

        if let satisfy::Witness::Stack(stack) = satisfaction.stack {
            Ok(Plan {
                descriptor: self,
                template: stack,
                absolute_timelock: satisfaction.absolute_timelock.map(Into::into),
                // unwrap to be removed in a later commit
                relative_timelock: satisfaction.relative_timelock.map(Into::into),
            })
        } else {
            Err(self)
        }
    }
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Descriptor<Pk> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, pred: F) -> bool {
        match *self {
            Descriptor::Bare(ref bare) => bare.for_each_key(pred),
            Descriptor::Pkh(ref pkh) => pkh.for_each_key(pred),
            Descriptor::Wpkh(ref wpkh) => wpkh.for_each_key(pred),
            Descriptor::Wsh(ref wsh) => wsh.for_each_key(pred),
            Descriptor::Sh(ref sh) => sh.for_each_key(pred),
            Descriptor::Tr(ref tr) => tr.for_each_key(pred),
        }
    }
}

impl Descriptor<DescriptorPublicKey> {
    /// Whether or not the descriptor has any wildcards
    #[deprecated(note = "use has_wildcards instead")]
    pub fn is_deriveable(&self) -> bool { self.has_wildcard() }

    /// Whether or not the descriptor has any wildcards i.e. `/*`.
    pub fn has_wildcard(&self) -> bool { self.for_any_key(|key| key.has_wildcard()) }

    /// Replaces all wildcards (i.e. `/*`) in the descriptor with a particular derivation index,
    /// turning it into a *definite* descriptor.
    ///
    /// # Errors
    /// - If index ≥ 2^31
    /// - If the descriptor contains multi-path derivations
    pub fn at_derivation_index(
        &self,
        index: u32,
    ) -> Result<Descriptor<DefiniteDescriptorKey>, ConversionError> {
        struct Derivator(u32);

        impl Translator<DescriptorPublicKey> for Derivator {
            type TargetPk = DefiniteDescriptorKey;
            type Error = ConversionError;

            fn pk(
                &mut self,
                pk: &DescriptorPublicKey,
            ) -> Result<DefiniteDescriptorKey, ConversionError> {
                pk.clone().at_derivation_index(self.0)
            }

            translate_hash_clone!(DescriptorPublicKey, DescriptorPublicKey, ConversionError);
        }
        self.translate_pk(&mut Derivator(index))
            .map_err(|e| e.expect_translator_err("No Context errors while translating"))
    }

    #[deprecated(note = "use at_derivation_index instead")]
    /// Deprecated name for [`Self::at_derivation_index`].
    pub fn derive(&self, index: u32) -> Result<Descriptor<DefiniteDescriptorKey>, ConversionError> {
        self.at_derivation_index(index)
    }

    /// Convert all the public keys in the descriptor to [`bitcoin::PublicKey`] by deriving them or
    /// otherwise converting them. All [`bitcoin::secp256k1::XOnlyPublicKey`]s are converted to by adding a
    /// default(0x02) y-coordinate.
    ///
    /// This is a shorthand for:
    ///
    /// ```
    /// # use miniscript::{Descriptor, DescriptorPublicKey, bitcoin::secp256k1::Secp256k1};
    /// # use core::str::FromStr;
    /// # let descriptor = Descriptor::<DescriptorPublicKey>::from_str("tr(xpub6BgBgsespWvERF3LHQu6CnqdvfEvtMcQjYrcRzx53QJjSxarj2afYWcLteoGVky7D3UKDP9QyrLprQ3VCECoY49yfdDEHGCtMMj92pReUsQ/0/*)")
    ///     .expect("Valid ranged descriptor");
    /// # let index = 42;
    /// # let secp = Secp256k1::verification_only();
    /// let derived_descriptor = descriptor.at_derivation_index(index).unwrap().derived_descriptor(&secp).unwrap();
    /// # assert_eq!(descriptor.derived_descriptor(&secp, index).unwrap(), derived_descriptor);
    /// ```
    ///
    /// and is only here really here for backwards compatibility.
    /// See [`at_derivation_index`] and `[derived_descriptor`] for more documentation.
    ///
    /// [`at_derivation_index`]: Self::at_derivation_index
    /// [`derived_descriptor`]: crate::DerivedDescriptor::derived_descriptor
    ///
    /// # Errors
    ///
    /// This function will return an error for multi-path descriptors
    /// or if hardened derivation is attempted,
    pub fn derived_descriptor<C: secp256k1::Verification>(
        &self,
        secp: &secp256k1::Secp256k1<C>,
        index: u32,
    ) -> Result<Descriptor<bitcoin::PublicKey>, ConversionError> {
        self.at_derivation_index(index)?.derived_descriptor(secp)
    }

    /// Parse a descriptor that may contain secret keys
    ///
    /// Internally turns every secret key found into the corresponding public key and then returns a
    /// a descriptor that only contains public keys and a map to lookup the secret key given a public key.
    pub fn parse_descriptor<C: secp256k1::Signing>(
        secp: &secp256k1::Secp256k1<C>,
        s: &str,
    ) -> Result<(Descriptor<DescriptorPublicKey>, KeyMap), Error> {
        fn parse_key<C: secp256k1::Signing>(
            s: &str,
            key_map: &mut KeyMap,
            secp: &secp256k1::Secp256k1<C>,
        ) -> Result<DescriptorPublicKey, Error> {
            let (public_key, secret_key) = match DescriptorSecretKey::from_str(s) {
                Ok(sk) => (
                    sk.to_public(secp)
                        .map_err(|e| Error::Unexpected(e.to_string()))?,
                    Some(sk),
                ),
                Err(_) => (
                    // try to parse as a public key if parsing as a secret key failed
                    s.parse()
                        .map_err(|e| Error::Parse(ParseError::box_from_str(e)))?,
                    None,
                ),
            };

            if let Some(secret_key) = secret_key {
                key_map.insert(public_key.clone(), secret_key);
            }

            Ok(public_key)
        }

        let mut keymap_pk = KeyMapWrapper(BTreeMap::new(), secp);

        struct KeyMapWrapper<'a, C: secp256k1::Signing>(KeyMap, &'a secp256k1::Secp256k1<C>);

        impl<C: secp256k1::Signing> Translator<String> for KeyMapWrapper<'_, C> {
            type TargetPk = DescriptorPublicKey;
            type Error = Error;

            fn pk(&mut self, pk: &String) -> Result<DescriptorPublicKey, Error> {
                parse_key(pk, &mut self.0, self.1)
            }

            fn sha256(&mut self, sha256: &String) -> Result<sha256::Hash, Error> {
                sha256
                    .parse()
                    .map_err(|e| Error::Parse(ParseError::box_from_str(e)))
            }

            fn hash256(&mut self, hash256: &String) -> Result<hash256::Hash, Error> {
                hash256
                    .parse()
                    .map_err(|e| Error::Parse(ParseError::box_from_str(e)))
            }

            fn ripemd160(&mut self, ripemd160: &String) -> Result<ripemd160::Hash, Error> {
                ripemd160
                    .parse()
                    .map_err(|e| Error::Parse(ParseError::box_from_str(e)))
            }

            fn hash160(&mut self, hash160: &String) -> Result<hash160::Hash, Error> {
                hash160
                    .parse()
                    .map_err(|e| Error::Parse(ParseError::box_from_str(e)))
            }
        }

        let descriptor = Descriptor::<String>::from_str(s)?;
        let descriptor = descriptor
            .translate_pk(&mut keymap_pk)
            .map_err(|e| e.expect_translator_err("No Outer context errors"))?;

        Ok((descriptor, keymap_pk.0))
    }

    /// Serialize a descriptor to string with its secret keys
    pub fn to_string_with_secret(&self, key_map: &KeyMap) -> String {
        struct KeyMapLookUp<'a>(&'a KeyMap);

        impl Translator<DescriptorPublicKey> for KeyMapLookUp<'_> {
            type TargetPk = String;
            type Error = core::convert::Infallible;

            fn pk(&mut self, pk: &DescriptorPublicKey) -> Result<String, Self::Error> {
                key_to_string(pk, self.0)
            }

            fn sha256(&mut self, sha256: &sha256::Hash) -> Result<String, Self::Error> {
                Ok(sha256.to_string())
            }

            fn hash256(&mut self, hash256: &hash256::Hash) -> Result<String, Self::Error> {
                Ok(hash256.to_string())
            }

            fn ripemd160(&mut self, ripemd160: &ripemd160::Hash) -> Result<String, Self::Error> {
                Ok(ripemd160.to_string())
            }

            fn hash160(&mut self, hash160: &hash160::Hash) -> Result<String, Self::Error> {
                Ok(hash160.to_string())
            }
        }

        fn key_to_string(
            pk: &DescriptorPublicKey,
            key_map: &KeyMap,
        ) -> Result<String, core::convert::Infallible> {
            Ok(match key_map.get(pk) {
                Some(secret) => secret.to_string(),
                None => pk.to_string(),
            })
        }

        let descriptor = self
            .translate_pk(&mut KeyMapLookUp(key_map))
            .expect("Translation to string cannot fail");

        descriptor.to_string()
    }

    /// Utility method for deriving the descriptor at each index in a range to find one matching
    /// `script_pubkey`.
    ///
    /// If it finds a match then it returns the index it was derived at and the concrete
    /// descriptor at that index. If the descriptor is non-derivable then it will simply check the
    /// script pubkey against the descriptor and return it if it matches (in this case the index
    /// returned will be meaningless).
    pub fn find_derivation_index_for_spk<C: secp256k1::Verification>(
        &self,
        secp: &secp256k1::Secp256k1<C>,
        script_pubkey: &Script,
        range: Range<u32>,
    ) -> Result<Option<(u32, Descriptor<bitcoin::PublicKey>)>, ConversionError> {
        let range = if self.has_wildcard() { range } else { 0..1 };

        for i in range {
            let concrete = self.derived_descriptor(secp, i)?;
            if &concrete.script_pubkey() == script_pubkey {
                return Ok(Some((i, concrete)));
            }
        }

        Ok(None)
    }

    /// Whether this descriptor contains a key that has multiple derivation paths.
    pub fn is_multipath(&self) -> bool { self.for_any_key(DescriptorPublicKey::is_multipath) }

    /// Get as many descriptors as different paths in this descriptor.
    ///
    /// For multipath descriptors it will return as many descriptors as there is
    /// "parallel" paths. For regular descriptors it will just return itself.
    #[allow(clippy::blocks_in_conditions)]
    pub fn into_single_descriptors(self) -> Result<Vec<Descriptor<DescriptorPublicKey>>, Error> {
        // All single-path descriptors contained in this descriptor.
        let mut descriptors = Vec::new();
        // We (ab)use `for_any_key` to gather the number of separate descriptors.
        if !self.for_any_key(|key| {
            // All multipath keys must have the same number of indexes at the "multi-index"
            // step. So we can return early if we already populated the vector.
            if !descriptors.is_empty() {
                return true;
            }

            match key {
                DescriptorPublicKey::Single(..) | DescriptorPublicKey::XPub(..) => false,
                DescriptorPublicKey::MultiXPub(xpub) => {
                    for _ in 0..xpub.derivation_paths.paths().len() {
                        descriptors.push(self.clone());
                    }
                    true
                }
            }
        }) {
            // If there is no multipath key, return early.
            return Ok(vec![self]);
        }
        assert!(!descriptors.is_empty());

        // Now, transform the multipath key of each descriptor into a single-key using each index.
        struct IndexChoser(usize);
        impl Translator<DescriptorPublicKey> for IndexChoser {
            type TargetPk = DescriptorPublicKey;
            type Error = Error;

            fn pk(&mut self, pk: &DescriptorPublicKey) -> Result<DescriptorPublicKey, Error> {
                match pk {
                    DescriptorPublicKey::Single(..) | DescriptorPublicKey::XPub(..) => {
                        Ok(pk.clone())
                    }
                    DescriptorPublicKey::MultiXPub(_) => pk
                        .clone()
                        .into_single_keys()
                        .get(self.0)
                        .cloned()
                        .ok_or(Error::MultipathDescLenMismatch),
                }
            }
            translate_hash_clone!(DescriptorPublicKey, DescriptorPublicKey, Error);
        }

        for (i, desc) in descriptors.iter_mut().enumerate() {
            let mut index_choser = IndexChoser(i);
            *desc = desc
                .translate_pk(&mut index_choser)
                .map_err(|e| e.expect_translator_err("No Context errors possible"))?;
        }

        Ok(descriptors)
    }
}

impl Descriptor<DefiniteDescriptorKey> {
    /// Convert all the public keys in the descriptor to [`bitcoin::PublicKey`] by deriving them or
    /// otherwise converting them. All [`bitcoin::secp256k1::XOnlyPublicKey`]s are converted to by adding a
    /// default(0x02) y-coordinate.
    ///
    /// # Examples
    ///
    /// ```
    /// use miniscript::descriptor::{Descriptor, DescriptorPublicKey};
    /// use miniscript::bitcoin::secp256k1;
    /// use std::str::FromStr;
    ///
    /// // test from bip 86
    /// let secp = secp256k1::Secp256k1::verification_only();
    /// let descriptor = Descriptor::<DescriptorPublicKey>::from_str("tr(xpub6BgBgsespWvERF3LHQu6CnqdvfEvtMcQjYrcRzx53QJjSxarj2afYWcLteoGVky7D3UKDP9QyrLprQ3VCECoY49yfdDEHGCtMMj92pReUsQ/0/*)")
    ///     .expect("Valid ranged descriptor");
    /// let result = descriptor.at_derivation_index(0).unwrap().derived_descriptor(&secp).expect("Non-hardened derivation");
    /// assert_eq!(result.to_string(), "tr(03cc8a4bc64d897bddc5fbc2f670f7a8ba0b386779106cf1223c6fc5d7cd6fc115)#6qm9h8ym");
    /// ```
    ///
    /// # Errors
    ///
    /// This function will return an error if hardened derivation is attempted.
    pub fn derived_descriptor<C: secp256k1::Verification>(
        &self,
        secp: &secp256k1::Secp256k1<C>,
    ) -> Result<Descriptor<bitcoin::PublicKey>, ConversionError> {
        struct Derivator<'a, C: secp256k1::Verification>(&'a secp256k1::Secp256k1<C>);

        impl<C: secp256k1::Verification> Translator<DefiniteDescriptorKey> for Derivator<'_, C> {
            type TargetPk = bitcoin::PublicKey;
            type Error = ConversionError;

            fn pk(
                &mut self,
                pk: &DefiniteDescriptorKey,
            ) -> Result<bitcoin::PublicKey, ConversionError> {
                pk.derive_public_key(self.0)
            }

            translate_hash_clone!(DefiniteDescriptorKey, bitcoin::PublicKey, ConversionError);
        }

        let derived = self.translate_pk(&mut Derivator(secp));
        match derived {
            Ok(derived) => Ok(derived),
            Err(e) => Err(e.expect_translator_err("No Context errors when deriving keys")),
        }
    }
}

impl<Pk: FromStrKey> crate::expression::FromTree for Descriptor<Pk> {
    /// Parse an expression tree into a descriptor.
    fn from_tree(top: expression::TreeIterItem) -> Result<Descriptor<Pk>, Error> {
        Ok(match (top.name(), top.n_children()) {
            ("pkh", 1) => Descriptor::Pkh(Pkh::from_tree(top)?),
            ("wpkh", 1) => Descriptor::Wpkh(Wpkh::from_tree(top)?),
            ("sh", 1) => Descriptor::Sh(Sh::from_tree(top)?),
            ("wsh", 1) => Descriptor::Wsh(Wsh::from_tree(top)?),
            ("tr", _) => Descriptor::Tr(Tr::from_tree(top)?),
            _ => Descriptor::Bare(Bare::from_tree(top)?),
        })
    }
}

impl<Pk: FromStrKey> FromStr for Descriptor<Pk> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Descriptor<Pk>, Error> {
        let top = expression::Tree::from_str(s)?;
        let ret = Self::from_tree(top.root())?;
        if let Descriptor::Tr(ref inner) = ret {
            // FIXME preserve weird/broken behavior from 12.x.
            // See https://github.com/rust-bitcoin/rust-miniscript/issues/734
            ret.sanity_check()?;
            for (_, ms) in inner.iter_scripts() {
                ms.ext_check(&crate::miniscript::analyzable::ExtParams::sane())?;
            }
        }
        Ok(ret)
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Descriptor<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Descriptor::Bare(ref sub) => fmt::Debug::fmt(sub, f),
            Descriptor::Pkh(ref pkh) => fmt::Debug::fmt(pkh, f),
            Descriptor::Wpkh(ref wpkh) => fmt::Debug::fmt(wpkh, f),
            Descriptor::Sh(ref sub) => fmt::Debug::fmt(sub, f),
            Descriptor::Wsh(ref sub) => fmt::Debug::fmt(sub, f),
            Descriptor::Tr(ref tr) => fmt::Debug::fmt(tr, f),
        }
    }
}

impl<Pk: MiniscriptKey> fmt::Display for Descriptor<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Descriptor::Bare(ref sub) => fmt::Display::fmt(sub, f),
            Descriptor::Pkh(ref pkh) => fmt::Display::fmt(pkh, f),
            Descriptor::Wpkh(ref wpkh) => fmt::Display::fmt(wpkh, f),
            Descriptor::Sh(ref sub) => fmt::Display::fmt(sub, f),
            Descriptor::Wsh(ref sub) => fmt::Display::fmt(sub, f),
            Descriptor::Tr(ref tr) => fmt::Display::fmt(tr, f),
        }
    }
}

serde_string_impl_pk!(Descriptor, "a script descriptor");

macro_rules! write_descriptor {
    ($fmt:expr, $s:literal $(, $args:expr)*) => {
        {
            use fmt::Write as _;

            let mut wrapped_f = $crate::descriptor::checksum::Formatter::new($fmt);
            write!(wrapped_f, $s $(, $args)*)?;
            wrapped_f.write_checksum_if_not_alt()?;

            fmt::Result::Ok(())
        }
    }
}
pub(crate) use write_descriptor;

#[cfg(test)]
mod tests {
    use core::convert::TryFrom;

    use bitcoin::blockdata::opcodes::all::{OP_CLTV, OP_CSV};
    use bitcoin::blockdata::script::Instruction;
    use bitcoin::blockdata::{opcodes, script};
    use bitcoin::hashes::hex::FromHex;
    use bitcoin::hashes::Hash;
    use bitcoin::script::PushBytes;
    use bitcoin::sighash::EcdsaSighashType;
    use bitcoin::{bip32, PublicKey, Sequence};

    use super::{checksum, *};
    use crate::hex_script;
    #[cfg(feature = "compiler")]
    use crate::policy;

    type StdDescriptor = Descriptor<PublicKey>;
    const TEST_PK: &str = "pk(020000000000000000000000000000000000000000000000000000000000000002)";

    fn roundtrip_descriptor(s: &str) {
        let desc = Descriptor::<String>::from_str(s).unwrap();
        let output = desc.to_string();
        let normalize_aliases = s.replace("c:pk_k(", "pk(").replace("c:pk_h(", "pkh(");

        let mut checksum_eng = checksum::Engine::new();
        checksum_eng.input(&normalize_aliases).unwrap();
        assert_eq!(format!("{}#{}", &normalize_aliases, checksum_eng.checksum()), output);
    }

    #[test]
    fn display_prefers_u() {
        // The fragments u:0 and l:0 are identical in terms of Script and
        // in terms of the in-memory representation -- OrI(False, False).
        // Test that the way we display the ambiguous fragment doesn't
        // change, in case somebody somehow is depending on it.
        let desc = StdDescriptor::from_str("sh(u:0)").unwrap();
        assert_eq!("sh(u:0)#ncq3yf9h", desc.to_string());

        // This is a regression test for https://github.com/rust-bitcoin/rust-miniscript/pull/735
        // which was found at the same time. It's just a bug plain and simple.
        let desc = StdDescriptor::from_str("sh(and_n(u:0,1))").unwrap();
        assert_eq!("sh(and_n(u:0,1))#5j5tw8nm", desc.to_string());
    }

    #[test]
    fn desc_rtt_tests() {
        roundtrip_descriptor("c:pk_k()");
        roundtrip_descriptor("wsh(pk())");
        roundtrip_descriptor("wsh(c:pk_k())");
        roundtrip_descriptor("c:pk_h()");
    }
    #[test]
    fn parse_descriptor() {
        StdDescriptor::from_str("(").unwrap_err();
        StdDescriptor::from_str("(x()").unwrap_err();
        StdDescriptor::from_str("(\u{7f}()3").unwrap_err();
        StdDescriptor::from_str("pk()").unwrap_err();
        StdDescriptor::from_str("nl:0").unwrap_err(); //issue 63
        assert_eq!(
            StdDescriptor::from_str("sh(sortedmulti)")
                .unwrap_err()
                .to_string(),
            "sortedmulti must have at least 1 children, but found 0"
        ); //issue 202
        assert_eq!(
            StdDescriptor::from_str(&format!("sh(sortedmulti(2,{}))", &TEST_PK[3..69]))
                .unwrap_err()
                .to_string(),
            "invalid threshold 2-of-1; cannot have k > n",
        ); //issue 202

        StdDescriptor::from_str(TEST_PK).unwrap();

        let uncompressed_pk =
        "0414fc03b8df87cd7b872996810db8458d61da8448e531569c8517b469a119d267be5645686309c6e6736dbd93940707cc9143d3cf29f1b877ff340e2cb2d259cf";

        // Context tests
        StdDescriptor::from_str(&format!("pk({})", uncompressed_pk)).unwrap();
        StdDescriptor::from_str(&format!("pkh({})", uncompressed_pk)).unwrap();
        StdDescriptor::from_str(&format!("sh(pk({}))", uncompressed_pk)).unwrap();
        StdDescriptor::from_str(&format!("wpkh({})", uncompressed_pk)).unwrap_err();
        StdDescriptor::from_str(&format!("sh(wpkh({}))", uncompressed_pk)).unwrap_err();
        StdDescriptor::from_str(&format!("wsh(pk{})", uncompressed_pk)).unwrap_err();
        StdDescriptor::from_str(&format!("sh(wsh(pk{}))", uncompressed_pk)).unwrap_err();
        StdDescriptor::from_str(&format!("or_i(pk({}),pk({}))", uncompressed_pk, uncompressed_pk))
            .unwrap_err();
    }

    #[test]
    pub fn script_pubkey() {
        let bare = StdDescriptor::from_str(
            "multi(1,020000000000000000000000000000000000000000000000000000000000000002)",
        )
        .unwrap();
        assert_eq!(
            bare.script_pubkey(),
            hex_script(
                "512102000000000000000000000000000000000000000000000000000000000000000251ae"
            )
        );
        assert_eq!(
            bare.address(Network::Bitcoin).unwrap_err().to_string(),
            "Bare descriptors don't have address"
        );

        let pk = StdDescriptor::from_str(TEST_PK).unwrap();
        assert_eq!(
            pk.script_pubkey(),
            ScriptBuf::from(vec![
                0x21, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xac,
            ])
        );

        let pkh = StdDescriptor::from_str(
            "pkh(\
             020000000000000000000000000000000000000000000000000000000000000002\
             )",
        )
        .unwrap();
        assert_eq!(
            pkh.script_pubkey(),
            script::Builder::new()
                .push_opcode(opcodes::all::OP_DUP)
                .push_opcode(opcodes::all::OP_HASH160)
                .push_slice(
                    hash160::Hash::from_str("84e9ed95a38613f0527ff685a9928abe2d4754d4",)
                        .unwrap()
                        .to_byte_array()
                )
                .push_opcode(opcodes::all::OP_EQUALVERIFY)
                .push_opcode(opcodes::all::OP_CHECKSIG)
                .into_script()
        );
        assert_eq!(
            pkh.address(Network::Bitcoin,).unwrap().to_string(),
            "1D7nRvrRgzCg9kYBwhPH3j3Gs6SmsRg3Wq"
        );

        let wpkh = StdDescriptor::from_str(
            "wpkh(\
             020000000000000000000000000000000000000000000000000000000000000002\
             )",
        )
        .unwrap();
        assert_eq!(
            wpkh.script_pubkey(),
            script::Builder::new()
                .push_opcode(opcodes::all::OP_PUSHBYTES_0)
                .push_slice(
                    hash160::Hash::from_str("84e9ed95a38613f0527ff685a9928abe2d4754d4",)
                        .unwrap()
                        .to_byte_array()
                )
                .into_script()
        );
        assert_eq!(
            wpkh.address(Network::Bitcoin,).unwrap().to_string(),
            "bc1qsn57m9drscflq5nl76z6ny52hck5w4x5wqd9yt"
        );

        let shwpkh = StdDescriptor::from_str(
            "sh(wpkh(\
             020000000000000000000000000000000000000000000000000000000000000002\
             ))",
        )
        .unwrap();
        assert_eq!(
            shwpkh.script_pubkey(),
            script::Builder::new()
                .push_opcode(opcodes::all::OP_HASH160)
                .push_slice(
                    hash160::Hash::from_str("f1c3b9a431134cb90a500ec06e0067cfa9b8bba7",)
                        .unwrap()
                        .to_byte_array()
                )
                .push_opcode(opcodes::all::OP_EQUAL)
                .into_script()
        );
        assert_eq!(
            shwpkh.address(Network::Bitcoin,).unwrap().to_string(),
            "3PjMEzoveVbvajcnDDuxcJhsuqPHgydQXq"
        );

        let sh = StdDescriptor::from_str(
            "sh(c:pk_k(\
             020000000000000000000000000000000000000000000000000000000000000002\
             ))",
        )
        .unwrap();
        assert_eq!(
            sh.script_pubkey(),
            script::Builder::new()
                .push_opcode(opcodes::all::OP_HASH160)
                .push_slice(
                    hash160::Hash::from_str("aa5282151694d3f2f32ace7d00ad38f927a33ac8",)
                        .unwrap()
                        .to_byte_array()
                )
                .push_opcode(opcodes::all::OP_EQUAL)
                .into_script()
        );
        assert_eq!(
            sh.address(Network::Bitcoin,).unwrap().to_string(),
            "3HDbdvM9CQ6ASnQFUkWw6Z4t3qNwMesJE9"
        );

        let wsh = StdDescriptor::from_str(
            "wsh(c:pk_k(\
             020000000000000000000000000000000000000000000000000000000000000002\
             ))",
        )
        .unwrap();
        assert_eq!(
            wsh.script_pubkey(),
            script::Builder::new()
                .push_opcode(opcodes::all::OP_PUSHBYTES_0)
                .push_slice(
                    sha256::Hash::from_str(
                        "\
                         f9379edc8983152dc781747830075bd5\
                         3896e4b0ce5bff73777fd77d124ba085\
                         "
                    )
                    .unwrap()
                    .to_byte_array()
                )
                .into_script()
        );
        assert_eq!(
            wsh.address(Network::Bitcoin,).unwrap().to_string(),
            "bc1qlymeahyfsv2jm3upw3urqp6m65ufde9seedl7umh0lth6yjt5zzsk33tv6"
        );

        let shwsh = StdDescriptor::from_str(
            "sh(wsh(c:pk_k(\
             020000000000000000000000000000000000000000000000000000000000000002\
             )))",
        )
        .unwrap();
        assert_eq!(
            shwsh.script_pubkey(),
            script::Builder::new()
                .push_opcode(opcodes::all::OP_HASH160)
                .push_slice(
                    hash160::Hash::from_str("4bec5d7feeed99e1d0a23fe32a4afe126a7ff07e",)
                        .unwrap()
                        .to_byte_array()
                )
                .push_opcode(opcodes::all::OP_EQUAL)
                .into_script()
        );
        assert_eq!(
            shwsh.address(Network::Bitcoin,).unwrap().to_string(),
            "38cTksiyPT2b1uGRVbVqHdDhW9vKs84N6Z"
        );
    }

    #[test]
    fn satisfy() {
        let secp = secp256k1::Secp256k1::new();
        let sk =
            secp256k1::SecretKey::from_slice(&b"sally was a secret key, she said"[..]).unwrap();
        let pk = bitcoin::PublicKey::new(secp256k1::PublicKey::from_secret_key(&secp, &sk));
        let msg = secp256k1::Message::from_digest_slice(&b"michael was a message, amusingly"[..])
            .expect("32 bytes");
        let sig = secp.sign_ecdsa(&msg, &sk);
        let mut sigser = sig.serialize_der().to_vec();
        sigser.push(0x01); // sighash_all

        struct SimpleSat {
            sig: secp256k1::ecdsa::Signature,
            pk: bitcoin::PublicKey,
        }

        impl Satisfier<bitcoin::PublicKey> for SimpleSat {
            fn lookup_ecdsa_sig(
                &self,
                pk: &bitcoin::PublicKey,
            ) -> Option<bitcoin::ecdsa::Signature> {
                if *pk == self.pk {
                    Some(bitcoin::ecdsa::Signature {
                        signature: self.sig,
                        sighash_type: bitcoin::sighash::EcdsaSighashType::All,
                    })
                } else {
                    None
                }
            }
        }

        let satisfier = SimpleSat { sig, pk };
        let ms = ms_str!("c:pk_k({})", pk);

        let mut txin = bitcoin::TxIn {
            previous_output: bitcoin::OutPoint::default(),
            script_sig: bitcoin::ScriptBuf::new(),
            sequence: Sequence::from_height(100),
            witness: Witness::default(),
        };
        let bare = Descriptor::new_bare(ms).unwrap();

        bare.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: script::Builder::new()
                    .push_slice(<&PushBytes>::try_from(sigser.as_slice()).unwrap())
                    .into_script(),
                sequence: Sequence::from_height(100),
                witness: Witness::default(),
            }
        );
        assert_eq!(bare.unsigned_script_sig(), bitcoin::ScriptBuf::new());

        let pkh = Descriptor::new_pkh(pk).unwrap();
        pkh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: script::Builder::new()
                    .push_slice(<&PushBytes>::try_from(sigser.as_slice()).unwrap())
                    .push_key(&pk)
                    .into_script(),
                sequence: Sequence::from_height(100),
                witness: Witness::default(),
            }
        );
        assert_eq!(pkh.unsigned_script_sig(), bitcoin::ScriptBuf::new());

        let wpkh = Descriptor::new_wpkh(pk).unwrap();
        wpkh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: bitcoin::ScriptBuf::new(),
                sequence: Sequence::from_height(100),
                witness: Witness::from_slice(&[sigser.clone(), pk.to_bytes()]),
            }
        );
        assert_eq!(wpkh.unsigned_script_sig(), bitcoin::ScriptBuf::new());

        let shwpkh = Descriptor::new_sh_wpkh(pk).unwrap();
        shwpkh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        let redeem_script = script::Builder::new()
            .push_opcode(opcodes::all::OP_PUSHBYTES_0)
            .push_slice(
                hash160::Hash::from_str("d1b2a1faf62e73460af885c687dee3b7189cd8ab")
                    .unwrap()
                    .to_byte_array(),
            )
            .into_script();
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: script::Builder::new()
                    .push_slice(<&PushBytes>::try_from(redeem_script.as_bytes()).unwrap())
                    .into_script(),
                sequence: Sequence::from_height(100),
                witness: Witness::from_slice(&[sigser.clone(), pk.to_bytes()]),
            }
        );
        assert_eq!(
            shwpkh.unsigned_script_sig(),
            script::Builder::new()
                .push_slice(<&PushBytes>::try_from(redeem_script.as_bytes()).unwrap())
                .into_script()
        );

        let ms = ms_str!("c:pk_k({})", pk);
        let sh = Descriptor::new_sh(ms.clone()).unwrap();
        sh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: script::Builder::new()
                    .push_slice(<&PushBytes>::try_from(sigser.as_slice()).unwrap())
                    .push_slice(<&PushBytes>::try_from(ms.encode().as_bytes()).unwrap())
                    .into_script(),
                sequence: Sequence::from_height(100),
                witness: Witness::default(),
            }
        );
        assert_eq!(sh.unsigned_script_sig(), bitcoin::ScriptBuf::new());

        let ms = ms_str!("c:pk_k({})", pk);

        let wsh = Descriptor::new_wsh(ms.clone()).unwrap();
        wsh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: bitcoin::ScriptBuf::new(),
                sequence: Sequence::from_height(100),
                witness: Witness::from_slice(&[sigser.clone(), ms.encode().into_bytes()]),
            }
        );
        assert_eq!(wsh.unsigned_script_sig(), bitcoin::ScriptBuf::new());

        let shwsh = Descriptor::new_sh_wsh(ms.clone()).unwrap();
        shwsh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: script::Builder::new()
                    .push_slice(<&PushBytes>::try_from(ms.encode().to_p2wsh().as_bytes()).unwrap())
                    .into_script(),
                sequence: Sequence::from_height(100),
                witness: Witness::from_slice(&[sigser.clone(), ms.encode().into_bytes()]),
            }
        );
        assert_eq!(
            shwsh.unsigned_script_sig(),
            script::Builder::new()
                .push_slice(<&PushBytes>::try_from(ms.encode().to_p2wsh().as_bytes()).unwrap())
                .into_script()
        );
    }

    #[test]
    fn after_is_cltv() {
        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str("wsh(after(1000))").unwrap();
        let script = descriptor.explicit_script().unwrap();

        let actual_instructions: Vec<_> = script.instructions().collect();
        let check = actual_instructions.last().unwrap();

        assert_eq!(check, &Ok(Instruction::Op(OP_CLTV)))
    }

    #[test]
    fn older_is_csv() {
        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str("wsh(older(1000))").unwrap();
        let script = descriptor.explicit_script().unwrap();

        let actual_instructions: Vec<_> = script.instructions().collect();
        let check = actual_instructions.last().unwrap();

        assert_eq!(check, &Ok(Instruction::Op(OP_CSV)))
    }

    #[test]
    fn tr_roundtrip_key() {
        let script = Tr::<String>::from_str("tr()").unwrap().to_string();
        assert_eq!(script, format!("tr()#x4ml3kxd"))
    }

    #[test]
    fn tr_roundtrip_script() {
        let descriptor = Tr::<String>::from_str("tr(,{pk(),pk()})")
            .unwrap()
            .to_string();

        assert_eq!(descriptor, "tr(,{pk(),pk()})#7dqr6v8r");

        let descriptor = Descriptor::<String>::from_str("tr(A,{pk(B),pk(C)})")
            .unwrap()
            .to_string();
        assert_eq!(descriptor, "tr(A,{pk(B),pk(C)})#y0uc9t6x");
    }

    #[test]
    fn tr_roundtrip_tree() {
        let p1 = "020000000000000000000000000000000000000000000000000000000000000001";
        let p2 = "020000000000000000000000000000000000000000000000000000000000000002";
        let p3 = "020000000000000000000000000000000000000000000000000000000000000003";
        let p4 = "020000000000000000000000000000000000000000000000000000000000000004";
        let p5 = "03f8551772d66557da28c1de858124f365a8eb30ce6ad79c10e0f4c546d0ab0f82";
        let descriptor = Tr::<PublicKey>::from_str(&format!(
            "tr({},{{pk({}),{{pk({}),or_d(pk({}),pkh({}))}}}})",
            p1, p2, p3, p4, p5
        ))
        .unwrap()
        .to_string();

        // p5.to_pubkeyhash() = 516ca378e588a7ed71336147e2a72848b20aca1a
        assert_eq!(
            descriptor,
            format!(
                "tr({},{{pk({}),{{pk({}),or_d(pk({}),pkh({}))}}}})#tvu28c0s",
                p1, p2, p3, p4, p5
            )
        )
    }

    #[test]
    fn tr_script_pubkey() {
        let key = Descriptor::<bitcoin::PublicKey>::from_str(
            "tr(02e20e746af365e86647826397ba1c0e0d5cb685752976fe2f326ab76bdc4d6ee9)",
        )
        .unwrap();
        assert_eq!(
            key.script_pubkey().to_hex_string(),
            "51209c19294f03757da3dc235a5960631e3c55751632f5889b06b7a053bdc0bcfbcb"
        )
    }

    #[test]
    fn tr_named_branch() {
        use crate::{ParseError, ParseTreeError};

        assert!(matches!(
            StdDescriptor::from_str(
                "tr(0202d44008000010100000000084F0000000dd0dd00000000000201dceddd00d00,abc{0,0})"
            ),
            Err(Error::Parse(ParseError::Tree(ParseTreeError::IncorrectName {
                expected: "",
                ..
            }))),
        ));
    }

    #[test]
    fn roundtrip_tests() {
        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str("multi");
        assert_eq!(descriptor.unwrap_err().to_string(), "expected threshold, found terminal",);
    }

    #[test]
    fn empty_thresh() {
        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str("thresh");
        assert_eq!(descriptor.unwrap_err().to_string(), "expected threshold, found terminal");
    }

    #[test]
    fn witness_stack_for_andv_is_arranged_in_correct_order() {
        // arrange
        let a = bitcoin::PublicKey::from_str(
            "02937402303919b3a2ee5edd5009f4236f069bf75667b8e6ecf8e5464e20116a0e",
        )
        .unwrap();
        let sig_a = secp256k1::ecdsa::Signature::from_str("3045022100a7acc3719e9559a59d60d7b2837f9842df30e7edcd754e63227e6168cec72c5d022066c2feba4671c3d99ea75d9976b4da6c86968dbf3bab47b1061e7a1966b1778c").unwrap();

        let b = bitcoin::PublicKey::from_str(
            "02eb64639a17f7334bb5a1a3aad857d6fec65faef439db3de72f85c88bc2906ad3",
        )
        .unwrap();
        let sig_b = secp256k1::ecdsa::Signature::from_str("3044022075b7b65a7e6cd386132c5883c9db15f9a849a0f32bc680e9986398879a57c276022056d94d12255a4424f51c700ac75122cb354895c9f2f88f0cbb47ba05c9c589ba").unwrap();

        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str(&format!(
            "wsh(and_v(v:pk({A}),pk({B})))",
            A = a,
            B = b
        ))
        .unwrap();

        let mut txin = bitcoin::TxIn {
            previous_output: bitcoin::OutPoint::default(),
            script_sig: bitcoin::ScriptBuf::new(),
            sequence: Sequence::ZERO,
            witness: Witness::default(),
        };
        let satisfier = {
            let mut satisfier = BTreeMap::new();

            satisfier.insert(
                a,
                bitcoin::ecdsa::Signature { signature: sig_a, sighash_type: EcdsaSighashType::All },
            );
            satisfier.insert(
                b,
                bitcoin::ecdsa::Signature { signature: sig_b, sighash_type: EcdsaSighashType::All },
            );

            satisfier
        };

        // act
        descriptor.satisfy(&mut txin, &satisfier).unwrap();

        // assert
        let wit = txin.witness.to_vec();
        let witness0 = &wit[0];
        let witness1 = &wit[1];

        let sig0 = secp256k1::ecdsa::Signature::from_der(&witness0[..witness0.len() - 1]).unwrap();
        let sig1 = secp256k1::ecdsa::Signature::from_der(&witness1[..witness1.len() - 1]).unwrap();

        // why are we asserting this way?
        // The witness stack is evaluated from top to bottom. Given an `and` instruction, the left arm of the and is going to evaluate first,
        // meaning the next witness element (on a three element stack, that is the middle one) needs to be the signature for the left side of the `and`.
        // The left side of the `and` performs a CHECKSIG against public key `a` so `sig1` needs to be `sig_a` and `sig0` needs to be `sig_b`.
        assert_eq!(sig1, sig_a);
        assert_eq!(sig0, sig_b);
    }

    #[test]
    fn test_scriptcode() {
        // P2WPKH (from bip143 test vectors)
        let descriptor = Descriptor::<PublicKey>::from_str(
            "wpkh(025476c2e83188368da1ff3e292e7acafcdb3566bb0ad253f62fc70f07aeee6357)",
        )
        .unwrap();
        assert_eq!(
            *descriptor.script_code().unwrap().as_bytes(),
            Vec::<u8>::from_hex("76a9141d0f172a0ecb48aee1be1f2687d2963ae33f71a188ac").unwrap()[..]
        );

        // P2SH-P2WPKH (from bip143 test vectors)
        let descriptor = Descriptor::<PublicKey>::from_str(
            "sh(wpkh(03ad1d8e89212f0b92c74d23bb710c00662ad1470198ac48c43f7d6f93a2a26873))",
        )
        .unwrap();
        assert_eq!(
            *descriptor.script_code().unwrap().as_bytes(),
            Vec::<u8>::from_hex("76a91479091972186c449eb1ded22b78e40d009bdf008988ac").unwrap()[..]
        );

        // P2WSH (from bitcoind's `createmultisig`)
        let descriptor = Descriptor::<PublicKey>::from_str(
            "wsh(multi(2,03789ed0bb717d88f7d321a368d905e7430207ebbd82bd342cf11ae157a7ace5fd,03dbc6764b8884a92e871274b87583e6d5c2a58819473e17e107ef3f6aa5a61626))",
        )
        .unwrap();
        assert_eq!(
            *descriptor
                .script_code().unwrap()
                .as_bytes(),
            Vec::<u8>::from_hex("522103789ed0bb717d88f7d321a368d905e7430207ebbd82bd342cf11ae157a7ace5fd2103dbc6764b8884a92e871274b87583e6d5c2a58819473e17e107ef3f6aa5a6162652ae").unwrap()[..]
        );

        // P2SH-P2WSH (from bitcoind's `createmultisig`)
        let descriptor = Descriptor::<PublicKey>::from_str("sh(wsh(multi(2,03789ed0bb717d88f7d321a368d905e7430207ebbd82bd342cf11ae157a7ace5fd,03dbc6764b8884a92e871274b87583e6d5c2a58819473e17e107ef3f6aa5a61626)))").unwrap();
        assert_eq!(
            *descriptor
                .script_code().unwrap()
                .as_bytes(),
            Vec::<u8>::from_hex("522103789ed0bb717d88f7d321a368d905e7430207ebbd82bd342cf11ae157a7ace5fd2103dbc6764b8884a92e871274b87583e6d5c2a58819473e17e107ef3f6aa5a6162652ae")
                .unwrap()[..]
        );
    }

    #[test]
    fn parse_descriptor_key() {
        // With a wildcard
        let key = "[78412e3a/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*";
        let expected = DescriptorPublicKey::XPub(DescriptorXKey {
            origin: Some((
                bip32::Fingerprint::from([0x78, 0x41, 0x2e, 0x3a]),
                (&[
                    bip32::ChildNumber::from_hardened_idx(44).unwrap(),
                    bip32::ChildNumber::from_hardened_idx(0).unwrap(),
                    bip32::ChildNumber::from_hardened_idx(0).unwrap(),
                ][..])
                .into(),
            )),
            xkey: bip32::Xpub::from_str("xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL").unwrap(),
            derivation_path: (&[bip32::ChildNumber::from_normal_idx(1).unwrap()][..]).into(),
            wildcard: Wildcard::Unhardened,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Without origin
        let key = "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1";
        let expected = DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::Xpub::from_str("xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL").unwrap(),
            derivation_path: (&[bip32::ChildNumber::from_normal_idx(1).unwrap()][..]).into(),
            wildcard: Wildcard::None,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Testnet tpub
        let key = "tpubD6NzVbkrYhZ4YqYr3amYH15zjxHvBkUUeadieW8AxTZC7aY2L8aPSk3tpW6yW1QnWzXAB7zoiaNMfwXPPz9S68ZCV4yWvkVXjdeksLskCed/1";
        let expected = DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::Xpub::from_str("tpubD6NzVbkrYhZ4YqYr3amYH15zjxHvBkUUeadieW8AxTZC7aY2L8aPSk3tpW6yW1QnWzXAB7zoiaNMfwXPPz9S68ZCV4yWvkVXjdeksLskCed").unwrap(),
            derivation_path: (&[bip32::ChildNumber::from_normal_idx(1).unwrap()][..]).into(),
            wildcard: Wildcard::None,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Without derivation path
        let key = "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL";
        let expected = DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::Xpub::from_str("xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL").unwrap(),
            derivation_path: bip32::DerivationPath::from(&[][..]),
            wildcard: Wildcard::None,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Raw (compressed) pubkey
        let key = "03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8";
        let expected = DescriptorPublicKey::Single(SinglePub {
            key: SinglePubKey::FullKey(
                bitcoin::PublicKey::from_str(
                    "03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8",
                )
                .unwrap(),
            ),
            origin: None,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Raw (uncompressed) pubkey
        let key = "04f5eeb2b10c944c6b9fbcfff94c35bdeecd93df977882babc7f3a2cf7f5c81d3b09a68db7f0e04f21de5d4230e75e6dbe7ad16eefe0d4325a62067dc6f369446a";
        let expected = DescriptorPublicKey::Single(SinglePub {
            key: SinglePubKey::FullKey(bitcoin::PublicKey::from_str(
                "04f5eeb2b10c944c6b9fbcfff94c35bdeecd93df977882babc7f3a2cf7f5c81d3b09a68db7f0e04f21de5d4230e75e6dbe7ad16eefe0d4325a62067dc6f369446a",
            )
            .unwrap()),
            origin: None,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Raw pubkey with origin
        let desc =
            "[78412e3a/0'/42/0']0231c7d3fc85c148717848033ce276ae2b464a4e2c367ed33886cc428b8af48ff8";
        let expected = DescriptorPublicKey::Single(SinglePub {
            key: SinglePubKey::FullKey(
                bitcoin::PublicKey::from_str(
                    "0231c7d3fc85c148717848033ce276ae2b464a4e2c367ed33886cc428b8af48ff8",
                )
                .unwrap(),
            ),
            origin: Some((
                bip32::Fingerprint::from([0x78, 0x41, 0x2e, 0x3a]),
                (&[
                    bip32::ChildNumber::from_hardened_idx(0).unwrap(),
                    bip32::ChildNumber::from_normal_idx(42).unwrap(),
                    bip32::ChildNumber::from_hardened_idx(0).unwrap(),
                ][..])
                    .into(),
            )),
        });
        assert_eq!(expected, desc.parse().expect("Parsing desc"));
        assert_eq!(format!("{}", expected), desc);
    }

    #[test]
    fn test_sortedmulti() {
        fn _test_sortedmulti(raw_desc_one: &str, raw_desc_two: &str, raw_addr_expected: &str) {
            let secp_ctx = secp256k1::Secp256k1::verification_only();
            let index = 5;

            // Parse descriptor
            let desc_one = Descriptor::<DescriptorPublicKey>::from_str(raw_desc_one).unwrap();
            let desc_two = Descriptor::<DescriptorPublicKey>::from_str(raw_desc_two).unwrap();

            // Same string formatting
            assert_eq!(desc_one.to_string(), raw_desc_one);
            assert_eq!(desc_two.to_string(), raw_desc_two);

            // Same address
            let addr_one = desc_one
                .at_derivation_index(index)
                .unwrap()
                .derived_descriptor(&secp_ctx)
                .unwrap()
                .address(bitcoin::Network::Bitcoin)
                .unwrap();
            let addr_two = desc_two
                .at_derivation_index(index)
                .unwrap()
                .derived_descriptor(&secp_ctx)
                .unwrap()
                .address(bitcoin::Network::Bitcoin)
                .unwrap();
            let addr_expected = bitcoin::Address::from_str(raw_addr_expected)
                .unwrap()
                .assume_checked();
            assert_eq!(addr_one, addr_expected);
            assert_eq!(addr_two, addr_expected);
        }

        // P2SH and pubkeys
        _test_sortedmulti(
            "sh(sortedmulti(1,03fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a1460297556,0250863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352))#uetvewm2",
            "sh(sortedmulti(1,0250863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352,03fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a1460297556))#7l8smyg9",
            "3JZJNxvDKe6Y55ZaF5223XHwfF2eoMNnoV",
        );

        // P2WSH and single-xpub descriptor
        _test_sortedmulti(
            "wsh(sortedmulti(1,xpub661MyMwAqRbcFW31YEwpkMuc5THy2PSt5bDMsktWQcFF8syAmRUapSCGu8ED9W6oDMSgv6Zz8idoc4a6mr8BDzTJY47LJhkJ8UB7WEGuduB,xpub69H7F5d8KSRgmmdJg2KhpAK8SR3DjMwAdkxj3ZuxV27CprR9LgpeyGmXUbC6wb7ERfvrnKZjXoUmmDznezpbZb7ap6r1D3tgFxHmwMkQTPH))#7etm7zk7",
            "wsh(sortedmulti(1,xpub69H7F5d8KSRgmmdJg2KhpAK8SR3DjMwAdkxj3ZuxV27CprR9LgpeyGmXUbC6wb7ERfvrnKZjXoUmmDznezpbZb7ap6r1D3tgFxHmwMkQTPH,xpub661MyMwAqRbcFW31YEwpkMuc5THy2PSt5bDMsktWQcFF8syAmRUapSCGu8ED9W6oDMSgv6Zz8idoc4a6mr8BDzTJY47LJhkJ8UB7WEGuduB))#ppmeel9k",
            "bc1qpq2cfgz5lktxzr5zqv7nrzz46hsvq3492ump9pz8rzcl8wqtwqcspx5y6a",
        );

        // P2WSH-P2SH and ranged descriptor
        _test_sortedmulti(
            "sh(wsh(sortedmulti(1,xpub661MyMwAqRbcFW31YEwpkMuc5THy2PSt5bDMsktWQcFF8syAmRUapSCGu8ED9W6oDMSgv6Zz8idoc4a6mr8BDzTJY47LJhkJ8UB7WEGuduB/1/0/*,xpub69H7F5d8KSRgmmdJg2KhpAK8SR3DjMwAdkxj3ZuxV27CprR9LgpeyGmXUbC6wb7ERfvrnKZjXoUmmDznezpbZb7ap6r1D3tgFxHmwMkQTPH/0/0/*)))#u60cee0u",
            "sh(wsh(sortedmulti(1,xpub69H7F5d8KSRgmmdJg2KhpAK8SR3DjMwAdkxj3ZuxV27CprR9LgpeyGmXUbC6wb7ERfvrnKZjXoUmmDznezpbZb7ap6r1D3tgFxHmwMkQTPH/0/0/*,xpub661MyMwAqRbcFW31YEwpkMuc5THy2PSt5bDMsktWQcFF8syAmRUapSCGu8ED9W6oDMSgv6Zz8idoc4a6mr8BDzTJY47LJhkJ8UB7WEGuduB/1/0/*)))#75dkf44w",
            "325zcVBN5o2eqqqtGwPjmtDd8dJRyYP82s",
        );
    }

    #[test]
    fn test_parse_descriptor() {
        let secp = &secp256k1::Secp256k1::signing_only();
        let (descriptor, key_map) = Descriptor::parse_descriptor(secp, "wpkh(tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/44'/0'/0'/0/*)").unwrap();
        assert_eq!(descriptor.to_string(), "wpkh([2cbe2a6d/44'/0'/0']tpubDCvNhURocXGZsLNqWcqD3syHTqPXrMSTwi8feKVwAcpi29oYKsDD3Vex7x2TDneKMVN23RbLprfxB69v94iYqdaYHsVz3kPR37NQXeqouVz/0/*)#nhdxg96s");
        assert_eq!(key_map.len(), 1);

        // https://github.com/bitcoin/bitcoin/blob/7ae86b3c6845873ca96650fc69beb4ae5285c801/src/test/descriptor_tests.cpp#L355-L360
        macro_rules! check_invalid_checksum {
            ($secp: ident,$($desc: expr),*) => {
                use crate::{ParseError, ParseTreeError};
                $(
                    match Descriptor::parse_descriptor($secp, $desc) {
                        Err(Error::Parse(ParseError::Tree(ParseTreeError::Checksum(_)))) => {},
                        Err(e) => panic!("Expected bad checksum for {}, got '{}'", $desc, e),
                        _ => panic!("Invalid checksum treated as valid: {}", $desc),
                    };
                )*
            };
        }
        check_invalid_checksum!(secp,
            "sh(multi(2,[00000000/111'/222]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc,xprv9uPDJpEQgRQfDcW7BkF7eTya6RPxXeJCqCJGHuCJ4GiRVLzkTXBAJMu2qaMWPrS7AANYqdq6vcBcBUdJCVVFceUvJFjaPdGZ2y9WACViL4L/0))#",
            "sh(multi(2,[00000000/111'/222]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL,xpub68NZiKmJWnxxS6aaHmn81bvJeTESw724CRDs6HbuccFQN9Ku14VQrADWgqbhhTHBaohPX4CjNLf9fq9MYo6oDaPPLPxSb7gwQN3ih19Zm4Y/0))#",
            "sh(multi(2,[00000000/111'/222]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc,xprv9uPDJpEQgRQfDcW7BkF7eTya6RPxXeJCqCJGHuCJ4GiRVLzkTXBAJMu2qaMWPrS7AANYqdq6vcBcBUdJCVVFceUvJFjaPdGZ2y9WACViL4L/0))#ggrsrxfyq",
            "sh(multi(2,[00000000/111'/222]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL,xpub68NZiKmJWnxxS6aaHmn81bvJeTESw724CRDs6HbuccFQN9Ku14VQrADWgqbhhTHBaohPX4CjNLf9fq9MYo6oDaPPLPxSb7gwQN3ih19Zm4Y/0))#tjg09x5tq",
            "sh(multi(2,[00000000/111'/222]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc,xprv9uPDJpEQgRQfDcW7BkF7eTya6RPxXeJCqCJGHuCJ4GiRVLzkTXBAJMu2qaMWPrS7AANYqdq6vcBcBUdJCVVFceUvJFjaPdGZ2y9WACViL4L/0))#ggrsrxf",
            "sh(multi(2,[00000000/111'/222]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL,xpub68NZiKmJWnxxS6aaHmn81bvJeTESw724CRDs6HbuccFQN9Ku14VQrADWgqbhhTHBaohPX4CjNLf9fq9MYo6oDaPPLPxSb7gwQN3ih19Zm4Y/0))#tjg09x5",
            "sh(multi(3,[00000000/111'/222]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc,xprv9uPDJpEQgRQfDcW7BkF7eTya6RPxXeJCqCJGHuCJ4GiRVLzkTXBAJMu2qaMWPrS7AANYqdq6vcBcBUdJCVVFceUvJFjaPdGZ2y9WACViL4L/0))#ggrsrxfy",
            "sh(multi(3,[00000000/111'/222]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL,xpub68NZiKmJWnxxS6aaHmn81bvJeTESw724CRDs6HbuccFQN9Ku14VQrADWgqbhhTHBaohPX4CjNLf9fq9MYo6oDaPPLPxSb7gwQN3ih19Zm4Y/0))#tjg09x5t",
            "sh(multi(2,[00000000/111'/222]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL,xpub68NZiKmJWnxxS6aaHmn81bvJeTESw724CRDs6HbuccFQN9Ku14VQrADWgqbhhTHBaohPX4CjNLf9fq9MYo6oDaPPLPxSb7gwQN3ih19Zm4Y/0))#tjq09x4t",
            "sh(multi(2,[00000000/111'/222]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc,xprv9uPDJpEQgRQfDcW7BkF7eTya6RPxXeJCqCJGHuCJ4GiRVLzkTXBAJMu2qaMWPrS7AANYqdq6vcBcBUdJCVVFceUvJFjaPdGZ2y9WACViL4L/0))##ggssrxfy",
            "sh(multi(2,[00000000/111'/222]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL,xpub68NZiKmJWnxxS6aaHmn81bvJeTESw724CRDs6HbuccFQN9Ku14VQrADWgqbhhTHBaohPX4CjNLf9fq9MYo6oDaPPLPxSb7gwQN3ih19Zm4Y/0))##tjq09x4t"
        );

        Descriptor::parse_descriptor(secp, "sh(multi(2,[00000000/111'/222]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc,xprv9uPDJpEQgRQfDcW7BkF7eTya6RPxXeJCqCJGHuCJ4GiRVLzkTXBAJMu2qaMWPrS7AANYqdq6vcBcBUdJCVVFceUvJFjaPdGZ2y9WACViL4L/0))#ggrsrxfy").expect("Valid descriptor with checksum");
        Descriptor::parse_descriptor(secp, "sh(multi(2,[00000000/111'/222]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL,xpub68NZiKmJWnxxS6aaHmn81bvJeTESw724CRDs6HbuccFQN9Ku14VQrADWgqbhhTHBaohPX4CjNLf9fq9MYo6oDaPPLPxSb7gwQN3ih19Zm4Y/0))#tjg09x5t").expect("Valid descriptor with checksum");
    }

    #[test]
    #[cfg(feature = "compiler")]
    fn parse_and_derive() {
        let descriptor_str = "thresh(2,\
pk([d34db33f/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*),\
pk(xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1),\
pk(03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8))";
        let policy: policy::concrete::Policy<DescriptorPublicKey> = descriptor_str.parse().unwrap();
        let descriptor = Descriptor::new_sh(policy.compile().unwrap()).unwrap();
        let definite_descriptor = descriptor.at_derivation_index(42).unwrap();

        let res_descriptor_str = "thresh(2,\
pk([d34db33f/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/42),\
pk(xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1),\
pk(03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8))";
        let res_policy: policy::concrete::Policy<DescriptorPublicKey> =
            res_descriptor_str.parse().unwrap();
        let res_descriptor = Descriptor::new_sh(res_policy.compile().unwrap()).unwrap();

        assert_eq!(res_descriptor.to_string(), definite_descriptor.to_string());
    }

    #[test]
    fn parse_with_secrets() {
        let secp = &secp256k1::Secp256k1::signing_only();
        let descriptor_str = "wpkh(xprv9s21ZrQH143K4CTb63EaMxja1YiTnSEWKMbn23uoEnAzxjdUJRQkazCAtzxGm4LSoTSVTptoV9RbchnKPW9HxKtZumdyxyikZFDLhogJ5Uj/44'/0'/0'/0/*)#v20xlvm9";
        let (descriptor, keymap) =
            Descriptor::<DescriptorPublicKey>::parse_descriptor(secp, descriptor_str).unwrap();

        let expected = "wpkh([a12b02f4/44'/0'/0']xpub6BzhLAQUDcBUfHRQHZxDF2AbcJqp4Kaeq6bzJpXrjrWuK26ymTFwkEFbxPra2bJ7yeZKbDjfDeFwxe93JMqpo5SsPJH6dZdvV9kMzJkAZ69/0/*)#u37l7u8u";
        assert_eq!(expected, descriptor.to_string());
        assert_eq!(keymap.len(), 1);

        // try to turn it back into a string with the secrets
        assert_eq!(descriptor_str, descriptor.to_string_with_secret(&keymap));
    }

    #[test]
    fn checksum_for_nested_sh() {
        let descriptor_str = "sh(wpkh(xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL))";
        let descriptor: Descriptor<DescriptorPublicKey> = descriptor_str.parse().unwrap();
        assert_eq!(descriptor.to_string(), "sh(wpkh(xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL))#tjp2zm88");

        let descriptor_str = "sh(wsh(pk(xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL)))";
        let descriptor: Descriptor<DescriptorPublicKey> = descriptor_str.parse().unwrap();
        assert_eq!(descriptor.to_string(), "sh(wsh(pk(xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL)))#6c6hwr22");
    }

    #[test]
    fn test_xonly_keys() {
        let comp_key = "0308c0fcf8895f4361b4fc77afe2ad53b0bd27dcebfd863421b2b246dc283d4103";
        let x_only_key = "08c0fcf8895f4361b4fc77afe2ad53b0bd27dcebfd863421b2b246dc283d4103";

        // Both x-only keys and comp keys allowed in tr
        Descriptor::<DescriptorPublicKey>::from_str(&format!("tr({})", comp_key)).unwrap();
        Descriptor::<DescriptorPublicKey>::from_str(&format!("tr({})", x_only_key)).unwrap();

        // Only compressed keys allowed in wsh
        Descriptor::<DescriptorPublicKey>::from_str(&format!("wsh(pk({}))", comp_key)).unwrap();
        Descriptor::<DescriptorPublicKey>::from_str(&format!("wsh(pk({}))", x_only_key))
            .unwrap_err();
    }

    #[test]
    fn test_find_derivation_index_for_spk() {
        let secp = secp256k1::Secp256k1::verification_only();
        let descriptor = Descriptor::from_str("tr([73c5da0a/86'/0'/0']xpub6BgBgsespWvERF3LHQu6CnqdvfEvtMcQjYrcRzx53QJjSxarj2afYWcLteoGVky7D3UKDP9QyrLprQ3VCECoY49yfdDEHGCtMMj92pReUsQ/0/*)").unwrap();
        let script_at_0_1 = ScriptBuf::from_hex(
            "5120a82f29944d65b86ae6b5e5cc75e294ead6c59391a1edc5e016e3498c67fc7bbb",
        )
        .unwrap();
        let expected_concrete = Descriptor::from_str(
            "tr(0283dfe85a3151d2517290da461fe2815591ef69f2b18a2ce63f01697a8b313145)",
        )
        .unwrap();

        assert_eq!(descriptor.find_derivation_index_for_spk(&secp, &script_at_0_1, 0..1), Ok(None));
        assert_eq!(
            descriptor.find_derivation_index_for_spk(&secp, &script_at_0_1, 0..2),
            Ok(Some((1, expected_concrete.clone())))
        );
        assert_eq!(
            descriptor.find_derivation_index_for_spk(&secp, &script_at_0_1, 0..10),
            Ok(Some((1, expected_concrete)))
        );
    }

    #[test]
    fn display_alternate() {
        let bare = StdDescriptor::from_str(
            "pk(020000000000000000000000000000000000000000000000000000000000000002)",
        )
        .unwrap();
        assert_eq!(
            format!("{}", bare),
            "pk(020000000000000000000000000000000000000000000000000000000000000002)#7yxkn84h",
        );
        assert_eq!(
            format!("{:#}", bare),
            "pk(020000000000000000000000000000000000000000000000000000000000000002)",
        );

        let pkh = StdDescriptor::from_str(
            "pkh(020000000000000000000000000000000000000000000000000000000000000002)",
        )
        .unwrap();
        assert_eq!(
            format!("{}", pkh),
            "pkh(020000000000000000000000000000000000000000000000000000000000000002)#ma7nspkf",
        );
        assert_eq!(
            format!("{:#}", pkh),
            "pkh(020000000000000000000000000000000000000000000000000000000000000002)",
        );

        let wpkh = StdDescriptor::from_str(
            "wpkh(020000000000000000000000000000000000000000000000000000000000000002)",
        )
        .unwrap();
        assert_eq!(
            format!("{}", wpkh),
            "wpkh(020000000000000000000000000000000000000000000000000000000000000002)#d3xz2xye",
        );
        assert_eq!(
            format!("{:#}", wpkh),
            "wpkh(020000000000000000000000000000000000000000000000000000000000000002)",
        );

        let shwpkh = StdDescriptor::from_str(
            "sh(wpkh(020000000000000000000000000000000000000000000000000000000000000002))",
        )
        .unwrap();
        assert_eq!(
            format!("{}", shwpkh),
            "sh(wpkh(020000000000000000000000000000000000000000000000000000000000000002))#45zpjtet",
        );
        assert_eq!(
            format!("{:#}", shwpkh),
            "sh(wpkh(020000000000000000000000000000000000000000000000000000000000000002))",
        );

        let wsh = StdDescriptor::from_str("wsh(1)").unwrap();
        assert_eq!(format!("{}", wsh), "wsh(1)#mrg7xj7p");
        assert_eq!(format!("{:#}", wsh), "wsh(1)");

        let sh = StdDescriptor::from_str("sh(1)").unwrap();
        assert_eq!(format!("{}", sh), "sh(1)#l8r75ggs");
        assert_eq!(format!("{:#}", sh), "sh(1)");

        let shwsh = StdDescriptor::from_str("sh(wsh(1))").unwrap();
        assert_eq!(format!("{}", shwsh), "sh(wsh(1))#hcyfl07f");
        assert_eq!(format!("{:#}", shwsh), "sh(wsh(1))");

        let tr = StdDescriptor::from_str(
            "tr(020000000000000000000000000000000000000000000000000000000000000002)",
        )
        .unwrap();
        assert_eq!(
            format!("{}", tr),
            "tr(020000000000000000000000000000000000000000000000000000000000000002)#8hc7wq5h",
        );
        assert_eq!(
            format!("{:#}", tr),
            "tr(020000000000000000000000000000000000000000000000000000000000000002)",
        );
    }

    #[test]
    fn multipath_descriptors() {
        // We can parse a multipath descriptors, and make it into separate single-path descriptors.
        let desc = Descriptor::from_str("wsh(andor(pk(tpubDEN9WSToTyy9ZQfaYqSKfmVqmq1VVLNtYfj3Vkqh67et57eJ5sTKZQBkHqSwPUsoSskJeaYnPttHe2VrkCsKA27kUaN9SDc5zhqeLzKa1rr/0'/<7';8h;20>/*),older(10000),pk(tpubD8LYfn6njiA2inCoxwM7EuN3cuLVcaHAwLYeups13dpevd3nHLRdK9NdQksWXrhLQVxcUZRpnp5CkJ1FhE61WRAsHxDNAkvGkoQkAeWDYjV/8/4567/<0;1;987>/*)))").unwrap();
        assert!(desc.is_multipath());
        assert_eq!(desc.into_single_descriptors().unwrap(), vec![
            Descriptor::from_str("wsh(andor(pk(tpubDEN9WSToTyy9ZQfaYqSKfmVqmq1VVLNtYfj3Vkqh67et57eJ5sTKZQBkHqSwPUsoSskJeaYnPttHe2VrkCsKA27kUaN9SDc5zhqeLzKa1rr/0'/7'/*),older(10000),pk(tpubD8LYfn6njiA2inCoxwM7EuN3cuLVcaHAwLYeups13dpevd3nHLRdK9NdQksWXrhLQVxcUZRpnp5CkJ1FhE61WRAsHxDNAkvGkoQkAeWDYjV/8/4567/0/*)))").unwrap(),
            Descriptor::from_str("wsh(andor(pk(tpubDEN9WSToTyy9ZQfaYqSKfmVqmq1VVLNtYfj3Vkqh67et57eJ5sTKZQBkHqSwPUsoSskJeaYnPttHe2VrkCsKA27kUaN9SDc5zhqeLzKa1rr/0'/8h/*),older(10000),pk(tpubD8LYfn6njiA2inCoxwM7EuN3cuLVcaHAwLYeups13dpevd3nHLRdK9NdQksWXrhLQVxcUZRpnp5CkJ1FhE61WRAsHxDNAkvGkoQkAeWDYjV/8/4567/1/*)))").unwrap(),
            Descriptor::from_str("wsh(andor(pk(tpubDEN9WSToTyy9ZQfaYqSKfmVqmq1VVLNtYfj3Vkqh67et57eJ5sTKZQBkHqSwPUsoSskJeaYnPttHe2VrkCsKA27kUaN9SDc5zhqeLzKa1rr/0'/20/*),older(10000),pk(tpubD8LYfn6njiA2inCoxwM7EuN3cuLVcaHAwLYeups13dpevd3nHLRdK9NdQksWXrhLQVxcUZRpnp5CkJ1FhE61WRAsHxDNAkvGkoQkAeWDYjV/8/4567/987/*)))").unwrap()
        ]);

        // Even if only one of the keys is multipath.
        let desc = Descriptor::from_str("wsh(andor(pk(tpubDEN9WSToTyy9ZQfaYqSKfmVqmq1VVLNtYfj3Vkqh67et57eJ5sTKZQBkHqSwPUsoSskJeaYnPttHe2VrkCsKA27kUaN9SDc5zhqeLzKa1rr/0'/<0;1>/*),older(10000),pk(tpubD8LYfn6njiA2inCoxwM7EuN3cuLVcaHAwLYeups13dpevd3nHLRdK9NdQksWXrhLQVxcUZRpnp5CkJ1FhE61WRAsHxDNAkvGkoQkAeWDYjV/8/4567/*)))").unwrap();
        assert!(desc.is_multipath());
        assert_eq!(desc.into_single_descriptors().unwrap(), vec![
            Descriptor::from_str("wsh(andor(pk(tpubDEN9WSToTyy9ZQfaYqSKfmVqmq1VVLNtYfj3Vkqh67et57eJ5sTKZQBkHqSwPUsoSskJeaYnPttHe2VrkCsKA27kUaN9SDc5zhqeLzKa1rr/0'/0/*),older(10000),pk(tpubD8LYfn6njiA2inCoxwM7EuN3cuLVcaHAwLYeups13dpevd3nHLRdK9NdQksWXrhLQVxcUZRpnp5CkJ1FhE61WRAsHxDNAkvGkoQkAeWDYjV/8/4567/*)))").unwrap(),
            Descriptor::from_str("wsh(andor(pk(tpubDEN9WSToTyy9ZQfaYqSKfmVqmq1VVLNtYfj3Vkqh67et57eJ5sTKZQBkHqSwPUsoSskJeaYnPttHe2VrkCsKA27kUaN9SDc5zhqeLzKa1rr/0'/1/*),older(10000),pk(tpubD8LYfn6njiA2inCoxwM7EuN3cuLVcaHAwLYeups13dpevd3nHLRdK9NdQksWXrhLQVxcUZRpnp5CkJ1FhE61WRAsHxDNAkvGkoQkAeWDYjV/8/4567/*)))").unwrap(),
        ]);

        // We can detect regular single-path descriptors.
        let notmulti_desc = Descriptor::from_str("wsh(andor(pk(tpubDEN9WSToTyy9ZQfaYqSKfmVqmq1VVLNtYfj3Vkqh67et57eJ5sTKZQBkHqSwPUsoSskJeaYnPttHe2VrkCsKA27kUaN9SDc5zhqeLzKa1rr/0'/*),older(10000),pk(tpubD8LYfn6njiA2inCoxwM7EuN3cuLVcaHAwLYeups13dpevd3nHLRdK9NdQksWXrhLQVxcUZRpnp5CkJ1FhE61WRAsHxDNAkvGkoQkAeWDYjV/8/4567/*)))").unwrap();
        assert!(!notmulti_desc.is_multipath());
        assert_eq!(notmulti_desc.clone().into_single_descriptors().unwrap(), vec![notmulti_desc]);

        // We refuse to parse multipath descriptors with a mismatch in the number of derivation paths between keys.
        Descriptor::<DescriptorPublicKey>::from_str("wsh(andor(pk(tpubDEN9WSToTyy9ZQfaYqSKfmVqmq1VVLNtYfj3Vkqh67et57eJ5sTKZQBkHqSwPUsoSskJeaYnPttHe2VrkCsKA27kUaN9SDc5zhqeLzKa1rr/0'/<0;1>/*),older(10000),pk(tpubD8LYfn6njiA2inCoxwM7EuN3cuLVcaHAwLYeups13dpevd3nHLRdK9NdQksWXrhLQVxcUZRpnp5CkJ1FhE61WRAsHxDNAkvGkoQkAeWDYjV/8/<0;1;2;3;4>/*)))").unwrap_err();
        Descriptor::<DescriptorPublicKey>::from_str("wsh(andor(pk(tpubDEN9WSToTyy9ZQfaYqSKfmVqmq1VVLNtYfj3Vkqh67et57eJ5sTKZQBkHqSwPUsoSskJeaYnPttHe2VrkCsKA27kUaN9SDc5zhqeLzKa1rr/0'/<0;1;2;3>/*),older(10000),pk(tpubD8LYfn6njiA2inCoxwM7EuN3cuLVcaHAwLYeups13dpevd3nHLRdK9NdQksWXrhLQVxcUZRpnp5CkJ1FhE61WRAsHxDNAkvGkoQkAeWDYjV/8/<0;1;2>/*)))").unwrap_err();
    }

    #[test]
    fn regression_736() {
        Descriptor::<DescriptorPublicKey>::from_str(
            "tr(0000000000000000000000000000000000000000000000000000000000000002,)",
        )
        .unwrap_err();
    }

    #[test]
    fn regression_734() {
        Descriptor::<DescriptorPublicKey>::from_str(
            "wsh(or_i(pk(0202baaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a66a),1))",
        )
        .unwrap();
        Descriptor::<DescriptorPublicKey>::from_str(
            "sh(or_i(pk(0202baaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a66a),1))",
        )
        .unwrap();
        Descriptor::<DescriptorPublicKey>::from_str(
            "tr(02baaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a66a,1)",
        )
        .unwrap_err();
    }

    #[test]
    fn test_context_pks() {
        let comp_key = bitcoin::PublicKey::from_str(
            "02015e4cb53458bf813db8c79968e76e10d13ed6426a23fa71c2f41ba021c2a7ab",
        )
        .unwrap();
        let x_only_key = bitcoin::key::XOnlyPublicKey::from_str(
            "015e4cb53458bf813db8c79968e76e10d13ed6426a23fa71c2f41ba021c2a7ab",
        )
        .unwrap();
        let uncomp_key = bitcoin::PublicKey::from_str("04015e4cb53458bf813db8c79968e76e10d13ed6426a23fa71c2f41ba021c2a7ab0d46021e9e69ef061eb25eab41ae206187b2b05e829559df59d78319bd9267b4").unwrap();

        type Desc = Descriptor<DescriptorPublicKey>;

        // Legacy tests, x-only keys are not supported
        Desc::from_str(&format!("sh(pk({}))", comp_key)).unwrap();
        Desc::from_str(&format!("sh(pk({}))", uncomp_key)).unwrap();
        Desc::from_str(&format!("sh(pk({}))", x_only_key)).unwrap_err();

        // bare tests, x-only keys not supported
        Desc::from_str(&format!("pk({})", comp_key)).unwrap();
        Desc::from_str(&format!("pk({})", uncomp_key)).unwrap();
        Desc::from_str(&format!("pk({})", x_only_key)).unwrap_err();

        // pkh tests, x-only keys not supported
        Desc::from_str(&format!("pkh({})", comp_key)).unwrap();
        Desc::from_str(&format!("pkh({})", uncomp_key)).unwrap();
        Desc::from_str(&format!("pkh({})", x_only_key)).unwrap_err();

        // wpkh tests, uncompressed and x-only keys not supported
        Desc::from_str(&format!("wpkh({})", comp_key)).unwrap();
        Desc::from_str(&format!("wpkh({})", uncomp_key)).unwrap_err();
        Desc::from_str(&format!("wpkh({})", x_only_key)).unwrap_err();

        // Segwitv0 tests, uncompressed and x-only keys not supported
        Desc::from_str(&format!("wsh(pk({}))", comp_key)).unwrap();
        Desc::from_str(&format!("wsh(pk({}))", uncomp_key)).unwrap_err();
        Desc::from_str(&format!("wsh(pk({}))", x_only_key)).unwrap_err();

        // Tap tests, key path
        Desc::from_str(&format!("tr({})", comp_key)).unwrap();
        Desc::from_str(&format!("tr({})", uncomp_key)).unwrap_err();
        Desc::from_str(&format!("tr({})", x_only_key)).unwrap();

        // Tap tests, script path
        Desc::from_str(&format!("tr({},pk({}))", x_only_key, comp_key)).unwrap();
        Desc::from_str(&format!("tr({},pk({}))", x_only_key, uncomp_key)).unwrap_err();
        Desc::from_str(&format!("tr({},pk({}))", x_only_key, x_only_key)).unwrap();
    }

    #[test]
    fn test_stackoverflow() {
        type Desc = Descriptor<DescriptorPublicKey>;

        let s = "tr(02b35c601492528601122c0807fa1f8bf987b9704dff438b2524d979b954e206fb,or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(or_i(pk(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798),pk(02c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5)),pk(02f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9)),pk(02e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd13)),pk(022f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4)),pk(03fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a1460297556)),pk(025cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc)),pk(022f01e5e15cca351daff3843fb70f3c2f0a1bdd05e5af888a67784ef3e10a2a01)),pk(03acd484e2f0c7f65309ad178a9f559abde09796974c57e714c35f110dfc27ccbe)),pk(03a0434d9e47f3c86235477c7b1ae6ae5d3442d49b1943c2b752a68e2a47e247c7)),pk(03774ae7f858a9411e5ef4246b70c65aac5649980be5c17891bbec17895da008cb)),pk(03d01115d548e7561b15c38f004d734633687cf4419620095bc5b0f47070afe85a)),pk(03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8)),pk(03499fdf9e895e719cfd64e67f07d38e3226aa7b63678949e6e49b241a60e823e4)),pk(02d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e)),pk(03e60fce93b59e9ec53011aabc21c23e97b2a31369b87a5ae9c44ee89e2a6dec0a)),pk(03defdea4cdb677750a420fee807eacf21eb9898ae79b9768766e4faa04a2d4a34)),pk(025601570cb47f238d2b0286db4a990fa0f3ba28d1a319f5e7cf55c2a2444da7cc)),pk(022b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c)),pk(024ce119c96e2fa357200b559b2f7dd5a5f02d5290aff74b03f3e471b273211c97)),pk(02352bbf4a4cdd12564f93fa332ce333301d9ad40271f8107181340aef25be59d5)),pk(03421f5fc9a21065445c96fdb91c0c1e2f2431741c72713b4b99ddcb316f31e9fc)),pk(032fa2104d6b38d11b0230010559879124e42ab8dfeff5ff29dc9cdadd4ecacc3f)),pk(03fe72c435413d33d48ac09c9161ba8b09683215439d62b7940502bda8b202e6ce)),pk(029248279b09b4d68dab21a9b066edda83263c3d84e09572e269ca0cd7f5453714)),pk(026687cdb5b650d558f40cbdefc8e40997c03fe1b2abb840885e5cad81710c4c8a)),pk(03daed4f2be3a8bf278e70132fb0beb7522f570e144bf615c07e996d443dee8729)),pk(0255eb67d7b7238a70a7fa6f64d5dc3c826b31536da6eb344dc39a66f904f97968)),pk(02c44d12c7065d812e8acf28d7cbb19f9011ecd9e9fdf281b0e6a3b5e87d22e7db)),pk(036d2b085e9e382ed10b69fc311a03f8641ccfff21574de0927513a49d9a688a00)),pk(026a245bf6dc698504c89a20cfded60853152b695336c28063b61c65cbd269e6b4)),pk(03d30199d74fb5a22d47b6e054e2f378cedacffcb89904a61d75d0dbd407143e65)),pk(021697ffa6fd9de627c077e3d2fe541084ce13300b0bec1146f95ae57f0d0bd6a5)),pk(031be68a5a028f2601d0e80d468c344ba331d611b96c358b6032e8b4da0547fc11)),pk(03605bdb019981718b986d0f07e834cb0d9deb8360ffb7f61df982345ef27a7479)),pk(02e0392cfa338aaf2f0b56c563e3e5e67a5d5fefe3388f85d90c899da20f0198f9)),pk(0362d14dab4150bf497402fdc45a215e10dcb01c354959b10cfe31c7e9d87ff33d)),pk(02b699a30e6e184cdfa88ac16c7d80bffd38e2e1fc705821ea69cd5fdf1691fff7)),pk(0280c60ad0040f27dade5b4b06c408e56b2c50e9f56b9b8b425e555c2f86308b6f)),pk(0391de2f6bb67b11139f0e21203041bf080eacf59a33d99cd9f1929141bb0b4d0b)),pk(037a9375ad6167ad54aa74c6348cc54d344cc5dc9487d847049d5eabb0fa03c8fb)),pk(02fe8d1eb1bcb3432b1db5833ff5f2226d9cb5e65cee430558c18ed3a3c86ce1af)),pk(03d528ecd9b696b54c907a9ed045447a79bb408ec39b68df504bb51f459bc3ffc9)),pk(025d045857332d5b9e541514731622af8d60c180165d971a61e06b70a9b3834765)),pk(02049370a4b5f43412ea25f514e8ecdad05266115e4a7ecb1387231808f8b45963)),pk(03f8b0b03d44112259f903b3d100e3950d980fdde9c7e85701c16baedc90235717)),pk(0277f230936ee88cbbd73df930d64702ef881d811e0e1498e2f1c13eb1fc345d74)),pk(026eca335d9645307db441656ef4e65b4bfc579b27452bebc19bd870aa1118e5c3)),pk(03f2dac991cc4ce4b9ea44887e5c7c0bce58c80074ab9d4dbaeb28531b7739f530)),pk(0229757774cc6f3be1d5f1774aefa8f02e50bc64404230e7a67e8fde79bd559a9a)),pk(02463b3d9f662621fb1b4be8fbbe2520125a216cdfc9dae3debcba4850c690d45b)),pk(032b22efda32491a9e0294339ca3da761f7d36cfc8814c1b29ca731921025ff695)),pk(02f16f804244e46e2a09232d4aff3b59976b98fac14328a2d1a32496b49998f247)),pk(034fdcb8fa639cee441c8331fd47a2e5ff3447be24500ca7a5249971067c1d506b)),pk(02caf754272dc84563b0352b7a14311af55d245315ace27c65369e15f7151d41d1)),pk(02bce74de6d5f98dc027740c2bbff05b6aafe5fd8d103f827e48894a2bd3460117)),pk(022600ca4b282cb986f85d0f1709979d8b44a09c07cb86d7c124497bc86f082120)),pk(0245562f033698faca1540cbc9bf962cf4764c1ef4094ee4b6742b761c49b46d3b)),pk(037635ca72d7e8432c338ec53cd12220bc01c48685e24f7dc8c602a7746998e435)),pk(0301257e93a78a5b7d8fe0cf28ff1d8822350c778ac8a30e57d2acfc4d5fb8c192)),pk(03754e3239f325570cdbbf4a87deee8a66b7f2b33479d468fbc1a50743bf56cc18)),pk(03108443b948d1553584a271333f7fbd043c4d66a91706edecbf07f6894c04f299)),pk(03e3e6bd1071a1e96aff57859c82d570f0330800661d1c952f9fe2694691d9b9e8)),pk(03bf23c1542d16eab70b1051eaf832823cfc4c6f1dcdbafd81e37918e6f874ef8b)),pk(03186b483d056a033826ae73d88f732985c4ccb1f32ba35f4b4cc47fdcf04aa6eb)),pk(03079264c4b4bfcd7fe3a7b7b92b6c439f3a5b3abcd29189bf7b54d781ff03d722)),pk(03df9d70a6b9876ce544c98561f4be4f725442e6d2b737d9c91a8321724ce0963f)),pk(0270e6b44a2ac6083ab673bacb5cb7ca554b795b416e702c1c980bb7b87c78b8e9)),pk(025edd5cc23c51e87a497ca815d5dce0f8ab52554f849ed8995de64c5f34ce7143)),pk(03c00be8830995d1e44f1420dd3b90d3441fb66f6861c84a35f959c495a3be5440)),pk(02290798c2b6476830da12fe02287e9e777aa3fba1c355b17a722d362f84614fba)),pk(03a8f2c94e19d9d829ecb4b17f84f42d8c1e988d693df4a1fb659032865ff5154c)),pk(02af3c423a95d9f5b3054754efa150ac39cd29552fe360257362dfdecef4053b45)),pk(032773840fcf4e9e459c052cebbfbb7e9dfd6b072c4fbb8d476e37b93c5c478840)),pk(02766dbb24d134e745cccaa28c99bf274906bb66b26dcf98df8d2fed50d884249a)),pk(0296516a8f65774275278d0d7420a88df0ac44bd64c7bae07c3fe397c5b3300b23)),pk(0259dbf46f8c94759ba21277c33784f41645f7b44f6c596a58ce92e666191abe3e)),pk(032ddf7bbcfe114e807efe354db9f95fe70e7e555bd9114950bb3d3d987058c8ae)),pk(03f13ada95103c4537305e691e74e9a4a8dd647e711a95e73cb62dc6018cfd87b8)),pk(03e9623bbef1bf90ec0d7c744ed34659f010e6e638637161270ecd31e14f87f62e)),pk(027754b4fa0e8aced06d4167a2c59cca4cda1869c06ebadfb6488550015a88522c)),pk(03e35bc6bb1b05b2130a37c28e771c6cb4be89b397b454c8b59e594fecc13b59df)),pk(02948dcadf5990e048aa3874d46abef9d701858f95de8041d2a6828c99e2262519)),pk(0287c01e27d84da2dbd3330a7f05a58614a1ecdbabdcfccd39e5626baaf6812379)),pk(037962414450c76c1689c7b48f8202ec37fb224cf5ac0bfa1570328a8a3d7c77ab)),pk(02497c83c39c76e56d070fb906bced44099de2d0e222575f22e4749682de46eeac)),pk(033514087834964b54b15b160644d915485a16977225b8847bb0dd085137ec47ca)),pk(02a8af384e794930e63d81d3e1ef66cdab16d1cfda1b054da5f7086353a80c44fe)),pk(02d3cc30ad6b483e4bc79ce2c9dd8bc54993e947eb8df787b442943d3f7b527eaf)),pk(03eb49fd9f510469f4fe540e4b0664410f216cbbc90d97aed62af2e606110cc919)),pk(031624d84780732860ce1c78fcbfefe08b2b29823db913f6493975ba0ff4847610)),pk(03de1d35cbc6308cc5b435db84a21605a7d3a6172d6511c68bf6639d49c8704818)),pk(03733ce80da955a8a26902c95633e62a985192474b5af207da6df7b4fd5fc61cd4)),pk(0284df2e6e5e84cdff24120ca18648961ac134bcd7d6f35919bf6dcd5710e682f2)),pk(0315d9441254945064cf1a1c33bbd3b49f8966c5092171e699ef258dfab81c045c)),pk(033f0e80e574456d8f8fa64e044b2eb72ea22eb53fe1efe3a443933aca7f8cb0e3)),pk(03a1d0fcf2ec9de675b612136e5ce70d271c21417c9d2b8aaaac138599d0717940)),pk(024752f8548620831139bf1c39d65f194d191110fd2e9122abd637ab63ef91e5b4)),pk(02e22fbe15c0af8ccc5780c0735f84dbe9a790badee8245c06c7ca37331cb36980)),pk(02ed3bace23c5e17652e174c835fb72bf53ee306b3406a26890221b4cef7500f88)),pk(02311091dd9860e8e20ee13473c1155f5f69635e394704eaa74009452246cfa9b3)),pk(023049f7ffc71d744bd9bed6f42dc6a28974e3a1b9d30671f800e5d46389103c7e)),pk(0234c1fd04d301be89b31c0442d3e6ac24883928b45a9340781867d4232ec2dbdf)),pk(021880c9ad32fbb07e1fb52a688d9d6fe6db0df90ecd4c9483203f636ee00926dc)),pk(03f219ea5d6b54701c1c14de5b557eb42a8d13f3abbcd08affcc2a5e6b049b8d63)),pk(031fc757d383e4250772310db34c1e79f3888043b17bcbe91490c7f04f8accb725)),pk(03d7b8740f74a8fbaab1f683db8f45de26543a5490bca627087236912469a0b448)),pk(037e660beda020e9cc20391cef85374576853b0f22b8925d5d81c5845bb834c21e)),pk(0332d31c222f8f6f0ef86f7c98d3a3335ead5bcd32abdd94289fe4d3091aa824bf)),pk(033bb9aec1f1eb9ec7fa735fc4fcd0ab7c7b00f024a9728087f745ddaa42583d11)),pk(027461f371914ab32671045a155d9831ea8793d77cd59592c4340f86cbc18347b5)),pk(02bc82dd73e5161dba0884a36f2080d682ffc274bf62fca8f9eb0aadf82a8d733c)),pk(02ee079adb1df1860074356a25aa38206a6d716b2c3e67453d287698bad7b2b2d6)),pk(02b74f0c165b4a943593cc339096d66ad588d6b130b16695e5bd95ec557a93eab5)),pk(0316ec93e447ec83f0467b18302ee620f7e65de331874c9dc72bfd8616ba9da6b5)),pk(03fc6040fe245682cdf81eee193a3af355ef6cc374ce1438469306fe7f8957f489)),pk(02eaa5f980c245f6f038978290afa70b6bd8855897f98b6aa485b96065d537bd99)),pk(02a7c0ea7395d8785253de84833ccffdb31dc81f9c32bb84a53ec1775d0fadae00)),pk(02078c9407544ac132692ee1910a02439958ae04877151342ea96c4b6b35a49f51)),pk(02dd5ba67cfb807824bd3ff25e9d1667fa89e7020e8e0becb79caa00f574adc826)),pk(02494f4be219a1a77016dcd838431aea0001cdc8ae7a6fc688726578d9702857a5)),pk(02139ae46a1133f1f9d23f25efba0f6dd87bf7ddaf568a5fb9e0a3bfda73176237)),pk(03a598a8030da6d86c6bc7f2f5144ea549d28211ea58faa70ebf4c1e665c1fe9b5)),pk(02f90b89d53bdc724a685bb8c12419bbf5b8ffea50ec08422a9a7b09b1029471e3)),pk(03c41916365abb2b5d09192f5f2dbeafec208f020f12570a184dbadc3e58595997)),pk(026df7b5a7a126a6112e1e0ba01ad1a0f89f055dd3c1c7e5336938ad32c494b319)),pk(02841d6063a586fa475a724604da03bc5b92a2e0d2e0a36acfe4c73a5514742881)),pk(0234ff3be4033f7a06696c3d09f7d1671cbcf55cd700535655647077456769a24e)),pk(035e95bb399a6971d376026947f89bde2f282b33810928be4ded112ac4d70e20d5)),pk(039dda94404337db1474e67f1d7052f398a0e70ed205c5e94d6e731b06c6f51cd8)),pk(0236e4641a53948fd476c39f8a99fd974e5ec07564b5315d8bf99471bca0ef2f66)),pk(028a93046d22897b40361bcd154301ff4b7ed3c170c45e44d445d2ae2ae38947d7)),pk(020336581ea7bfbbb290c191a2f507a41cf5643842170e914faeab27c2c579f726)),pk(02d5f66020bdd383a875e8b46dc5a91925f17d3f1f5eeafb4e2b1f39bec59b9618)),pk(028ab89816dadfd6b6a1f2634fcf00ec8403781025ed6890c4849742706bd43ede)),pk(03f25f6e271e231dfd5f5f8d2aaf30fc6dafe835feca1575e93f667f69d0d97018)),pk(021e33f1a746c9c5778133344d9299fcaa20b0938e8acff2544bb40284b8c5fb94)),pk(020f1dd626b97220199541a803535b09dc6f0328bc6eda337b5ea937913ccf1095)),pk(0385b7c1dcb3cec1b7ee7f30ded79dd20a0ed1f4cc18cbcfcfa410361fd8f08f31)),pk(039358bf4e626ce79a888c0a54ce408b48fa4acb89cd7d9487b92d2f1129289fa9)),pk(0329df9fbd8d9e46509275f4b125d6d45d7fbe9a3b878a7af872a2800661ac5f51)),pk(02ef68a2c7ad33241d6adc31b4e7830036b5e571af914fe014c9f81b66ff472adb)),pk(02a0b1cae06b0a847a3fea6e671aaf8adfdfe58ca2f768105c8082b2e449fce252)),pk(028e3d1248c7657211d20291ce1798f490743f1bc852858e32d7efe2315fbc7671)),pk(0204e8ceafb9b3e9a136dc7ff67e840295b499dfb3b2133e4ba113f2e4c0e121e5)),pk(037b732af34077f33108a0e679d9eea6a81cf5e707c8f3050d5dfb298429952152)),pk(03d24a44e047e19b6f5afb81c7ca2f69080a5076689a010919f42725c2b789a33b)),pk(03ecc99b0cf89ef1412718197ef17ed0876f02c24fbb10ae46df051b79da14b6c3)),pk(03ea01606a7a6c9cdd249fdfcfacb99584001edd28abbab77b5104e98e8e3b35d4)),pk(031f6014569d1203ae0c128ac00a41097609b16386bde7f857b908ea95e5eebbef)),pk(02af8addbf2b661c8a6c6328655eb96651252007d8c5ea31be4ad196de8ce2131f)),pk(03e19d8d416b28eeefb603b7d5153773222f127b76ff24d7b8419eb6997dee8d17)),pk(0200e3ae1974566ca06cc516d47e0fb165a674a3dabcfca15e722f0e3450f45889)),pk(029ea5c218b98cc990bf7257c3b588e75b4a03a9c0107e1d638e7b0a261f997190)),pk(02591ee355313d99721cf6993ffed1e3e301993ff3ed258802075ea8ced397e246)),pk(03a8be67d40815919c5f13c7cc84c166d55e603eb6750077acd7a17c18f15a3699)),pk(0211396d55fda54c49f19aa97318d8da61fa8584e47b084945077cf03255b52984)),pk(03915050c28c39ebfd36ecbe198e90fe71a53573822a6e94b30f734afb0a29f390)),pk(033c5d2a1ba39c5a1790000738c9e0c40b8dcdfd5468754b6405540157e017aa7a)),pk(03308913a27a52d9222bc776838f73f576a4d047122a9b184b05ec32ad51b03f6c)),pk(03cc8704b8a60a0defa3a99a7299f2e9c3fbc395afb04ac078425ef8a1793cc030)),pk(03fbaf4eb5bdf8fe9397a3b8bc51bfa27183ff4ac34a966eb822109700780a7943)),pk(02c533e4f7ea8555aacd9777ac5cad29b97dd4defccc53ee7ea204119b2889b197)),pk(03f62885ce55ff7be291dd96717159e106b77beeb53920db82a218a7bda715e7ba)),pk(020c14f8f2ccb27d6f109f6d08d03cc96a69ba8c34eec07bbcf566d48e33da6593)),pk(02a5822bd06c673e21b41f30c4efd7c49109f00c12cdc12c5156835fe50c9d3205)),pk(03a6cbc3046bc6a450bac24789fa17115a4c9739ed75f8f21ce441f72e0b90e6ef)),pk(03328ba6c70c404497a663505914704a7b695331569d729745baa1f1cdcbf2d359)),pk(02347d6d9a02c48927ebfb86c1359b1caf130a3c0267d11ce6344b39f99d43cc38)),pk(02f9502d540ca7d5ab09ea89e83889fa4bcd0b27f7eec5752f4fa07b1b19160f3b)),pk(02da6545d2181db8d983f7dcb375ef5866d47c67b1bf31c8cf855ef7437b72656a)),pk(02c4f942ea2b52a8cef06e95d0665a4073d9c41961f668fdb68464ab4070ab2b7a)),pk(02c40747cc9d012cb1a13b8148309c6de7ec25d6945d657146b9d5994b8feb1111)),pk(0269317694d15b16c548fc20ec98691ed6838230a85b762e92fa4f1bc1da40f082)),pk(034e42c8ec82c99798ccf3a610be870e78338c7f713348bd34c8203ef4037f3502)),pk(0378a891aa2234a498896a193ed088a2b68fcae82788f506a0f3287432beb31db2)),pk(033775ab7089bc6af823aba2e1af70b236d251cadb0c86743287522a1b3b0dedea)),pk(03192e787021b1e83ead4572c55b488607dcb079365966c5437632c5c33e4cb721)),pk(03cee31cbf7e34ec379d94fb814d3d775ad954595d1314ba8846959e3e82f74e26)),pk(038267f5f35e78f30dcf58f7bc65a2514d0c8c0ac8d1f6b99374818ee88f5e524f)),pk(02b4f9eaea09b6917619f6ea6a4eb5464efddb58fd45b1ebefcdc1a01d08b47986)),pk(02a076cacf92cc467c94ed72da5b9961395dacf1a224b157559169e4ea2b19a602)),pk(02d4263dfc3d2df923a0179a48966d30ce84e2515afc3dccc1b77907792ebcc60e)),pk(034265bbaf8d442ac5162aaae1836a64aab9e912769ef3393f395681815f5be39c)),pk(0348457524820fa65a4f8d35eb6930857c0032acc0a4a2de422233eeda897612c4)),pk(033e805fa563758c7b2187ee0a7a4e2503495f3686c9351822b054d3844f1724c1)),pk(03dfeeef1881101f2cb11644f3a2afdfc2045e19919152923f367a1767c11cceda)),pk(03296eef5bdd483af1ec401a7fa0f5db8b75a7adb1b159624075f3d8ef294845f3)),pk(026d7ef6b17543f8373c573f44e1f389835d89bcbc6062ced36c82df83b8fae859)),pk(0232c001f5785688f62416f0ae4ed51ec85d8db3a2dc56b8b1e63065b098bbae2e)),pk(03e75605d59102a5a2684500d3b991f2e3f3c88b93225547035af25af66e04541f)),pk(02d7a0da58d01dc635812ddf64d99c9aeae783c797d7cd204ec7b750f733ce1752)),pk(02eb98660f4c4dfaa06a2be453d5020bc99a0c2e60abe388457dd43fefb1ed620c)),pk(03838ed2eb98f466853b4ab50f6b1030ce1d8742af3a39049ad0f9cf8031bdc863)),pk(0313e87b027d8514d35939f2e6892b19922154596941888336dc3563e3b8dba942)),pk(0221c76dbf7a8d075a88b426221796035964f08ea3aa575d8f5f2d7ca5d86e196e)),pk(02ee163026e9fd6fe017c38f06a5be6fc125424b371ce2708e7bf4491691e5764a)),pk(0293e651f2d3ac2659e38b59ba5857b83cfe3f31125f3bc5bc6a0c81bd90877ed5)),pk(03b268f5ef9ad51e4d78de3a750c2dc89b1e626d43505867999932e5db33af3d80)),pk(03cd5a3be41717d65683fe7a9de8ae5b4b8feced69f26a8b55eeefbcc2e74b75fb)),pk(02ff07f3118a9df035e9fad85eb6c7bfe42b02f01ca99ceea3bf7ffdba93c4750d)),pk(036c0d1f1784e47ff04108c1d9049df6b3658aa6490ef4ef1ac1e4dbfd90ac0427)),pk(028d8b9855c7c052a34146fd20ffb658bea4b9f69e0d825ebec16e8c3ce2b526a1)),pk(03da9b9e9ab699c11cef8b8cdbd452f7c5ca6dd9da7a9efa19acc0a89758554b6c)),pk(0352db0b5384dfbf05bfa9d472d7ae26dfe4b851ceca91b1eba54263180da32b63)),pk(0352520de6009c7e49f080ea4c21a2ade2d2f58220c30a7cb056fc4c098ad30369)),pk(03e62f9490d3d51da6395efd24e80919cc7d0f29c3f3fa48c6fff543becbd43352)),pk(027d86781855db1b17d7ce3765816076eba7163cb9fba082bb65348f778db0e595)),pk(027f30ea2476b399b4957509c88f77d0191afa2ff5cb7b14fd6d8e7d65aaab1193)),pk(0359ae134c1a41cfee81c5c2cd51ac727b4e7759552d729e07b25031df15661815)),pk(025098ff1e1d9f14fb46a210fada6c903fef0fb7b4a1dd1d9ac60a0361800b7a00)),pk(03f4a0caad9ad209925131b1389effbbd28615402eb31f2c082cf6531fd68befd5)),pk(0232b78c7de9ee512a72895be6b9cbefa6e2f3c4ccce445c96b9f2c81e2778ad58)),pk(02b40226a37a1a586d0b360ad75ee73fabac67947361320882a8f9e0cfb9746ecc)),pk(02e2cb74fddc8e9fbcd076eef2a7c72b0ce37d50f08269dfc074b581550547a4f7)),pk(0354bebc996f6c2b7c52ac321ea930afa666c2f828ca99facc577e0ffa43b4f3bc)),pk(038438447566d4d7bedadc299496ab357426009a35f235cb141be0d99cd10ae3a8)),pk(02cea8d97ae24caebb2bba4eff99c743dccac732be31e1b61434d667b8fad96201)),pk(034162d488b89402039b584c6fc6c308870587d9c46f660b878ab65c82c711d67e)),pk(034b24649ac96f264fd12ef9ca0a34b068f84b6f6249ae3d7dfc9caa19ff32151e)),pk(023fad3fa84caf0f34f0f89bfd2dcf54fc175d767aec3e50684f3ba4a4bf5f683d)),pk(02bdc6c1b0f061c563243061575dc28b48a562847bec1b88b6f600bbde5b2c74a4)),pk(03674f2600a3007a00568c1a7ce05d0816c1fb84bf1370798f1c69532faeb1a86b)),pk(0308bc89c2f919ed158885c35600844d49890905c79b357322609c45706ce6b514)),pk(03d32f4da54ade74abb81b815ad1fb3b263d82d6c692714bcff87d29bd5ee9f08f)),pk(02714651a9cb4af14c78ac98661e39723d234d56537053d0140f08670f188ce2bc)),pk(0330e4e670435385556e593657135845d36fbb6931f72b08cb1ed954f1e3ce3ff6)),pk(027e62469c0893fc1661fa0449250cd2a57558b9e8d46130c125149eed98fe1249)),pk(02be2062003c51cc3004682904330e4dee7f3dcd10b01e580bf1971b04d4cad297)),pk(020639863c5cf03696867960f4f378473fafddfed53ea145226b51046bf16e839b)),pk(0293144423ace3451ed29e0fb9ac2af211cb6e84a601df5993c419859fff5df04a)),pk(037d54261d569c7330a5b943abdd4a0d7f2fb1f35ea3adc41f422049a122517961)),pk(03b015f8044f5fcbdcf21ca26d6c34fb8197829205c7b7d2a7cb66418c157b112c)),pk(03b35511d67e63fa6552db740b48aba6d230c21799e65a6647a5cbfc789ef0184b)),pk(02d5e9e1da649d97d89e4868117a465a3a4f8a18de57a140d36b3f2af341a21b52)),pk(02e485be3daccabfab0e0ca7b596da918d7f0107d535274c949683baab330bff95)),pk(02d3ae41047dd7ca065dbf8ed77b992439983005cd72e16d6f996a5316d36966bb)),pk(030659214ac1a1790023f53c4cf55a0a63b9e20c1151efa971215b395a558aa151)),pk(03463e2763d885f958fc66cdd22800f0a487197d0a82e377b49f80af87c897b065)),pk(02ddc5310f00582ac848494b9dc41ab08676545f84205e6a2a008fef8516060dfc)),pk(037985fdfd127c0567c6f53ec1bb63ec3158e597c40bfe747c83cddfc910641917)),pk(036a843ba43c244f89a8f86c708c25f0e14d8e2df756ef139df3ed516ed7c504ef)),pk(0274a1ad6b5f76e39db2dd249410eac7f99e74c59cb83d2d0ed5ff1543da7703e9)),pk(032e34552aa716aef75edf6a1f8a10dff8636478cbbff1713a5fc0da4813704a08)),pk(0230682a50703375f602d416664ba19b7fc9bab42c72747463a71d0896b22f6da3)),pk(0200136933174bc388a74ebd6746e13afe0eef5d66580c8e23d33464c342dc0080)),pk(039e2158f0d7c0d5f26c3791efefa79597654e7a2b2464f52b1ee6c1347769ef57)),pk(0322213b78f3dcfbdfeb76cc1731c1ba318b2b0c32f081e206f50618fa7eaf5aa3)),pk(03176e26989a43c9cfeba4029c202538c28172e566e3c4fce7322857f3be327d66)),pk(028758a9fd232f0fe9a7afc8456a40d57bc46e2a586d37641c2d6c77bcac938f93)),pk(0275d46efea3771e6e68abb89a13ad747ecf1892393dfc4f1b7004788c50374da8)),pk(0269b47c7249439d23a5f3c28db17e60da861a483939a113e2d903e0547bb26bfb)),pk(03809a20c67d64900ffb698c4c825f6d5f2310fb0451c869345b7319f645605721)),pk(035654834268843e72c300e97d5188fca2ed04459e09ca4351475a62c4bc8ade53)),pk(031b38903a43f7f114ed4500b4eac7083fdefece1cf29c63528d563446f972c180)),pk(038282263212c609d9ea2a6e3e172de238d8c39cabd5ac1ca10646e23fd5f51508)),pk(0290a80db6eb294b9eab0b4e8ddfa3efe7263458ce2d07566df4e6c58868feef23)),pk(02545f13c023715040ea7d7701363c4285552b572eda6a27a20f458aaa1bbf1433)),pk(02c2c80f844b70599812d625460f60340e3e6f36054a14546e6dc25d47376bea9b)),pk(03f27cddeea945ef4047108936b531bb68957e1dc74ca938084632645c569f8346)),pk(039cf606744cf4b5f3fdf989d3f19fb2652d00cfe1d5fcd692a323ce11a28e7553)),pk(02b54d9afb4f81394d6604467edd323c314fb004d707db9cc0623833d9037c07df)),pk(0257488fa28742c6b25a493fd6060d936ea6280b0c742005abce98f5855ad82208)),pk(024a5f2b9f56c13dc77430ee6e589c05e56b71482e30faaf96c3af58d3e8e65bc6)),pk(03f1133cbe6be8bbc8dc8df2b8d75963c2d40ed616c758cdc84edbc5eb4899447d)),pk(03630aca4d7f4e5d9288f2f14b83fec5049c05377aaad025370951b67458ef54d7)),pk(0295083e753301bd787f8989c79065bb813f3d69bff3e425050f4e04175bbe89c0)),pk(0214e333e19222ffaf7a5a04b09d46f6f182d033abe15ee1a094cd2910186a92df)),pk(021a908355cbb756755e576ed29c99af638668c7b363c8d97362100443bc5c75c6)),pk(02d1e0265aa86ae428c75f9d4d45b2b643c8245d6ffb4bbc43bd6b7cea1ad3ec49)),pk(02c5922f740bd343d5aa867308fad97f9f8a2d1f63c5f31db4f04df3bef349b648)),pk(03a83d1893ba454e96c9c91effca154cde3ff705cf3d8eb91010758152439f943f)),pk(0264e1b1969f9102977691a40431b0b672055dcf31163897d996434420e6c95dc9)),pk(022290006b8d17b03cfe370eeb9075043ec818a14cee53f767d44a3a5d1fb1dfa8)),pk(03033b2e76687744ed6c521bad3333dd37c602f8a7549e9ce7808fb7ea07ce08de)),pk(020bbba8d764098dc402ca9a53d9d22580a5a4f8a80adcdb140225a6e483cf4b80)),pk(0220f18f4c866d8a1cc2a3103317b4ac3189fbf30ff294a75c951473be45e4f294)),pk(02aa336dda311186a2a8dfaa5328fffedffca6476eed1fd8d69fbf74b955b3edc6)),pk(024d1623c944c9c716a0eb4c685e2a8b9d2df3465354643befd1444176d7b69a8b)),pk(020f66dc33e335abc9a7c06f71ad2c0db65d5ac4b6f46d2dad9465e6a4ac04dc3f)),pk(03a901b0dbe8ab292d280d6b36858947854faad0a4dd0da7e2d4ad0ff53db079e0)),pk(03bb8a643d0f0c3991efdb401c11354c5e54f28fa8f3f367e3ef5f2776b40cbed5)),pk(037e0af07130218ffd50bd66f4484645b12f42a24f7c80889b3031c9a6ebfc9a70)),pk(02fe330b776c5f5c95b8eb0201cecc40e57353c30a84f9fde9fb37d7c0fa4753a8)),pk(037ba8187e1a7b25a2c185d335440a9038b47f0528546e9da4ef82aab05aebf20d)),pk(024b8b2d95c98777ba4663785ce387c4ac220c57cb0d48496c241dd1f60f2ce57b)),pk(028c050fc34d83b279b6000816e18fca389767b7960e92677255b84a39d93a6807)),pk(030b07d3e8dbbe686e5e1637258402cac30e1e4f29fdf154f7bf008c5f9969da10)),pk(0253b7849a78e4df8625860583a52499489d7201a2cbf506202a7b8b1bc99c2ec9)),pk(023f6841c0aa49e8f42893f416eb820836881b6842b2da753f890a71cef93cb107)),pk(029bdf9e67a5d0c9956a075a010fe762beb633500431dee78efebc527e53313b33)),pk(03261923949e9661b55edf6d2fca4b15f91b92cc919c7f24e0ac1c2fc929010467)),pk(037caa72b37a8ab3bd0bac031a47606f8917d9f42c6ec2d2fb429fd9904a381f34)),pk(02b1d6ff90f1776329c097793d9116ce71cc3cf4ce06a9402b2ae7f6cb96e73ce9)),pk(032ef29b9f0982797579c0295fc3f48db7925d62c75532493dde16b97e3993d81a)),pk(03f0d94b756288b707dad8e169c06514f03d7ceb47ea8d3ae9ebe186694c574c92)),pk(02df157cad95b07875573c1860ae5d02c64029e952ec354e6a9e5c34be97317ff8)),pk(036abd4d9333bfafbb6fa8ad52c3b042faf49cfb56bd9452b315d53b8b91afeb7c)),pk(02dd55c150a29ca526b6182e643b9eb544e651d236b71920e7b15a987016454b1d)),pk(0385a7b790fc9d962493788317e4874a4ab07f1e9c78c773c47f2f6c96df756f05)),pk(0316886cf46ed42c7919147763063d3256c4d5d39387f0172325b9e4b898227f27)),pk(03654f313a31153e076e4e3f391d9fddcd9d3bce6705a8a806cfaaeb03678dfdc7)),pk(036ff180fcdaa3061808e8b306d6f0acff27968c22484ff45e56aeaa7b2b60732f)),pk(02f9d8df5e84d139b79741bbeca9aeedc02ce7eccf5ef163328bc63d79ece7a90c)),pk(0303ea4511a00dc2a03eb4f51f40ee677caa912b5539f685c4f8bcc8eadc395e36)),pk(0286cb288be8f7c5ebf3da1e01e00eae28c95226709bc0f32b057092c2e810feaf)),pk(030b82cd70dc3de9eab38742d8f32dfb8d53e4150a835e54b63c7cca20f253081d)),pk(0272e8d1d7b3a6df2bea4f47738b8e383dd074c5a950068469bfbde332851adf4b)),pk(02fe2fc3e00074874584ee23bf105a69a606d056f017327d49b7b38b57a196c77f)),pk(03561b1c96e5af2704858be8e17a4207c8cf45f67f0004633bc7de6a136a109f76)),pk(0204b90176cdaa369347e8778b12db9d6ee8b0011446ea35ec845dbf574bb7858b)),pk(03e19b94787546d4862031e39c810f81a2d0172be8cb2e3bfcc7ac53b7e81dfb49)),pk(0335f382511d34600b4b8c86a9f0dbc9eddefc4272f59528a0cd3ec10a5944c6d2)),pk(032f19cd628cd13cfcf6fb17a6299ed421d57454b00d23fce0bd0cf968ae813458)),pk(021d74b2970311b7ffa1027e26587d3f5be1d0e9ac3f0111cdf3cc2371722cb94a)),pk(0313597010dfab0f823472adc69ce9c2d382d302e24c43e22a371b37e58a69fccb)),pk(0250a094f309c6f9560b020737b9ec722e4f75d1b7c41593e6f934a68a98450428)),pk(02e290678cbf2a518f1f9294d456849c86d2fb805d77a00ec292f44930ae3ccdfe)),pk(029b65bb812129157cdfecf12e275ec38c282dbcd914b4810599b0a6d627c63db7)),pk(03fe1c5d4876b17caab8a65ca77c422ddab36248acde3cb42741a9d2dab3eba32e)),pk(038b4544fc1fdfa06e456c1115a1dc831c85e7f1c5e620eca51c20802d36a4bc6b)),pk(036c7630c50231b40eece52a94195712d6132d0676311a594506b2168fe82d6c03)),pk(026c709880b959eb7c5179b29cc5578fdc6cb2ae13ddcede29d5f81d95de0ab4aa)),pk(03238e918ae286a80be7d0950e536a1e25b98f917c524b4f8b8f3f350f48e6014f)),pk(0377760b5137ba6a7195d891f794a087a076fc9d67802b81e7085b56773d537806)),pk(03e4b65a7cff579e46e341c05fc609fd522a2f5b2f968d133148f3d67e59663767)),pk(021a8bd7836a0b0c82e9a904a8a8c91a67e23cd4f8efd625d0df4c426e7e163102)),pk(03f5eaf4de39d745e72466597572a907ba5765395df8ed19d1457051461540ed0b)),pk(02fe217db659079913fb1e453ed24d91d6a3fb3099e69471d753db5390864abc30)),pk(02124c5c798edff99abd3f3a5182745060baa045e73dab0980889c71e4fb8e3f52)),pk(022504d63754afd5ebc38f58b65ead696d07e3abd748cb6c5f212aed49f5b33b91)),pk(020d2a035b8715bfdbaf586b9c402003e95dd189beb02fdfd3c55303dc864f625a)),pk(030b06f702f47b22d789a9bd3f687105c36160abbf5cc8976b7fbddcafdb197b5c)),pk(02065210379a8f4d1a8d9b9103361874b36c39aa35a87e2cc1876745f9a3372a42)),pk(03803b203bb31f9cf94034eeb931b54480a6f3f99ebd23d0acbc2128a60d044e23)),pk(030429053001eec810b1d22b59a2b999628cb29372e5799f7688236c81fdbc33b0)),pk(02266a9cb4c5f5ceadbb50e5bda03a7312e52de1de8e95a8dcd57289fe0302749a)),pk(03abf10b2d598ff1d9cb71534a9ad047985e190d948ed2d7bb7aea9ded421e0b20)),pk(02fd8a9d95d80c7ad52599a7ab98163df364c4c141e9abea355d7360bcf84eba94)),pk(02a8ec150dde7feb5fbcaebd264b611f92f85699f1c9e1a96cef7c62a092b55825)),pk(02a7322df309f28f2359fc339a8b2c80be6e84acc5b7b0b8f8f2cb6f26f9db0a7d)),pk(0306522b91f2e518e515462823821bb9cba57451495c25e9c4ae26074eab7c9c54)),pk(0282a8c10f336a664963a104ddbf7f0f18bd4c461aea569ffc82c3c7e4cb052d36)),pk(03e5e2f23f7f3ebbd6be1d440de92f23f532c79f178cafef8c8c77c15df280714a)),pk(039b50d1b68e3bf795007cd12f05a60c266c4ef2b75ba5c516c54784a94f15d6df)),pk(0270d4ed5aa6bc59c5bb2e268f07c0bd6e13929c030ac2b7ecc98334d798d27e79)),pk(023f9083ddc8b423fe7de3a82281d3056ab8dcb9d7ee82cb806718595fbae08d32)),pk(03695a4bc690d371e49937dbf1ea9065942f4e021adc54c87991fc66fc195742b6)),pk(02c75c85c1ee17c1a256eff6bd592666cbc923170659d50bfadbd1074ef2167faf)),pk(0256276403f3a5f577cb7e7aae006316d1346d804976604ea4ed181dfcb8155102)),pk(03c5341feaf8a0f5d3b4d0cf0d2f7aad7c60ea8e2b3d4b7fb95c68d57698656045)),pk(029038876f21c3bc14111d5f6a04749d0734e40a537d398c680809355f764cf1ba)),pk(0283acda3e2a8997e0d52bd4c68705dd22220852b7752d67fd8967a03260c2d89b)),pk(035d8c91c5507b7af561d5209abd231bdb31b94960db0898a7ed2bd22ed44f7809)),pk(025b8191468b2990745b9c4164e29d594cf1c0d5716c5d39625bd279b30025237b)),pk(02588f275c9a4654578c61e798442e5453cd4f6d703d538acf83737d56b9b55983)),pk(0364778122214e38eff8041796166104e732f5f664d38d77219b89045e2c3b0e6c)),pk(033f44923b0693b954aee312306c994dc88703b423b93e08294968d01879f05627)),pk(02ed4d826afe5762f4795099099aee86642b475a9d6da1017c43d0cb9f1af12323)),pk(03953365cf99092ecdb2f9a546e05cb0119cb012d173167742943296b9aebb30d8)),pk(0338b42924419aecc3acd6f551346fd61a4d82ac2b55f7afe97a06eb40cd109c4a)),pk(03d5fb3642dd34f7713ec01a72a2b48542662967e3b8fd89f6a675756d4c913fdc)),pk(02c3cad4a8d8bb94a7b434cf70183e8615bb2a8f6224f216e3446ac2e982138911)),pk(03a5b5088c01df0902b8346dd2e5023d25a19cb524734664e100152f2aa8e736f1)),pk(032d408ff4d3d236fd54fae40dce3ea9ecd9212e5736591a9e55588e4a54bd6538)),pk(036e087ac61ce913827c75ab4fd13f60b161b371d8c145f818ce799f5377539d77)),pk(02ee7adf6d247f25fb76e90cf813f888ebd67423a3a3c6fdaebafb7eaa7a33c854)),pk(03864e30ec83f1ab4985625011814927d897b2f0ce99495d2c38fe94479a207310)),pk(032f9457c8a9ffaca13d91151dc4c5e89ddd5d37a37c9a864b7c811f3e01144b34)),pk(0207a594943852c33c49cc68cea542f71cf13ab5402c8fbe9b572e051373d72229)),pk(03d3f332b8a0f115821ce3478cefe18de360120483ef531c277b30c46eb7fec294)),pk(03ee9bf5db6bf58d83b170355da78b00ce07bfaa6a000cc126cd34ecdb324e4279)),pk(02183408d338b05aad3521fcd86ef36dd75f3ddb8666b52f7e9a4cdf1f8e152b91)),pk(03368b590c7040ee625679e2a39c61aebef237fd4928da8d6dc75991fd328618a3)),pk(02283fec5db1145e53ba8f1f0ff9cf89a721faffd6c25346863d3956095f40374e)),pk(03ef98e34f8fd7a186ab459017757f75324b7f34db23ef10444a5b728ba70076c4)),pk(030ce7570a4f943cfa413bd249d8e7dbfcebc73579770fd6daf54a0dfbdd52fa62)),pk(024b5bfce9275226a6f869cc90d81d9371592496fbc8b1510e89c56579b464b617)),pk(027e9c4f19c8f4ec3f1269f648cd919525df79031574cbeb1537794a4c838fd470)),pk(03942139d4c45b0ee4237dff76a505bb63ad78857d654d2c5f4fd7674b83411328)),pk(02e2a9bbe60d5d5bfea7c7f919df2309f90ba04f4c722a3ec23bf451b464cb001b)),pk(02886eb2e66be68b8835dde695b48cfd5cddf755b146a9726629ba933572aca3aa)),pk(03504512a43e17ef50e43bf37d42a94990f55e641b1558c265e709900275271012)),pk(023443a7067a08cd3e10d3aad6a78ed1afb5714e7796eb9f84a908b701b5476085)),pk(0381d1f013a6bb325f4b2d1d51ba72c721859945d8a17b3411cd5cbe87285f850d)),pk(03d5b0ac978945c962e1a27fbd9d1b0c886e09b46aac3b7de3810ae9a13952ee2c)),pk(035b66c2dfc1d2826618a872767e66c33dd90dd51414a3b87ca733383d1d895022)),pk(0394d09a21e27ec50f103c0fb2aa1d36c0606f4c6608f96ba7f6d3ab8c560e3564)),pk(03aeb5f70e98ec5e38dbd2d544bdbff8ab99b583d9af58c597afaf868820381186)),pk(0360f74920a550b0bed80d8cd566f2213f8ea83e7d8745b6bdc935d52c94388352)),pk(020b289effe841943b84761e3c67a9c02a557679ca76ad753a707a98212505052e)),pk(03481ae134ba75525e901c75bf0ad6c84ae8f67752d830ca2649a9f8ee55640f0d)),pk(02abae39458b12199e6b0c8360cfd282883f585917e44e1200f81bd356f619291c)),pk(03794a1c1a306d944ed1c2a6a6cee4ac399682d35086af5d5f0443b35835e2ec00)),pk(024a9583a6485b5a5a81ac224a518eb29d1e0f658c8d91b0139419c80955fbacaa)),pk(0297a2b6ff47c3de75505232b12c82984b1980ddfc201ca2d2bf30da3c728c7ea9)),pk(02d52f630edba6f7cb65fcf46544ab0d9eea236ac1460f17ae3a21010210ebc169)),pk(023824b450c286bcf892e54a2577cc170a7f80f94a517484cbc74a8a45238f4b32)),pk(030bdc523782c75858f5c50fc052e4c1e9c74a2a6335bca9bf8d10e1209add6a4d)),pk(02cfd70505faacd3caf4419000bf4b6ab9e7dc2e4bcf43bbcaa550839cf4713b42)))";

        Desc::from_str(s).unwrap();
    }
}
