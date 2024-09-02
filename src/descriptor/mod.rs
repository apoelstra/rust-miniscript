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
}
