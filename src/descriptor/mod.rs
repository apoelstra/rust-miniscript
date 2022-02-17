// Miniscript
// Written in 2018 by
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

use std::{collections::HashMap, sync::Arc};
use std::{
    fmt,
    str::{self, FromStr},
};

use bitcoin::blockdata::witness::Witness;
use bitcoin::{self, secp256k1, Script};

use self::checksum::verify_checksum;
use expression;
use miniscript;
use miniscript::{Legacy, Miniscript, Segwitv0};
use {
    BareCtx, Error, ForEach, ForEachKey, MiniscriptKey, Satisfier, ToPublicKey, TranslatePk,
    TranslatePk2,
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

mod checksum;
mod key;

pub use self::key::{
    ConversionError, DescriptorKeyParseError, DescriptorPublicKey, DescriptorSecretKey,
    DescriptorSinglePriv, DescriptorSinglePub, DescriptorXKey, InnerXKey, SinglePubKey, Wildcard,
};

/// Alias type for a map of public key to secret key
///
/// This map is returned whenever a descriptor that contains secrets is parsed using
/// [`Descriptor::parse_descriptor`], since the descriptor will always only contain
/// public keys. This map allows looking up the corresponding secret key given a
/// public key from the descriptor.
pub type KeyMap = HashMap<DescriptorPublicKey, DescriptorSecretKey>;

/// A general trait for Bitcoin descriptor.
/// Offers function for witness cost estimation, script pubkey creation
/// satisfaction using the [Satisfier] trait.
// Unfortunately, the translation function cannot be added to trait
// because of traits cannot know underlying generic of Self.
// Thus, we must implement additional trait for translate function
pub trait DescriptorTrait<Pk: MiniscriptKey> {
    /// Whether the descriptor is safe
    /// Checks whether all the spend paths in the descriptor are possible
    /// on the bitcoin network under the current standardness and consensus rules
    /// Also checks whether the descriptor requires signauture on all spend paths
    /// And whether the script is malleable.
    /// In general, all the guarantees of miniscript hold only for safe scripts.
    /// All the analysis guarantees of miniscript only hold safe scripts.
    /// The signer may not be able to find satisfactions even if one exists
    fn sanity_check(&self) -> Result<(), Error>;

    /// Computes the Bitcoin address of the descriptor, if one exists
    /// Some descriptors like pk() don't have any address.
    /// Errors:
    /// - On raw/bare descriptors that don't have any address
    /// - In Tr descriptors where the precomputed spend data is not available
    fn address(&self, network: bitcoin::Network) -> Result<bitcoin::Address, Error>
    where
        Pk: ToPublicKey;

    /// Computes the scriptpubkey of the descriptor
    fn script_pubkey(&self) -> Script
    where
        Pk: ToPublicKey;

    /// Computes the scriptSig that will be in place for an unsigned
    /// input spending an output with this descriptor. For pre-segwit
    /// descriptors, which use the scriptSig for signatures, this
    /// returns the empty script.
    ///
    /// This is used in Segwit transactions to produce an unsigned
    /// transaction whose txid will not change during signing (since
    /// only the witness data will change).
    fn unsigned_script_sig(&self) -> Script
    where
        Pk: ToPublicKey;

    /// Computes the "witness script" of the descriptor, i.e. the underlying
    /// script before any hashing is done. For `Bare`, `Pkh` and `Wpkh` this
    /// is the scriptPubkey; for `ShWpkh` and `Sh` this is the redeemScript;
    /// for the others it is the witness script.
    /// For `Tr` descriptors, this will error as there is no underlying script
    fn explicit_script(&self) -> Result<Script, Error>
    where
        Pk: ToPublicKey;

    /// Returns satisfying non-malleable witness and scriptSig with minimum weight to spend an
    /// output controlled by the given descriptor if it possible to
    /// construct one using the satisfier S.
    fn get_satisfaction<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, Script), Error>
    where
        Pk: ToPublicKey,
        S: Satisfier<Pk>;

    /// Returns satisfying, possibly malleable witness and scriptSig to spend an
    /// output controlled by the given descriptor if it possible to
    /// construct one using the satisfier S.
    fn get_satisfaction_mall<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, Script), Error>
    where
        Pk: ToPublicKey,
        S: Satisfier<Pk>;

    /// Attempts to produce a non-malleable satisfying witness and scriptSig to spend an
    /// output controlled by the given descriptor; add the data to a given
    /// `TxIn` output.
    fn satisfy<S>(&self, txin: &mut bitcoin::TxIn, satisfier: S) -> Result<(), Error>
    where
        Pk: ToPublicKey,
        S: Satisfier<Pk>,
    {
        // easy default implementation
        let (witness, script_sig) = self.get_satisfaction(satisfier)?;
        txin.witness = Witness::from_vec(witness);
        txin.script_sig = script_sig;
        Ok(())
    }

    /// Computes an upper bound on the weight of a satisfying witness to the
    /// transaction. Assumes all ec-signatures are 73 bytes, including push opcode
    /// and sighash suffix. Includes the weight of the VarInts encoding the
    /// scriptSig and witness stack length.
    /// Returns Error when the descriptor is impossible to safisfy (ex: sh(OP_FALSE))
    fn max_satisfaction_weight(&self) -> Result<usize, Error>;

    /// Get the `scriptCode` of a transaction output.
    ///
    /// The `scriptCode` is the Script of the previous transaction output being serialized in the
    /// sighash when evaluating a `CHECKSIG` & co. OP code.
    /// Errors:
    /// - When the descriptor is Tr
    fn script_code(&self) -> Result<Script, Error>
    where
        Pk: ToPublicKey;
}

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

impl<Pk: MiniscriptKey> Descriptor<Pk> {
    // Keys

    /// Create a new pk descriptor
    pub fn new_pk(pk: Pk) -> Self {
        // roundabout way to constuct `c:pk_k(pk)`
        let ms: Miniscript<Pk, BareCtx> =
            Miniscript::from_ast(miniscript::decode::Terminal::Check(Arc::new(
                Miniscript::from_ast(miniscript::decode::Terminal::PkK(pk))
                    .expect("Type check cannot fail"),
            )))
            .expect("Type check cannot fail");
        Descriptor::Bare(Bare::new(ms).expect("Context checks cannot fail for p2pk"))
    }

    /// Create a new PkH descriptor
    pub fn new_pkh(pk: Pk) -> Self {
        Descriptor::Pkh(Pkh::new(pk))
    }

    /// Create a new Wpkh descriptor
    /// Will return Err if uncompressed key is used
    pub fn new_wpkh(pk: Pk) -> Result<Self, Error> {
        Ok(Descriptor::Wpkh(Wpkh::new(pk)?))
    }

    /// Create a new sh wrapped wpkh from `Pk`.
    /// Errors when uncompressed keys are supplied
    pub fn new_sh_wpkh(pk: Pk) -> Result<Self, Error> {
        Ok(Descriptor::Sh(Sh::new_wpkh(pk)?))
    }

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
}

impl<P: MiniscriptKey, Q: MiniscriptKey> TranslatePk<P, Q> for Descriptor<P> {
    type Output = Descriptor<Q>;
    /// Convert a descriptor using abstract keys to one using specific keys
    /// This will panic if translatefpk returns an uncompressed key when
    /// converting to a Segwit descriptor. To prevent this panic, ensure
    /// translatefpk returns an error in this case instead.
    fn translate_pk<Fpk, Fpkh, E>(
        &self,
        mut translatefpk: Fpk,
        mut translatefpkh: Fpkh,
    ) -> Result<Descriptor<Q>, E>
    where
        Fpk: FnMut(&P) -> Result<Q, E>,
        Fpkh: FnMut(&P::Hash) -> Result<Q::Hash, E>,
        Q: MiniscriptKey,
    {
        let desc = match *self {
            Descriptor::Bare(ref bare) => {
                Descriptor::Bare(bare.translate_pk(&mut translatefpk, &mut translatefpkh)?)
            }
            Descriptor::Pkh(ref pk) => {
                Descriptor::Pkh(pk.translate_pk(&mut translatefpk, &mut translatefpkh)?)
            }
            Descriptor::Wpkh(ref pk) => {
                Descriptor::Wpkh(pk.translate_pk(&mut translatefpk, &mut translatefpkh)?)
            }
            Descriptor::Sh(ref sh) => {
                Descriptor::Sh(sh.translate_pk(&mut translatefpk, &mut translatefpkh)?)
            }
            Descriptor::Wsh(ref wsh) => {
                Descriptor::Wsh(wsh.translate_pk(&mut translatefpk, &mut translatefpkh)?)
            }
            Descriptor::Tr(ref tr) => {
                Descriptor::Tr(tr.translate_pk(&mut translatefpk, &mut translatefpkh)?)
            }
        };
        Ok(desc)
    }
}

impl<Pk: MiniscriptKey> DescriptorTrait<Pk> for Descriptor<Pk> {
    /// Whether the descriptor is safe
    /// Checks whether all the spend paths in the descriptor are possible
    /// on the bitcoin network under the current standardness and consensus rules
    /// Also checks whether the descriptor requires signauture on all spend paths
    /// And whether the script is malleable.
    /// In general, all the guarantees of miniscript hold only for safe scripts.
    /// All the analysis guarantees of miniscript only hold safe scripts.
    /// The signer may not be able to find satisfactions even if one exists
    fn sanity_check(&self) -> Result<(), Error> {
        match *self {
            Descriptor::Bare(ref bare) => bare.sanity_check(),
            Descriptor::Pkh(ref pkh) => pkh.sanity_check(),
            Descriptor::Wpkh(ref wpkh) => wpkh.sanity_check(),
            Descriptor::Wsh(ref wsh) => wsh.sanity_check(),
            Descriptor::Sh(ref sh) => sh.sanity_check(),
            Descriptor::Tr(ref tr) => tr.sanity_check(),
        }
    }
    /// Computes the Bitcoin address of the descriptor, if one exists
    fn address(&self, network: bitcoin::Network) -> Result<bitcoin::Address, Error>
    where
        Pk: ToPublicKey,
    {
        match *self {
            Descriptor::Bare(ref bare) => bare.address(network),
            Descriptor::Pkh(ref pkh) => pkh.address(network),
            Descriptor::Wpkh(ref wpkh) => wpkh.address(network),
            Descriptor::Wsh(ref wsh) => wsh.address(network),
            Descriptor::Sh(ref sh) => sh.address(network),
            Descriptor::Tr(ref tr) => tr.address(network),
        }
    }

    /// Computes the scriptpubkey of the descriptor
    fn script_pubkey(&self) -> Script
    where
        Pk: ToPublicKey,
    {
        match *self {
            Descriptor::Bare(ref bare) => bare.script_pubkey(),
            Descriptor::Pkh(ref pkh) => pkh.script_pubkey(),
            Descriptor::Wpkh(ref wpkh) => wpkh.script_pubkey(),
            Descriptor::Wsh(ref wsh) => wsh.script_pubkey(),
            Descriptor::Sh(ref sh) => sh.script_pubkey(),
            Descriptor::Tr(ref tr) => tr.script_pubkey(),
        }
    }

    /// Computes the scriptSig that will be in place for an unsigned
    /// input spending an output with this descriptor. For pre-segwit
    /// descriptors, which use the scriptSig for signatures, this
    /// returns the empty script.
    ///
    /// This is used in Segwit transactions to produce an unsigned
    /// transaction whose txid will not change during signing (since
    /// only the witness data will change).
    fn unsigned_script_sig(&self) -> Script
    where
        Pk: ToPublicKey,
    {
        match *self {
            Descriptor::Bare(ref bare) => bare.unsigned_script_sig(),
            Descriptor::Pkh(ref pkh) => pkh.unsigned_script_sig(),
            Descriptor::Wpkh(ref wpkh) => wpkh.unsigned_script_sig(),
            Descriptor::Wsh(ref wsh) => wsh.unsigned_script_sig(),
            Descriptor::Sh(ref sh) => sh.unsigned_script_sig(),
            Descriptor::Tr(ref tr) => tr.unsigned_script_sig(),
        }
    }

    /// Computes the "witness script" of the descriptor, i.e. the underlying
    /// script before any hashing is done. For `Bare`, `Pkh` and `Wpkh` this
    /// is the scriptPubkey; for `ShWpkh` and `Sh` this is the redeemScript;
    /// for the others it is the witness script.
    /// Errors:
    /// - When the descriptor is Tr
    fn explicit_script(&self) -> Result<Script, Error>
    where
        Pk: ToPublicKey,
    {
        match *self {
            Descriptor::Bare(ref bare) => bare.explicit_script(),
            Descriptor::Pkh(ref pkh) => pkh.explicit_script(),
            Descriptor::Wpkh(ref wpkh) => wpkh.explicit_script(),
            Descriptor::Wsh(ref wsh) => wsh.explicit_script(),
            Descriptor::Sh(ref sh) => sh.explicit_script(),
            Descriptor::Tr(ref tr) => tr.explicit_script(),
        }
    }

    /// Returns satisfying non-malleable witness and scriptSig to spend an
    /// output controlled by the given descriptor if it possible to
    /// construct one using the satisfier S.
    fn get_satisfaction<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, Script), Error>
    where
        Pk: ToPublicKey,
        S: Satisfier<Pk>,
    {
        match *self {
            Descriptor::Bare(ref bare) => bare.get_satisfaction(satisfier),
            Descriptor::Pkh(ref pkh) => pkh.get_satisfaction(satisfier),
            Descriptor::Wpkh(ref wpkh) => wpkh.get_satisfaction(satisfier),
            Descriptor::Wsh(ref wsh) => wsh.get_satisfaction(satisfier),
            Descriptor::Sh(ref sh) => sh.get_satisfaction(satisfier),
            Descriptor::Tr(ref tr) => tr.get_satisfaction(satisfier),
        }
    }

    /// Returns a possilbly mallable satisfying non-malleable witness and scriptSig to spend an
    /// output controlled by the given descriptor if it possible to
    /// construct one using the satisfier S.
    fn get_satisfaction_mall<S>(&self, satisfier: S) -> Result<(Vec<Vec<u8>>, Script), Error>
    where
        Pk: ToPublicKey,
        S: Satisfier<Pk>,
    {
        match *self {
            Descriptor::Bare(ref bare) => bare.get_satisfaction_mall(satisfier),
            Descriptor::Pkh(ref pkh) => pkh.get_satisfaction_mall(satisfier),
            Descriptor::Wpkh(ref wpkh) => wpkh.get_satisfaction_mall(satisfier),
            Descriptor::Wsh(ref wsh) => wsh.get_satisfaction_mall(satisfier),
            Descriptor::Sh(ref sh) => sh.get_satisfaction_mall(satisfier),
            Descriptor::Tr(ref tr) => tr.get_satisfaction_mall(satisfier),
        }
    }

    /// Computes an upper bound on the weight of a satisfying witness to the
    /// transaction. Assumes all signatures are 73 bytes, including push opcode
    /// and sighash suffix. Includes the weight of the VarInts encoding the
    /// scriptSig and witness stack length.
    fn max_satisfaction_weight(&self) -> Result<usize, Error> {
        match *self {
            Descriptor::Bare(ref bare) => bare.max_satisfaction_weight(),
            Descriptor::Pkh(ref pkh) => pkh.max_satisfaction_weight(),
            Descriptor::Wpkh(ref wpkh) => wpkh.max_satisfaction_weight(),
            Descriptor::Wsh(ref wsh) => wsh.max_satisfaction_weight(),
            Descriptor::Sh(ref sh) => sh.max_satisfaction_weight(),
            Descriptor::Tr(ref tr) => tr.max_satisfaction_weight(),
        }
    }

    /// Get the `scriptCode` of a transaction output.
    ///
    /// The `scriptCode` is the Script of the previous transaction output being serialized in the
    /// sighash when evaluating a `CHECKSIG` & co. OP code.
    /// Returns Error for Tr descriptors
    fn script_code(&self) -> Result<Script, Error>
    where
        Pk: ToPublicKey,
    {
        match *self {
            Descriptor::Bare(ref bare) => bare.script_code(),
            Descriptor::Pkh(ref pkh) => pkh.script_code(),
            Descriptor::Wpkh(ref wpkh) => wpkh.script_code(),
            Descriptor::Wsh(ref wsh) => wsh.script_code(),
            Descriptor::Sh(ref sh) => sh.script_code(),
            Descriptor::Tr(ref tr) => tr.script_code(),
        }
    }
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Descriptor<Pk> {
    fn for_each_key<'a, F: FnMut(ForEach<'a, Pk>) -> bool>(&'a self, pred: F) -> bool
    where
        Pk: 'a,
        Pk::Hash: 'a,
    {
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
    pub fn is_deriveable(&self) -> bool {
        self.for_any_key(|key| key.as_key().is_deriveable())
    }

    /// Derives all wildcard keys in the descriptor using the supplied index
    ///
    /// Panics if given an index ≥ 2^31
    ///
    /// In most cases, you would want to use [`Self::derived_descriptor`] directly to obtain
    /// a [`Descriptor<bitcoin::PublicKey>`]
    pub fn derive(&self, index: u32) -> Descriptor<DescriptorPublicKey> {
        self.translate_pk2_infallible(|pk| pk.clone().derive(index))
    }

    /// Derive a [`Descriptor`] with a concrete [`bitcoin::PublicKey`] at a given index
    /// Removes all extended pubkeys and wildcards from the descriptor and only leaves
    /// concrete [`bitcoin::PublicKey`]. All [`crate::XOnlyKey`]s are converted to [`bitcoin::PublicKey`]
    /// by adding a default(0x02) y-coordinate. For [`crate::descriptor::Tr`] descriptor,
    /// spend info is also cached.
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
    /// let result = descriptor.derived_descriptor(0, &secp).expect("Non-hardened derivation");
    /// assert_eq!(result.to_string(), "tr(03cc8a4bc64d897bddc5fbc2f670f7a8ba0b386779106cf1223c6fc5d7cd6fc115)#6qm9h8ym");
    /// ```
    ///
    /// # Errors
    ///
    /// This function will return an error if hardened derivation is attempted.
    pub fn derived_descriptor<C: secp256k1::Verification>(
        &self,
        index: u32,
        secp: &secp256k1::Secp256k1<C>,
    ) -> Result<Descriptor<bitcoin::PublicKey>, ConversionError> {
        let derived = self
            .derive(index)
            .translate_pk2(|xpk| xpk.derive_public_key(secp))?;
        Ok(derived)
    }

    /// Parse a descriptor that may contain secret keys
    ///
    /// Internally turns every secret key found into the corresponding public key and then returns a
    /// a descriptor that only contains public keys and a map to lookup the secret key given a public key.
    pub fn parse_descriptor<C: secp256k1::Signing>(
        secp: &secp256k1::Secp256k1<C>,
        s: &str,
    ) -> Result<(Descriptor<DescriptorPublicKey>, KeyMap), Error> {
        let parse_key = |s: &String,
                         key_map: &mut KeyMap|
         -> Result<DescriptorPublicKey, DescriptorKeyParseError> {
            let (public_key, secret_key) = match DescriptorSecretKey::from_str(s) {
                Ok(sk) => (sk.as_public(&secp)?, Some(sk)),
                Err(_) => (DescriptorPublicKey::from_str(s)?, None),
            };

            if let Some(secret_key) = secret_key {
                key_map.insert(public_key.clone(), secret_key);
            }

            Ok(public_key)
        };

        let mut keymap_pk = KeyMap::new();
        let mut keymap_pkh = KeyMap::new();

        let descriptor = Descriptor::<String>::from_str(s)?;
        let descriptor = descriptor
            .translate_pk(
                |pk| parse_key(pk, &mut keymap_pk),
                |pkh| parse_key(pkh, &mut keymap_pkh),
            )
            .map_err(|e| Error::Unexpected(e.to_string()))?;

        keymap_pk.extend(keymap_pkh.into_iter());

        Ok((descriptor, keymap_pk))
    }

    /// Serialize a descriptor to string with its secret keys
    pub fn to_string_with_secret(&self, key_map: &KeyMap) -> String {
        fn key_to_string(pk: &DescriptorPublicKey, key_map: &KeyMap) -> Result<String, ()> {
            Ok(match key_map.get(pk) {
                Some(secret) => secret.to_string(),
                None => pk.to_string(),
            })
        }

        let descriptor = self
            .translate_pk::<_, _, ()>(
                |pk| key_to_string(pk, key_map),
                |pkh| key_to_string(pkh, key_map),
            )
            .expect("Translation to string cannot fail");

        descriptor.to_string()
    }
}

impl<Pk> expression::FromTree for Descriptor<Pk>
where
    Pk: MiniscriptKey + str::FromStr,
    Pk::Hash: str::FromStr,
    <Pk as FromStr>::Err: ToString,
    <<Pk as MiniscriptKey>::Hash as FromStr>::Err: ToString,
{
    /// Parse an expression tree into a descriptor
    fn from_tree(top: &expression::Tree) -> Result<Descriptor<Pk>, Error> {
        Ok(match (top.name, top.args.len() as u32) {
            ("pkh", 1) => Descriptor::Pkh(Pkh::from_tree(top)?),
            ("wpkh", 1) => Descriptor::Wpkh(Wpkh::from_tree(top)?),
            ("sh", 1) => Descriptor::Sh(Sh::from_tree(top)?),
            ("wsh", 1) => Descriptor::Wsh(Wsh::from_tree(top)?),
            ("tr", _) => Descriptor::Tr(Tr::from_tree(top)?),
            _ => Descriptor::Bare(Bare::from_tree(top)?),
        })
    }
}

impl<Pk> FromStr for Descriptor<Pk>
where
    Pk: MiniscriptKey + str::FromStr,
    Pk::Hash: str::FromStr,
    <Pk as FromStr>::Err: ToString,
    <<Pk as MiniscriptKey>::Hash as FromStr>::Err: ToString,
{
    type Err = Error;

    fn from_str(s: &str) -> Result<Descriptor<Pk>, Error> {
        let desc_str = verify_checksum(s)?;
        let top = expression::Tree::from_str(desc_str)?;
        expression::FromTree::from_tree(&top)
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Descriptor<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Descriptor::Bare(ref sub) => write!(f, "{:?}", sub),
            Descriptor::Pkh(ref pkh) => write!(f, "{:?}", pkh),
            Descriptor::Wpkh(ref wpkh) => write!(f, "{:?}", wpkh),
            Descriptor::Sh(ref sub) => write!(f, "{:?}", sub),
            Descriptor::Wsh(ref sub) => write!(f, "{:?}", sub),
            Descriptor::Tr(ref tr) => write!(f, "{:?}", tr),
        }
    }
}

impl<Pk: MiniscriptKey> fmt::Display for Descriptor<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Descriptor::Bare(ref sub) => write!(f, "{}", sub),
            Descriptor::Pkh(ref pkh) => write!(f, "{}", pkh),
            Descriptor::Wpkh(ref wpkh) => write!(f, "{}", wpkh),
            Descriptor::Sh(ref sub) => write!(f, "{}", sub),
            Descriptor::Wsh(ref sub) => write!(f, "{}", sub),
            Descriptor::Tr(ref tr) => write!(f, "{}", tr),
        }
    }
}

serde_string_impl_pk!(Descriptor, "a script descriptor");

#[cfg(test)]
mod tests {
    use super::checksum::desc_checksum;
    use super::tr::Tr;
    use super::*;
    use bitcoin::blockdata::opcodes::all::{OP_CLTV, OP_CSV};
    use bitcoin::blockdata::script::Instruction;
    use bitcoin::blockdata::{opcodes, script};
    use bitcoin::hashes::hex::{FromHex, ToHex};
    use bitcoin::hashes::{hash160, sha256};
    use bitcoin::util::bip32;
    use bitcoin::{self, secp256k1, EcdsaSigHashType, PublicKey};
    use descriptor::key::Wildcard;
    use descriptor::{
        DescriptorPublicKey, DescriptorSecretKey, DescriptorSinglePub, DescriptorXKey,
    };
    use hex_script;
    use std::cmp;
    use std::collections::HashMap;
    use std::str::FromStr;
    use {Descriptor, DummyKey, Error, Miniscript, Satisfier, TranslatePk2};

    #[cfg(feature = "compiler")]
    use policy;

    type StdDescriptor = Descriptor<PublicKey>;
    const TEST_PK: &'static str =
        "pk(020000000000000000000000000000000000000000000000000000000000000002)";

    impl cmp::PartialEq for DescriptorSecretKey {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (
                    &DescriptorSecretKey::SinglePriv(ref a),
                    &DescriptorSecretKey::SinglePriv(ref b),
                ) => a.origin == b.origin && a.key == b.key,
                (&DescriptorSecretKey::XPrv(ref a), &DescriptorSecretKey::XPrv(ref b)) => {
                    a.origin == b.origin
                        && a.xkey == b.xkey
                        && a.derivation_path == b.derivation_path
                        && a.wildcard == b.wildcard
                }
                _ => false,
            }
        }
    }

    fn roundtrip_descriptor(s: &str) {
        let desc = Descriptor::<DummyKey>::from_str(&s).unwrap();
        let output = desc.to_string();
        let normalize_aliases = s.replace("c:pk_k(", "pk(").replace("c:pk_h(", "pkh(");
        assert_eq!(
            format!(
                "{}#{}",
                &normalize_aliases,
                desc_checksum(&normalize_aliases).unwrap()
            ),
            output
        );
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
        let compressed_pk = DummyKey.to_string();
        assert_eq!(
            StdDescriptor::from_str("sh(sortedmulti)")
                .unwrap_err()
                .to_string(),
            "unexpected «no arguments given for sortedmulti»"
        ); //issue 202
        assert_eq!(
            StdDescriptor::from_str(&format!("sh(sortedmulti(2,{}))", compressed_pk))
                .unwrap_err()
                .to_string(),
            "unexpected «higher threshold than there were keys in sortedmulti»"
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
        StdDescriptor::from_str(&format!(
            "or_i(pk({}),pk({}))",
            uncompressed_pk, uncompressed_pk
        ))
        .unwrap_err();
    }

    #[test]
    pub fn script_pubkey() {
        let bare = StdDescriptor::from_str(&format!(
            "multi(1,020000000000000000000000000000000000000000000000000000000000000002)"
        ))
        .unwrap();
        assert_eq!(
            bare.script_pubkey(),
            hex_script(
                "512102000000000000000000000000000000000000000000000000000000000000000251ae"
            )
        );
        assert_eq!(
            bare.address(bitcoin::Network::Bitcoin)
                .unwrap_err()
                .to_string(),
            "Bare descriptors don't have address"
        );

        let pk = StdDescriptor::from_str(TEST_PK).unwrap();
        assert_eq!(
            pk.script_pubkey(),
            bitcoin::Script::from(vec![
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
                    &hash160::Hash::from_hex("84e9ed95a38613f0527ff685a9928abe2d4754d4",).unwrap()
                        [..]
                )
                .push_opcode(opcodes::all::OP_EQUALVERIFY)
                .push_opcode(opcodes::all::OP_CHECKSIG)
                .into_script()
        );
        assert_eq!(
            pkh.address(bitcoin::Network::Bitcoin,).unwrap().to_string(),
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
                    &hash160::Hash::from_hex("84e9ed95a38613f0527ff685a9928abe2d4754d4",).unwrap()
                        [..]
                )
                .into_script()
        );
        assert_eq!(
            wpkh.address(bitcoin::Network::Bitcoin,)
                .unwrap()
                .to_string(),
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
                    &hash160::Hash::from_hex("f1c3b9a431134cb90a500ec06e0067cfa9b8bba7",).unwrap()
                        [..]
                )
                .push_opcode(opcodes::all::OP_EQUAL)
                .into_script()
        );
        assert_eq!(
            shwpkh
                .address(bitcoin::Network::Bitcoin,)
                .unwrap()
                .to_string(),
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
                    &hash160::Hash::from_hex("aa5282151694d3f2f32ace7d00ad38f927a33ac8",).unwrap()
                        [..]
                )
                .push_opcode(opcodes::all::OP_EQUAL)
                .into_script()
        );
        assert_eq!(
            sh.address(bitcoin::Network::Bitcoin,).unwrap().to_string(),
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
                    &sha256::Hash::from_hex(
                        "\
                         f9379edc8983152dc781747830075bd5\
                         3896e4b0ce5bff73777fd77d124ba085\
                         "
                    )
                    .unwrap()[..]
                )
                .into_script()
        );
        assert_eq!(
            wsh.address(bitcoin::Network::Bitcoin,).unwrap().to_string(),
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
                    &hash160::Hash::from_hex("4bec5d7feeed99e1d0a23fe32a4afe126a7ff07e",).unwrap()
                        [..]
                )
                .push_opcode(opcodes::all::OP_EQUAL)
                .into_script()
        );
        assert_eq!(
            shwsh
                .address(bitcoin::Network::Bitcoin,)
                .unwrap()
                .to_string(),
            "38cTksiyPT2b1uGRVbVqHdDhW9vKs84N6Z"
        );
    }

    #[test]
    fn satisfy() {
        let secp = secp256k1::Secp256k1::new();
        let sk =
            secp256k1::SecretKey::from_slice(&b"sally was a secret key, she said"[..]).unwrap();
        let pk = bitcoin::PublicKey::new(secp256k1::PublicKey::from_secret_key(&secp, &sk));
        let msg = secp256k1::Message::from_slice(&b"michael was a message, amusingly"[..])
            .expect("32 bytes");
        let sig = secp.sign_ecdsa(&msg, &sk);
        let mut sigser = sig.serialize_der().to_vec();
        sigser.push(0x01); // sighash_all

        struct SimpleSat {
            sig: secp256k1::ecdsa::Signature,
            pk: bitcoin::PublicKey,
        }

        impl Satisfier<bitcoin::PublicKey> for SimpleSat {
            fn lookup_ecdsa_sig(&self, pk: &bitcoin::PublicKey) -> Option<bitcoin::EcdsaSig> {
                if *pk == self.pk {
                    Some(bitcoin::EcdsaSig {
                        sig: self.sig,
                        hash_ty: bitcoin::EcdsaSigHashType::All,
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
            script_sig: bitcoin::Script::new(),
            sequence: 100,
            witness: Witness::default(),
        };
        let bare = Descriptor::new_bare(ms.clone()).unwrap();

        bare.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: script::Builder::new().push_slice(&sigser[..]).into_script(),
                sequence: 100,
                witness: Witness::default(),
            }
        );
        assert_eq!(bare.unsigned_script_sig(), bitcoin::Script::new());

        let pkh = Descriptor::new_pkh(pk);
        pkh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: script::Builder::new()
                    .push_slice(&sigser[..])
                    .push_key(&pk)
                    .into_script(),
                sequence: 100,
                witness: Witness::default(),
            }
        );
        assert_eq!(pkh.unsigned_script_sig(), bitcoin::Script::new());

        let wpkh = Descriptor::new_wpkh(pk).unwrap();
        wpkh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: bitcoin::Script::new(),
                sequence: 100,
                witness: Witness::from_vec(vec![sigser.clone(), pk.to_bytes(),]),
            }
        );
        assert_eq!(wpkh.unsigned_script_sig(), bitcoin::Script::new());

        let shwpkh = Descriptor::new_sh_wpkh(pk).unwrap();
        shwpkh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        let redeem_script = script::Builder::new()
            .push_opcode(opcodes::all::OP_PUSHBYTES_0)
            .push_slice(
                &hash160::Hash::from_hex("d1b2a1faf62e73460af885c687dee3b7189cd8ab").unwrap()[..],
            )
            .into_script();
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: script::Builder::new()
                    .push_slice(&redeem_script[..])
                    .into_script(),
                sequence: 100,
                witness: Witness::from_vec(vec![sigser.clone(), pk.to_bytes(),]),
            }
        );
        assert_eq!(
            shwpkh.unsigned_script_sig(),
            script::Builder::new()
                .push_slice(&redeem_script[..])
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
                    .push_slice(&sigser[..])
                    .push_slice(&ms.encode()[..])
                    .into_script(),
                sequence: 100,
                witness: Witness::default(),
            }
        );
        assert_eq!(sh.unsigned_script_sig(), bitcoin::Script::new());

        let ms = ms_str!("c:pk_k({})", pk);

        let wsh = Descriptor::new_wsh(ms.clone()).unwrap();
        wsh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: bitcoin::Script::new(),
                sequence: 100,
                witness: Witness::from_vec(vec![sigser.clone(), ms.encode().into_bytes(),]),
            }
        );
        assert_eq!(wsh.unsigned_script_sig(), bitcoin::Script::new());

        let shwsh = Descriptor::new_sh_wsh(ms.clone()).unwrap();
        shwsh.satisfy(&mut txin, &satisfier).expect("satisfaction");
        assert_eq!(
            txin,
            bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::default(),
                script_sig: script::Builder::new()
                    .push_slice(&ms.encode().to_v0_p2wsh()[..])
                    .into_script(),
                sequence: 100,
                witness: Witness::from_vec(vec![sigser.clone(), ms.encode().into_bytes(),]),
            }
        );
        assert_eq!(
            shwsh.unsigned_script_sig(),
            script::Builder::new()
                .push_slice(&ms.encode().to_v0_p2wsh()[..])
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
        let script = Tr::<DummyKey>::from_str("tr()").unwrap().to_string();
        assert_eq!(script, format!("tr()#x4ml3kxd"))
    }

    #[test]
    fn tr_roundtrip_script() {
        let descriptor = Tr::<DummyKey>::from_str("tr(,{pk(),pk()})")
            .unwrap()
            .to_string();

        assert_eq!(descriptor, "tr(,{pk(),pk()})#7dqr6v8r")
    }

    #[test]
    fn tr_roundtrip_tree() {
        let p1 = "020000000000000000000000000000000000000000000000000000000000000001";
        let p2 = "020000000000000000000000000000000000000000000000000000000000000002";
        let p3 = "020000000000000000000000000000000000000000000000000000000000000003";
        let p4 = "020000000000000000000000000000000000000000000000000000000000000004";
        let p5 = "f54a5851e9372b87810a8e60cdd2e7cfd80b6e31";
        let descriptor = Tr::<PublicKey>::from_str(&format!(
            "tr({},{{pk({}),{{pk({}),or_d(pk({}),pkh({}))}}}})",
            p1, p2, p3, p4, p5
        ))
        .unwrap()
        .to_string();

        assert_eq!(
            descriptor,
            format!(
                "tr({},{{pk({}),{{pk({}),or_d(pk({}),pkh({}))}}}})#fdhmu4fj",
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
            key.script_pubkey().to_hex(),
            "51209c19294f03757da3dc235a5960631e3c55751632f5889b06b7a053bdc0bcfbcb"
        )
    }

    #[test]
    fn roundtrip_tests() {
        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str("multi");
        assert_eq!(
            descriptor.unwrap_err().to_string(),
            "unexpected «no arguments given»"
        )
    }

    #[test]
    fn empty_thresh() {
        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str("thresh");
        assert_eq!(
            descriptor.unwrap_err().to_string(),
            "unexpected «no arguments given»"
        )
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
            script_sig: bitcoin::Script::new(),
            sequence: 0,
            witness: Witness::default(),
        };
        let satisfier = {
            let mut satisfier = HashMap::with_capacity(2);

            satisfier.insert(
                a,
                bitcoin::EcdsaSig {
                    sig: sig_a,
                    hash_ty: EcdsaSigHashType::All,
                },
            );
            satisfier.insert(
                b,
                bitcoin::EcdsaSig {
                    sig: sig_b,
                    hash_ty: EcdsaSigHashType::All,
                },
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
                bip32::Fingerprint::from(&[0x78, 0x41, 0x2e, 0x3a][..]),
                (&[
                    bip32::ChildNumber::from_hardened_idx(44).unwrap(),
                    bip32::ChildNumber::from_hardened_idx(0).unwrap(),
                    bip32::ChildNumber::from_hardened_idx(0).unwrap(),
                ][..])
                .into(),
            )),
            xkey: bip32::ExtendedPubKey::from_str("xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL").unwrap(),
            derivation_path: (&[bip32::ChildNumber::from_normal_idx(1).unwrap()][..]).into(),
            wildcard: Wildcard::Unhardened,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Without origin
        let key = "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1";
        let expected = DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::ExtendedPubKey::from_str("xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL").unwrap(),
            derivation_path: (&[bip32::ChildNumber::from_normal_idx(1).unwrap()][..]).into(),
            wildcard: Wildcard::None,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Testnet tpub
        let key = "tpubD6NzVbkrYhZ4YqYr3amYH15zjxHvBkUUeadieW8AxTZC7aY2L8aPSk3tpW6yW1QnWzXAB7zoiaNMfwXPPz9S68ZCV4yWvkVXjdeksLskCed/1";
        let expected = DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::ExtendedPubKey::from_str("tpubD6NzVbkrYhZ4YqYr3amYH15zjxHvBkUUeadieW8AxTZC7aY2L8aPSk3tpW6yW1QnWzXAB7zoiaNMfwXPPz9S68ZCV4yWvkVXjdeksLskCed").unwrap(),
            derivation_path: (&[bip32::ChildNumber::from_normal_idx(1).unwrap()][..]).into(),
            wildcard: Wildcard::None,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Without derivation path
        let key = "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL";
        let expected = DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::ExtendedPubKey::from_str("xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL").unwrap(),
            derivation_path: bip32::DerivationPath::from(&[][..]),
            wildcard: Wildcard::None,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Raw (compressed) pubkey
        let key = "03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8";
        let expected = DescriptorPublicKey::SinglePub(DescriptorSinglePub {
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
        let expected = DescriptorPublicKey::SinglePub(DescriptorSinglePub {
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
        let expected = DescriptorPublicKey::SinglePub(DescriptorSinglePub {
            key: SinglePubKey::FullKey(
                bitcoin::PublicKey::from_str(
                    "0231c7d3fc85c148717848033ce276ae2b464a4e2c367ed33886cc428b8af48ff8",
                )
                .unwrap(),
            ),
            origin: Some((
                bip32::Fingerprint::from(&[0x78, 0x41, 0x2e, 0x3a][..]),
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
            let mut desc_one = Descriptor::<DescriptorPublicKey>::from_str(raw_desc_one).unwrap();
            let mut desc_two = Descriptor::<DescriptorPublicKey>::from_str(raw_desc_two).unwrap();

            // Same string formatting
            assert_eq!(desc_one.to_string(), raw_desc_one);
            assert_eq!(desc_two.to_string(), raw_desc_two);

            // Derive a child if the descriptor is ranged
            if raw_desc_one.contains("*") && raw_desc_two.contains("*") {
                desc_one = desc_one.derive(index);
                desc_two = desc_two.derive(index);
            }

            // Same address
            let addr_one = desc_one
                .translate_pk2(|xpk| xpk.derive_public_key(&secp_ctx))
                .unwrap()
                .address(bitcoin::Network::Bitcoin)
                .unwrap();
            let addr_two = desc_two
                .translate_pk2(|xpk| xpk.derive_public_key(&secp_ctx))
                .unwrap()
                .address(bitcoin::Network::Bitcoin)
                .unwrap();
            let addr_expected = bitcoin::Address::from_str(raw_addr_expected).unwrap();
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
                $(
                    match Descriptor::parse_descriptor($secp, $desc) {
                        Err(Error::BadDescriptor(_)) => {},
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

        Descriptor::parse_descriptor(&secp, "sh(multi(2,[00000000/111'/222]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc,xprv9uPDJpEQgRQfDcW7BkF7eTya6RPxXeJCqCJGHuCJ4GiRVLzkTXBAJMu2qaMWPrS7AANYqdq6vcBcBUdJCVVFceUvJFjaPdGZ2y9WACViL4L/0))#ggrsrxfy").expect("Valid descriptor with checksum");
        Descriptor::parse_descriptor(&secp, "sh(multi(2,[00000000/111'/222]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL,xpub68NZiKmJWnxxS6aaHmn81bvJeTESw724CRDs6HbuccFQN9Ku14VQrADWgqbhhTHBaohPX4CjNLf9fq9MYo6oDaPPLPxSb7gwQN3ih19Zm4Y/0))#tjg09x5t").expect("Valid descriptor with checksum");
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
        let derived_descriptor = descriptor.derive(42);

        let res_descriptor_str = "thresh(2,\
pk([d34db33f/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/42),\
pk(xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1),\
pk(03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8))";
        let res_policy: policy::concrete::Policy<DescriptorPublicKey> =
            res_descriptor_str.parse().unwrap();
        let res_descriptor = Descriptor::new_sh(res_policy.compile().unwrap()).unwrap();

        assert_eq!(res_descriptor, derived_descriptor);
    }

    #[test]
    fn parse_with_secrets() {
        let secp = &secp256k1::Secp256k1::signing_only();
        let descriptor_str = "wpkh(xprv9s21ZrQH143K4CTb63EaMxja1YiTnSEWKMbn23uoEnAzxjdUJRQkazCAtzxGm4LSoTSVTptoV9RbchnKPW9HxKtZumdyxyikZFDLhogJ5Uj/44'/0'/0'/0/*)#v20xlvm9";
        let (descriptor, keymap) =
            Descriptor::<DescriptorPublicKey>::parse_descriptor(&secp, descriptor_str).unwrap();

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
}
