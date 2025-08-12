// SPDX-License-Identifier: CC0-1.0

//! # Satisfaction and Dissatisfaction
//!
//! Traits and implementations to support producing witnesses for Miniscript
//! scriptpubkeys.
//!

mod sat_dissat;

use core::{cmp, fmt, mem};

use bitcoin::hashes::hash160;
use bitcoin::key::XOnlyPublicKey;
use bitcoin::taproot::{ControlBlock, LeafVersion, TapLeafHash, TapNodeHash};
use bitcoin::{absolute, relative, ScriptBuf, Sequence};

use super::context::SigType;
use crate::plan::AssetProvider;
use crate::prelude::*;
use crate::util::witness_size;
use crate::{
    AbsLockTime, Miniscript, MiniscriptKey, RelLockTime, ScriptContext, ToPublicKey,
    ValidationParams,
};

/// No satisfaction exists for a Miniscript fragment; it is equivalent to `OP_FALSE`.
#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct SatisfactionImpossibleError;

impl fmt::Display for SatisfactionImpossibleError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("no satisfaction exists (equivalent to OP_FALSE)")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for SatisfactionImpossibleError {}

/// Type alias for 32 byte Preimage.
pub type Preimage32 = [u8; 32];
/// Trait describing a lookup table for signatures, hash preimages, etc.
///
/// Every method has a default implementation that simply returns `None`
/// on every query. Users are expected to override the methods that they
/// have data for.
pub trait Satisfier<Pk: MiniscriptKey + ToPublicKey> {
    /// Given a public key, look up an ECDSA signature with that key
    fn lookup_ecdsa_sig(&self, _: &Pk) -> Option<bitcoin::ecdsa::Signature> { None }

    /// Lookup the tap key spend sig
    fn lookup_tap_key_spend_sig(&self, _: &Pk) -> Option<bitcoin::taproot::Signature> { None }

    /// Given a public key and a associated leaf hash, look up an schnorr signature with that key
    fn lookup_tap_leaf_script_sig(
        &self,
        _: &Pk,
        _: &TapLeafHash,
    ) -> Option<bitcoin::taproot::Signature> {
        None
    }

    /// Obtain a reference to the control block for a ver and script
    fn lookup_tap_control_block_map(
        &self,
    ) -> Option<&BTreeMap<ControlBlock, (bitcoin::ScriptBuf, LeafVersion)>> {
        None
    }

    /// Given a raw `Pkh`, lookup corresponding [`bitcoin::PublicKey`]
    fn lookup_raw_pkh_pk(&self, _: &hash160::Hash) -> Option<bitcoin::PublicKey> { None }

    /// Given a raw `Pkh`, lookup corresponding [`bitcoin::secp256k1::XOnlyPublicKey`]
    fn lookup_raw_pkh_x_only_pk(&self, _: &hash160::Hash) -> Option<XOnlyPublicKey> { None }

    /// Given a keyhash, look up the EC signature and the associated key.
    ///
    /// Even if signatures for public key Hashes are not available, the users
    /// can use this map to provide pkh -> pk mapping which can be useful
    /// for dissatisfying pkh.
    fn lookup_raw_pkh_ecdsa_sig(
        &self,
        _: &hash160::Hash,
    ) -> Option<(bitcoin::PublicKey, bitcoin::ecdsa::Signature)> {
        None
    }

    /// Given a keyhash, look up the schnorr signature and the associated key.
    ///
    /// Even if signatures for public key Hashes are not available, the users
    /// can use this map to provide pkh -> pk mapping which can be useful
    /// for dissatisfying pkh.
    fn lookup_raw_pkh_tap_leaf_script_sig(
        &self,
        _: &(hash160::Hash, TapLeafHash),
    ) -> Option<(XOnlyPublicKey, bitcoin::taproot::Signature)> {
        None
    }

    /// Given a SHA256 hash, look up its preimage
    fn lookup_sha256(&self, _: &Pk::Sha256) -> Option<Preimage32> { None }

    /// Given a HASH256 hash, look up its preimage
    fn lookup_hash256(&self, _: &Pk::Hash256) -> Option<Preimage32> { None }

    /// Given a RIPEMD160 hash, look up its preimage
    fn lookup_ripemd160(&self, _: &Pk::Ripemd160) -> Option<Preimage32> { None }

    /// Given a HASH160 hash, look up its preimage
    fn lookup_hash160(&self, _: &Pk::Hash160) -> Option<Preimage32> { None }

    /// Assert whether an relative locktime is satisfied
    ///
    /// NOTE: If a descriptor mixes time-based and height-based timelocks, the implementation of
    /// this method MUST only allow timelocks of either unit, but not both. Allowing both could cause
    /// miniscript to construct an invalid witness.
    fn check_older(&self, _: relative::LockTime) -> bool { false }

    /// Assert whether a absolute locktime is satisfied
    ///
    /// NOTE: If a descriptor mixes time-based and height-based timelocks, the implementation of
    /// this method MUST only allow timelocks of either unit, but not both. Allowing both could cause
    /// miniscript to construct an invalid witness.
    fn check_after(&self, _: absolute::LockTime) -> bool { false }
}

// Allow use of `()` as a "no conditions available" satisfier
impl<Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk> for () {}

impl<Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk> for Sequence {
    fn check_older(&self, n: relative::LockTime) -> bool {
        if let Some(lt) = self.to_relative_lock_time() {
            Satisfier::<Pk>::check_older(&lt, n)
        } else {
            false
        }
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk> for RelLockTime {
    fn check_older(&self, n: relative::LockTime) -> bool {
        <relative::LockTime as Satisfier<Pk>>::check_older(&(*self).into(), n)
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk> for relative::LockTime {
    fn check_older(&self, n: relative::LockTime) -> bool { n.is_implied_by(*self) }
}

impl<Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk> for absolute::LockTime {
    fn check_after(&self, n: absolute::LockTime) -> bool { n.is_implied_by(*self) }
}

macro_rules! impl_satisfier_for_map_key_to_ecdsa_sig {
    ($(#[$($attr:meta)*])* impl Satisfier<Pk> for $map:ident<$key:ty, $val:ty>) => {
        $(#[$($attr)*])*
        impl<Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk>
            for $map<Pk, bitcoin::ecdsa::Signature>
        {
            fn lookup_ecdsa_sig(&self, key: &Pk) -> Option<bitcoin::ecdsa::Signature> {
                self.get(key).copied()
            }
        }
    };
}

impl_satisfier_for_map_key_to_ecdsa_sig! {
    impl Satisfier<Pk> for BTreeMap<Pk, bitcoin::ecdsa::Signature>
}

impl_satisfier_for_map_key_to_ecdsa_sig! {
    #[cfg(feature = "std")]
    impl Satisfier<Pk> for HashMap<Pk, bitcoin::ecdsa::Signature>
}

macro_rules! impl_satisfier_for_map_key_hash_to_taproot_sig {
    ($(#[$($attr:meta)*])* impl Satisfier<Pk> for $map:ident<$key:ty, $val:ty>) => {
        $(#[$($attr)*])*
        impl<Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk>
            for $map<(Pk, TapLeafHash), bitcoin::taproot::Signature>
        {
            fn lookup_tap_leaf_script_sig(
                &self,
                key: &Pk,
                h: &TapLeafHash,
            ) -> Option<bitcoin::taproot::Signature> {
                // Unfortunately, there is no way to get a &(a, b) from &a and &b without allocating
                // If we change the signature the of lookup_tap_leaf_script_sig to accept a tuple. We would
                // face the same problem while satisfying PkK.
                // We use this signature to optimize for the psbt common use case.
                self.get(&(key.clone(), *h)).copied()
            }
        }
    };
}

impl_satisfier_for_map_key_hash_to_taproot_sig! {
    impl Satisfier<Pk> for BTreeMap<(Pk, TapLeafHash), bitcoin::taproot::Signature>
}

impl_satisfier_for_map_key_hash_to_taproot_sig! {
    #[cfg(feature = "std")]
    impl Satisfier<Pk> for HashMap<(Pk, TapLeafHash), bitcoin::taproot::Signature>
}

macro_rules! impl_satisfier_for_map_hash_to_key_ecdsa_sig {
    ($(#[$($attr:meta)*])* impl Satisfier<Pk> for $map:ident<$key:ty, $val:ty>) => {
        $(#[$($attr)*])*
        impl<Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk>
            for $map<hash160::Hash, (Pk, bitcoin::ecdsa::Signature)>
        where
            Pk: MiniscriptKey + ToPublicKey,
        {
            fn lookup_ecdsa_sig(&self, key: &Pk) -> Option<bitcoin::ecdsa::Signature> {
                self.get(&key.to_pubkeyhash(SigType::Ecdsa)).map(|x| x.1)
            }

            fn lookup_raw_pkh_pk(&self, pk_hash: &hash160::Hash) -> Option<bitcoin::PublicKey> {
                self.get(pk_hash).map(|x| x.0.to_public_key())
            }

            fn lookup_raw_pkh_ecdsa_sig(
                &self,
                pk_hash: &hash160::Hash,
            ) -> Option<(bitcoin::PublicKey, bitcoin::ecdsa::Signature)> {
                self.get(pk_hash)
                    .map(|&(ref pk, sig)| (pk.to_public_key(), sig))
            }
        }
    };
}

impl_satisfier_for_map_hash_to_key_ecdsa_sig! {
    impl Satisfier<Pk> for BTreeMap<hash160::Hash, (Pk, bitcoin::ecdsa::Signature)>
}

impl_satisfier_for_map_hash_to_key_ecdsa_sig! {
    #[cfg(feature = "std")]
    impl Satisfier<Pk> for HashMap<hash160::Hash, (Pk, bitcoin::ecdsa::Signature)>
}

macro_rules! impl_satisfier_for_map_hash_tapleafhash_to_key_taproot_sig {
    ($(#[$($attr:meta)*])* impl Satisfier<Pk> for $map:ident<$key:ty, $val:ty>) => {
        $(#[$($attr)*])*
        impl<Pk: MiniscriptKey + ToPublicKey> Satisfier<Pk>
            for $map<(hash160::Hash, TapLeafHash), (Pk, bitcoin::taproot::Signature)>
        where
            Pk: MiniscriptKey + ToPublicKey,
        {
            fn lookup_tap_leaf_script_sig(
                &self,
                key: &Pk,
                h: &TapLeafHash,
            ) -> Option<bitcoin::taproot::Signature> {
                self.get(&(key.to_pubkeyhash(SigType::Schnorr), *h))
                    .map(|x| x.1)
            }

            fn lookup_raw_pkh_tap_leaf_script_sig(
                &self,
                pk_hash: &(hash160::Hash, TapLeafHash),
            ) -> Option<(XOnlyPublicKey, bitcoin::taproot::Signature)> {
                self.get(pk_hash)
                    .map(|&(ref pk, sig)| (pk.to_x_only_pubkey(), sig))
            }
        }
    };
}

impl_satisfier_for_map_hash_tapleafhash_to_key_taproot_sig! {
    impl Satisfier<Pk> for BTreeMap<(hash160::Hash, TapLeafHash), (Pk, bitcoin::taproot::Signature)>
}

impl_satisfier_for_map_hash_tapleafhash_to_key_taproot_sig! {
    #[cfg(feature = "std")]
    impl Satisfier<Pk> for HashMap<(hash160::Hash, TapLeafHash), (Pk, bitcoin::taproot::Signature)>
}

impl<Pk: MiniscriptKey + ToPublicKey, S: Satisfier<Pk>> Satisfier<Pk> for &S {
    fn lookup_ecdsa_sig(&self, p: &Pk) -> Option<bitcoin::ecdsa::Signature> {
        (**self).lookup_ecdsa_sig(p)
    }

    fn lookup_tap_leaf_script_sig(
        &self,
        p: &Pk,
        h: &TapLeafHash,
    ) -> Option<bitcoin::taproot::Signature> {
        (**self).lookup_tap_leaf_script_sig(p, h)
    }

    fn lookup_raw_pkh_pk(&self, pkh: &hash160::Hash) -> Option<bitcoin::PublicKey> {
        (**self).lookup_raw_pkh_pk(pkh)
    }

    fn lookup_raw_pkh_x_only_pk(&self, pkh: &hash160::Hash) -> Option<XOnlyPublicKey> {
        (**self).lookup_raw_pkh_x_only_pk(pkh)
    }

    fn lookup_raw_pkh_ecdsa_sig(
        &self,
        pkh: &hash160::Hash,
    ) -> Option<(bitcoin::PublicKey, bitcoin::ecdsa::Signature)> {
        (**self).lookup_raw_pkh_ecdsa_sig(pkh)
    }

    fn lookup_tap_key_spend_sig(&self, pk: &Pk) -> Option<bitcoin::taproot::Signature> {
        (**self).lookup_tap_key_spend_sig(pk)
    }

    fn lookup_raw_pkh_tap_leaf_script_sig(
        &self,
        pkh: &(hash160::Hash, TapLeafHash),
    ) -> Option<(XOnlyPublicKey, bitcoin::taproot::Signature)> {
        (**self).lookup_raw_pkh_tap_leaf_script_sig(pkh)
    }

    fn lookup_tap_control_block_map(
        &self,
    ) -> Option<&BTreeMap<ControlBlock, (bitcoin::ScriptBuf, LeafVersion)>> {
        (**self).lookup_tap_control_block_map()
    }

    fn lookup_sha256(&self, h: &Pk::Sha256) -> Option<Preimage32> { (**self).lookup_sha256(h) }

    fn lookup_hash256(&self, h: &Pk::Hash256) -> Option<Preimage32> { (**self).lookup_hash256(h) }

    fn lookup_ripemd160(&self, h: &Pk::Ripemd160) -> Option<Preimage32> {
        (**self).lookup_ripemd160(h)
    }

    fn lookup_hash160(&self, h: &Pk::Hash160) -> Option<Preimage32> { (**self).lookup_hash160(h) }

    fn check_older(&self, t: relative::LockTime) -> bool { (**self).check_older(t) }

    fn check_after(&self, n: absolute::LockTime) -> bool { (**self).check_after(n) }
}

impl<Pk: MiniscriptKey + ToPublicKey, S: Satisfier<Pk>> Satisfier<Pk> for &mut S {
    fn lookup_ecdsa_sig(&self, p: &Pk) -> Option<bitcoin::ecdsa::Signature> {
        (**self).lookup_ecdsa_sig(p)
    }

    fn lookup_tap_leaf_script_sig(
        &self,
        p: &Pk,
        h: &TapLeafHash,
    ) -> Option<bitcoin::taproot::Signature> {
        (**self).lookup_tap_leaf_script_sig(p, h)
    }

    fn lookup_tap_key_spend_sig(&self, pk: &Pk) -> Option<bitcoin::taproot::Signature> {
        (**self).lookup_tap_key_spend_sig(pk)
    }

    fn lookup_raw_pkh_pk(&self, pkh: &hash160::Hash) -> Option<bitcoin::PublicKey> {
        (**self).lookup_raw_pkh_pk(pkh)
    }

    fn lookup_raw_pkh_x_only_pk(&self, pkh: &hash160::Hash) -> Option<XOnlyPublicKey> {
        (**self).lookup_raw_pkh_x_only_pk(pkh)
    }

    fn lookup_raw_pkh_ecdsa_sig(
        &self,
        pkh: &hash160::Hash,
    ) -> Option<(bitcoin::PublicKey, bitcoin::ecdsa::Signature)> {
        (**self).lookup_raw_pkh_ecdsa_sig(pkh)
    }

    fn lookup_raw_pkh_tap_leaf_script_sig(
        &self,
        pkh: &(hash160::Hash, TapLeafHash),
    ) -> Option<(XOnlyPublicKey, bitcoin::taproot::Signature)> {
        (**self).lookup_raw_pkh_tap_leaf_script_sig(pkh)
    }

    fn lookup_tap_control_block_map(
        &self,
    ) -> Option<&BTreeMap<ControlBlock, (bitcoin::ScriptBuf, LeafVersion)>> {
        (**self).lookup_tap_control_block_map()
    }

    fn lookup_sha256(&self, h: &Pk::Sha256) -> Option<Preimage32> { (**self).lookup_sha256(h) }

    fn lookup_hash256(&self, h: &Pk::Hash256) -> Option<Preimage32> { (**self).lookup_hash256(h) }

    fn lookup_ripemd160(&self, h: &Pk::Ripemd160) -> Option<Preimage32> {
        (**self).lookup_ripemd160(h)
    }

    fn lookup_hash160(&self, h: &Pk::Hash160) -> Option<Preimage32> { (**self).lookup_hash160(h) }

    fn check_older(&self, t: relative::LockTime) -> bool { (**self).check_older(t) }

    fn check_after(&self, n: absolute::LockTime) -> bool { (**self).check_after(n) }
}

macro_rules! impl_tuple_satisfier {
    ($($ty:ident),*) => {
        #[allow(non_snake_case)]
        impl<$($ty,)* Pk> Satisfier<Pk> for ($($ty,)*)
        where
            Pk: MiniscriptKey + ToPublicKey,
            $($ty: Satisfier< Pk>,)*
        {
            fn lookup_ecdsa_sig(&self, key: &Pk) -> Option<bitcoin::ecdsa::Signature> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_ecdsa_sig(key) {
                        return Some(result);
                    }
                )*
                None
            }

            fn lookup_tap_key_spend_sig(&self, pk: &Pk) -> Option<bitcoin::taproot::Signature> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_tap_key_spend_sig(pk) {
                        return Some(result);
                    }
                )*
                None
            }

            fn lookup_tap_leaf_script_sig(&self, key: &Pk, h: &TapLeafHash) -> Option<bitcoin::taproot::Signature> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_tap_leaf_script_sig(key, h) {
                        return Some(result);
                    }
                )*
                None
            }

            fn lookup_raw_pkh_ecdsa_sig(
                &self,
                key_hash: &hash160::Hash,
            ) -> Option<(bitcoin::PublicKey, bitcoin::ecdsa::Signature)> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_raw_pkh_ecdsa_sig(key_hash) {
                        return Some(result);
                    }
                )*
                None
            }

            fn lookup_raw_pkh_tap_leaf_script_sig(
                &self,
                key_hash: &(hash160::Hash, TapLeafHash),
            ) -> Option<(XOnlyPublicKey, bitcoin::taproot::Signature)> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_raw_pkh_tap_leaf_script_sig(key_hash) {
                        return Some(result);
                    }
                )*
                None
            }

            fn lookup_raw_pkh_pk(
                &self,
                key_hash: &hash160::Hash,
            ) -> Option<bitcoin::PublicKey> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_raw_pkh_pk(key_hash) {
                        return Some(result);
                    }
                )*
                None
            }
            fn lookup_raw_pkh_x_only_pk(
                &self,
                key_hash: &hash160::Hash,
            ) -> Option<XOnlyPublicKey> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_raw_pkh_x_only_pk(key_hash) {
                        return Some(result);
                    }
                )*
                None
            }

            fn lookup_tap_control_block_map(
                &self,
            ) -> Option<&BTreeMap<ControlBlock, (bitcoin::ScriptBuf, LeafVersion)>> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_tap_control_block_map() {
                        return Some(result);
                    }
                )*
                None
            }

            fn lookup_sha256(&self, h: &Pk::Sha256) -> Option<Preimage32> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_sha256(h) {
                        return Some(result);
                    }
                )*
                None
            }

            fn lookup_hash256(&self, h: &Pk::Hash256) -> Option<Preimage32> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_hash256(h) {
                        return Some(result);
                    }
                )*
                None
            }

            fn lookup_ripemd160(&self, h: &Pk::Ripemd160) -> Option<Preimage32> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_ripemd160(h) {
                        return Some(result);
                    }
                )*
                None
            }

            fn lookup_hash160(&self, h: &Pk::Hash160) -> Option<Preimage32> {
                let &($(ref $ty,)*) = self;
                $(
                    if let Some(result) = $ty.lookup_hash160(h) {
                        return Some(result);
                    }
                )*
                None
            }

            fn check_older(&self, n: relative::LockTime) -> bool {
                let &($(ref $ty,)*) = self;
                $(
                    if $ty.check_older(n) {
                        return true;
                    }
                )*
                false
            }

            fn check_after(&self, n: absolute::LockTime) -> bool {
                let &($(ref $ty,)*) = self;
                $(
                    if $ty.check_after(n) {
                        return true;
                    }
                )*
                false
            }
        }
    }
}

impl_tuple_satisfier!(A);
impl_tuple_satisfier!(A, B);
impl_tuple_satisfier!(A, B, C);
impl_tuple_satisfier!(A, B, C, D);
impl_tuple_satisfier!(A, B, C, D, E);
impl_tuple_satisfier!(A, B, C, D, E, F);
impl_tuple_satisfier!(A, B, C, D, E, F, G);
impl_tuple_satisfier!(A, B, C, D, E, F, G, H);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Type of schnorr signature to produce
pub enum SchnorrSigType {
    /// Key spend signature
    KeySpend {
        /// Merkle root to tweak the key, if present
        merkle_root: Option<TapNodeHash>,
    },
    /// Script spend signature
    ScriptSpend {
        /// Leaf hash of the script
        leaf_hash: TapLeafHash,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Placeholder for some data in a [`Plan`]
///
/// [`Plan`]: crate::plan::Plan
pub enum Placeholder<Pk: MiniscriptKey> {
    /// Public key and its size
    Pubkey(Pk, usize),
    /// Public key hash and public key size
    PubkeyHash(hash160::Hash, usize),
    /// ECDSA signature given the raw pubkey
    EcdsaSigPk(Pk),
    /// ECDSA signature given the pubkey hash
    EcdsaSigPkHash(hash160::Hash),
    /// Schnorr signature and its size
    SchnorrSigPk(Pk, SchnorrSigType, usize),
    /// Schnorr signature given the pubkey hash, the tapleafhash, and the sig size
    SchnorrSigPkHash(hash160::Hash, TapLeafHash, usize),
    /// SHA-256 preimage
    Sha256Preimage(Pk::Sha256),
    /// HASH256 preimage
    Hash256Preimage(Pk::Hash256),
    /// RIPEMD160 preimage
    Ripemd160Preimage(Pk::Ripemd160),
    /// HASH160 preimage
    Hash160Preimage(Pk::Hash160),
    /// Hash dissatisfaction (32 bytes of 0x00)
    HashDissatisfaction,
    /// OP_1
    PushOne,
    /// \<empty item\>
    PushZero,
    /// Taproot leaf script
    TapScript(ScriptBuf),
    /// Taproot control block
    TapControlBlock(ControlBlock),
}

impl<Pk: MiniscriptKey> fmt::Display for Placeholder<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Pubkey(pk, size) => write!(f, "Pubkey(pk: {}, size: {})", pk, size),
            Self::PubkeyHash(hash, size) => write!(f, "PubkeyHash(hash: {}, size: {})", hash, size),
            Self::EcdsaSigPk(pk) => write!(f, "EcdsaSigPk(pk: {})", pk),
            Self::EcdsaSigPkHash(hash) => write!(f, "EcdsaSigPkHash(pkh: {})", hash),
            Self::SchnorrSigPk(pk, tap_leaf_hash, size) => write!(
                f,
                "SchnorrSig(pk: {}, tap_leaf_hash: {:?}, size: {})",
                pk, tap_leaf_hash, size
            ),
            Self::SchnorrSigPkHash(pkh, tap_leaf_hash, size) => write!(
                f,
                "SchnorrSigPkHash(pkh: {}, tap_leaf_hash: {:?}, size: {})",
                pkh, tap_leaf_hash, size
            ),
            Self::Sha256Preimage(hash) => write!(f, "Sha256Preimage(hash: {})", hash),
            Self::Hash256Preimage(hash) => write!(f, "Hash256Preimage(hash: {})", hash),
            Self::Ripemd160Preimage(hash) => write!(f, "Ripemd160Preimage(hash: {})", hash),
            Self::Hash160Preimage(hash) => write!(f, "Hash160Preimage(hash: {})", hash),
            Self::HashDissatisfaction => write!(f, "HashDissatisfaction"),
            Self::PushOne => write!(f, "PushOne"),
            Self::PushZero => write!(f, "PushZero"),
            Self::TapScript(script) => write!(f, "TapScript(script: {})", script),
            Self::TapControlBlock(control_block) => write!(
                f,
                "TapControlBlock(control_block: {})",
                bitcoin::consensus::encode::serialize_hex(&control_block.serialize())
            ),
        }
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Placeholder<Pk> {
    /// Replaces the placeholders with the information given by the satisfier
    pub fn satisfy_self<Sat: Satisfier<Pk>>(&self, sat: &Sat) -> Option<Vec<u8>> {
        match self {
            Self::Pubkey(pk, size) => {
                if *size == 33 {
                    Some(pk.to_x_only_pubkey().serialize().to_vec())
                } else {
                    Some(pk.to_public_key().to_bytes())
                }
            }
            Self::PubkeyHash(pkh, size) => sat
                .lookup_raw_pkh_pk(pkh)
                .map(|p| p.to_public_key())
                .or(sat.lookup_raw_pkh_ecdsa_sig(pkh).map(|(p, _)| p))
                .map(|pk| {
                    let pk = pk.to_bytes();
                    // We have to add a 1-byte OP_PUSH
                    debug_assert!(1 + pk.len() == *size);
                    pk
                }),
            Self::Hash256Preimage(h) => sat.lookup_hash256(h).map(|p| p.to_vec()),
            Self::Sha256Preimage(h) => sat.lookup_sha256(h).map(|p| p.to_vec()),
            Self::Hash160Preimage(h) => sat.lookup_hash160(h).map(|p| p.to_vec()),
            Self::Ripemd160Preimage(h) => sat.lookup_ripemd160(h).map(|p| p.to_vec()),
            Self::EcdsaSigPk(pk) => sat.lookup_ecdsa_sig(pk).map(|s| s.to_vec()),
            Self::EcdsaSigPkHash(pkh) => sat.lookup_raw_pkh_ecdsa_sig(pkh).map(|(_, s)| s.to_vec()),
            Self::SchnorrSigPk(pk, SchnorrSigType::ScriptSpend { leaf_hash }, size) => sat
                .lookup_tap_leaf_script_sig(pk, leaf_hash)
                .map(|s| s.to_vec())
                .map(|s| {
                    debug_assert!(s.len() == *size);
                    s
                }),
            Self::SchnorrSigPk(pk, _, size) => sat
                .lookup_tap_key_spend_sig(pk)
                .map(|s| s.to_vec())
                .map(|s| {
                    debug_assert!(s.len() == *size);
                    s
                }),
            Self::SchnorrSigPkHash(pkh, tap_leaf_hash, size) => sat
                .lookup_raw_pkh_tap_leaf_script_sig(&(*pkh, *tap_leaf_hash))
                .map(|(_, s)| {
                    let sig = s.to_vec();
                    debug_assert!(sig.len() == *size);
                    sig
                }),
            Self::HashDissatisfaction => Some(vec![0; 32]),
            Self::PushZero => Some(vec![]),
            Self::PushOne => Some(vec![1]),
            Self::TapScript(s) => Some(s.to_bytes()),
            Self::TapControlBlock(cb) => Some(cb.serialize()),
        }
    }
}

/// A witness, if available, for a Miniscript fragment
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Witness<T> {
    /// Witness Available and the value of the witness
    Stack(Vec<T>),
    /// Third party can possibly satisfy the fragment but we cannot
    /// Witness Unavailable
    Unavailable,
    /// No third party can produce a satisfaction without private key
    /// Witness Impossible
    Impossible,
}

impl<Pk: MiniscriptKey> PartialOrd for Witness<Placeholder<Pk>> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}

impl<Pk: MiniscriptKey> Ord for Witness<Placeholder<Pk>> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match (self, other) {
            (Self::Stack(v1), Self::Stack(v2)) => {
                let w1 = witness_size(v1);
                let w2 = witness_size(v2);
                w1.cmp(&w2)
            }
            (Self::Stack(_), _) => cmp::Ordering::Less,
            (_, Self::Stack(_)) => cmp::Ordering::Greater,
            (Self::Impossible, Self::Unavailable) => cmp::Ordering::Less,
            (Self::Unavailable, Self::Impossible) => cmp::Ordering::Greater,
            (Self::Impossible, Self::Impossible) => cmp::Ordering::Equal,
            (Self::Unavailable, Self::Unavailable) => cmp::Ordering::Equal,
        }
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Witness<Placeholder<Pk>> {
    /// Turn a signature into (part of) a satisfaction
    fn signature<S: AssetProvider<Pk>>(sat: &S, pk: &Pk, leaf_hash: Option<TapLeafHash>) -> Self {
        if let Some(leaf_hash) = leaf_hash {
            match sat.provider_lookup_tap_leaf_script_sig(pk, &leaf_hash) {
                Some(size) => Self::Stack(vec![Placeholder::SchnorrSigPk(
                    pk.clone(),
                    SchnorrSigType::ScriptSpend { leaf_hash },
                    size,
                )]),
                // Signatures cannot be forged
                None => Self::Impossible,
            }
        } else {
            if sat.provider_lookup_ecdsa_sig(pk) {
                Self::Stack(vec![Placeholder::EcdsaSigPk(pk.clone())])
            } else {
                // Signatures cannot be forged
                Self::Impossible
            }
        }
    }

    /// Turn a public key related to a pkh into (part of) a satisfaction
    fn pkh_public_key<S: AssetProvider<Pk>>(
        sat: &S,
        params: &ValidationParams,
        taproot: bool,
        pkh: &hash160::Hash,
    ) -> Self {
        // public key hashes are assumed to be unavailable
        // instead of impossible since it is the same as pub-key hashes
        if taproot {
            match sat.provider_lookup_raw_pkh_x_only_pk(pkh) {
                Some(pk) => {
                    Self::Stack(vec![Placeholder::PubkeyHash(*pkh, params.encoded_key_size(&pk))])
                }
                None => Self::Unavailable,
            }
        } else {
            match sat.provider_lookup_raw_pkh_pk(pkh) {
                Some(pk) => {
                    Self::Stack(vec![Placeholder::PubkeyHash(*pkh, params.encoded_key_size(&pk))])
                }
                None => Self::Unavailable,
            }
        }
    }

    /// Turn a key/signature pair related to a pkh into (part of) a satisfaction
    fn pkh_signature<S: AssetProvider<Pk>>(
        sat: &S,
        params: &ValidationParams,
        pkh: &hash160::Hash,
        leaf_hash: Option<TapLeafHash>,
    ) -> Self {
        if let Some(leaf_hash) = leaf_hash {
            match sat.provider_lookup_raw_pkh_tap_leaf_script_sig(&(*pkh, leaf_hash)) {
                Some((pk, size)) => Self::Stack(vec![
                    Placeholder::SchnorrSigPkHash(*pkh, leaf_hash, size),
                    Placeholder::PubkeyHash(*pkh, params.encoded_key_size(&pk)),
                ]),
                None => Self::Impossible,
            }
        } else {
            match sat.provider_lookup_raw_pkh_ecdsa_sig(pkh) {
                Some(pk) => Self::Stack(vec![
                    Placeholder::EcdsaSigPkHash(*pkh),
                    Placeholder::PubkeyHash(*pkh, params.encoded_key_size(&pk)),
                ]),
                None => Self::Impossible,
            }
        }
    }

    /// Turn a hash preimage into (part of) a satisfaction
    fn ripemd160_preimage<S: AssetProvider<Pk>>(sat: &S, h: &Pk::Ripemd160) -> Self {
        if sat.provider_lookup_ripemd160(h) {
            Self::Stack(vec![Placeholder::Ripemd160Preimage(h.clone())])
        // Note hash preimages are unavailable instead of impossible
        } else {
            Self::Unavailable
        }
    }

    /// Turn a hash preimage into (part of) a satisfaction
    fn hash160_preimage<S: AssetProvider<Pk>>(sat: &S, h: &Pk::Hash160) -> Self {
        if sat.provider_lookup_hash160(h) {
            Self::Stack(vec![Placeholder::Hash160Preimage(h.clone())])
        // Note hash preimages are unavailable instead of impossible
        } else {
            Self::Unavailable
        }
    }

    /// Turn a hash preimage into (part of) a satisfaction
    fn sha256_preimage<S: AssetProvider<Pk>>(sat: &S, h: &Pk::Sha256) -> Self {
        if sat.provider_lookup_sha256(h) {
            Self::Stack(vec![Placeholder::Sha256Preimage(h.clone())])
        // Note hash preimages are unavailable instead of impossible
        } else {
            Self::Unavailable
        }
    }

    /// Turn a hash preimage into (part of) a satisfaction
    fn hash256_preimage<S: AssetProvider<Pk>>(sat: &S, h: &Pk::Hash256) -> Self {
        if sat.provider_lookup_hash256(h) {
            Self::Stack(vec![Placeholder::Hash256Preimage(h.clone())])
        // Note hash preimages are unavailable instead of impossible
        } else {
            Self::Unavailable
        }
    }
}

impl<Pk: MiniscriptKey> Witness<Placeholder<Pk>> {
    /// Produce something like a 32-byte 0 push
    fn hash_dissatisfaction() -> Self { Self::Stack(vec![Placeholder::HashDissatisfaction]) }

    /// Construct a satisfaction equivalent to an empty stack
    const fn empty() -> Self { Self::Stack(vec![]) }

    /// Construct a satisfaction equivalent to `OP_1`
    fn push_1() -> Self { Self::Stack(vec![Placeholder::PushOne]) }

    /// Construct a satisfaction equivalent to a single empty push
    fn push_0() -> Self { Self::Stack(vec![Placeholder::PushZero]) }

    /// Concatenate, or otherwise combine, two satisfactions
    fn combine(one: Self, two: Self) -> Self {
        match (one, two) {
            (Self::Impossible, _) | (_, Self::Impossible) => Self::Impossible,
            (Self::Unavailable, _) | (_, Self::Unavailable) => Self::Unavailable,
            (Self::Stack(mut a), Self::Stack(b)) => {
                a.extend(b);
                Self::Stack(a)
            }
        }
    }
}

/// A (dis)satisfaction of a Miniscript fragment
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Satisfaction<T> {
    /// The actual witness stack
    pub stack: Witness<T>,
    /// Whether or not this (dis)satisfaction has a signature somewhere
    /// in it
    pub has_sig: bool,
    /// The absolute timelock used by this satisfaction
    pub absolute_timelock: Option<AbsLockTime>,
    /// The relative timelock used by this satisfaction
    pub relative_timelock: Option<RelLockTime>,
}

impl<Pk: MiniscriptKey + ToPublicKey> Satisfaction<Placeholder<Pk>> {
    /// The empty satisfaction.
    ///
    /// This has the property that, when concatenated on either side with another satisfaction
    /// X, the result will be X.
    fn empty() -> Self {
        Self {
            has_sig: false,
            relative_timelock: None,
            absolute_timelock: None,
            stack: Witness::Stack(vec![]),
        }
    }

    /// Forms a satisfaction which is the concatenation of two satisfactions, with `other`'s
    /// stack before `self`'s.
    ///
    /// This order allows callers to write `left.concatenate_rev(right)` which feels more
    /// natural than the opposite order, and more importantly, allows this method to be
    /// used when folding over an iterator of multiple satisfactions.
    fn concatenate_rev(self, other: Self) -> Self {
        Self {
            has_sig: self.has_sig || other.has_sig,
            relative_timelock: cmp::max(self.relative_timelock, other.relative_timelock),
            absolute_timelock: cmp::max(self.absolute_timelock, other.absolute_timelock),
            stack: Witness::combine(other.stack, self.stack),
        }
    }

    pub(crate) fn build_template<P, Ctx>(
        node: &Miniscript<Pk, Ctx>,
        provider: &P,
        root_has_sig: bool,
        leaf_hash: Option<TapLeafHash>,
    ) -> Self
    where
        Ctx: ScriptContext,
        P: AssetProvider<Pk>,
    {
        Self::dissat_sat(node, provider, false, root_has_sig, leaf_hash).1
    }

    pub(crate) fn build_template_mall<P, Ctx>(
        node: &Miniscript<Pk, Ctx>,
        provider: &P,
        root_has_sig: bool,
        leaf_hash: Option<TapLeafHash>,
    ) -> Self
    where
        Ctx: ScriptContext,
        P: AssetProvider<Pk>,
    {
        Self::dissat_sat(node, provider, true, root_has_sig, leaf_hash).1
    }

    // produce a non-malleable satisafaction for thesh frag
    fn thresh(k: usize, n: usize, dissats: Vec<Self>, mut sats: Vec<Self>) -> Self {
        // Start with the to-return stack set to all dissatisfactions
        let mut ret_stack = dissats;

        // Sort everything by (sat cost - dissat cost), except that
        // satisfactions without signatures beat satisfactions with
        // signatures
        let mut sat_indices = (0..n).collect::<Vec<_>>();
        sat_indices.sort_by_key(|&i| {
            let stack_weight = match (&sats[i].stack, &ret_stack[i].stack) {
                (&Witness::Unavailable, _) | (&Witness::Impossible, _) => i64::MAX,
                // This can only be the case when we have PkH without the corresponding
                // Pubkey.
                (_, &Witness::Unavailable) | (_, &Witness::Impossible) => i64::MIN,
                (Witness::Stack(s), Witness::Stack(d)) => {
                    witness_size(s) as i64 - witness_size(d) as i64
                }
            };
            let is_impossible = sats[i].stack == Witness::Impossible;
            // First consider the candidates that are not impossible to satisfy
            // by any party. Among those first consider the ones that have no sig
            // because third party can malleate them if they are not chosen.
            // Lastly, choose by weight.
            (is_impossible, sats[i].has_sig, stack_weight)
        });

        for i in 0..k {
            mem::swap(&mut ret_stack[sat_indices[i]], &mut sats[sat_indices[i]]);
        }

        // We preferably take satisfactions that are not impossible
        // If we cannot find `k` satisfactions that are not impossible
        // then the threshold branch is impossible to satisfy
        // For example, the fragment thresh(2, hash, 0, 0, 0)
        // is has an impossible witness
        if sats[sat_indices[k - 1]].stack == Witness::Impossible {
            Self {
                stack: Witness::Impossible,
                // If the witness is impossible, we don't care about the
                // has_sig flag, nor about the timelocks
                has_sig: false,
                relative_timelock: None,
                absolute_timelock: None,
            }
        }
        // We are now guaranteed that all elements in `k` satisfactions
        // are not impossible(we sort by is_impossible bool).
        // The above loop should have taken everything without a sig
        // (since those were sorted higher than non-sigs). If there
        // are remaining non-sig satisfactions this indicates a
        // malleability vector
        // For example, the fragment thresh(2, hash, hash, 0, 0)
        // is uniquely satisfyiable because there is no satisfaction
        // for the 0 fragment
        else if !sats[sat_indices[k]].has_sig && sats[sat_indices[k]].stack != Witness::Impossible
        {
            // All arguments should be `d`, so dissatisfactions have no
            // signatures; and in this branch we assume too many weak
            // arguments, so none of the satisfactions should have
            // signatures either.
            for sat in &ret_stack {
                assert!(!sat.has_sig);
            }
            Self {
                stack: Witness::Unavailable,
                has_sig: false,
                relative_timelock: None,
                absolute_timelock: None,
            }
        } else {
            // Otherwise flatten everything out
            ret_stack
                .into_iter()
                .fold(Self::empty(), Self::concatenate_rev)
        }
    }

    // produce a possily malleable satisafaction for thesh frag
    fn thresh_mall(k: usize, n: usize, dissats: Vec<Self>, mut sats: Vec<Self>) -> Self {
        // Start with the to-return stack set to all dissatisfactions
        let mut ret_stack = dissats;

        // Sort everything by (sat cost - dissat cost), except that
        // satisfactions without signatures beat satisfactions with
        // signatures
        let mut sat_indices = (0..n).collect::<Vec<_>>();
        sat_indices.sort_by_key(|&i| {
            // For malleable satifactions, directly choose smallest weights
            match (&sats[i].stack, &ret_stack[i].stack) {
                (&Witness::Unavailable, _) | (&Witness::Impossible, _) => i64::MAX,
                // This is only possible when one of the branches has PkH
                (_, &Witness::Unavailable) | (_, &Witness::Impossible) => i64::MIN,
                (Witness::Stack(s), Witness::Stack(d)) => {
                    witness_size(s) as i64 - witness_size(d) as i64
                }
            }
        });

        // swap the satisfactions
        for i in 0..k {
            mem::swap(&mut ret_stack[sat_indices[i]], &mut sats[sat_indices[i]]);
        }

        // combine the witness
        // no non-malleability checks needed
        ret_stack
            .into_iter()
            .fold(Self::empty(), Self::concatenate_rev)
    }

    fn minimum(sat1: Self, sat2: Self) -> Self {
        // If there is only one available satisfaction, we must choose that
        // regardless of has_sig marker.
        // This handles the case where both are impossible.
        match (&sat1.stack, &sat2.stack) {
            (&Witness::Impossible, _) => return sat2,
            (_, &Witness::Impossible) => return sat1,
            _ => {}
        }
        match (sat1.has_sig, sat2.has_sig) {
            // If neither option has a signature, this is a malleability
            // vector, so choose neither one.
            (false, false) => Self {
                stack: Witness::Unavailable,
                has_sig: false,
                relative_timelock: None,
                absolute_timelock: None,
            },
            // If only one has a signature, take the one that doesn't; a
            // third party could malleate by removing the signature, but
            // can't malleate if he'd have to add it
            (false, true) => Self {
                stack: sat1.stack,
                has_sig: false,
                relative_timelock: sat1.relative_timelock,
                absolute_timelock: sat1.absolute_timelock,
            },
            (true, false) => Self {
                stack: sat2.stack,
                has_sig: false,
                relative_timelock: sat2.relative_timelock,
                absolute_timelock: sat2.absolute_timelock,
            },
            // If both have a signature associated with them, choose the
            // cheaper one (where "cheaper" is defined such that available
            // things are cheaper than unavailable ones)
            (true, true) if sat1.stack < sat2.stack => Self {
                stack: sat1.stack,
                has_sig: true,
                relative_timelock: sat1.relative_timelock,
                absolute_timelock: sat1.absolute_timelock,
            },
            (true, true) => Self {
                stack: sat2.stack,
                has_sig: true,
                relative_timelock: sat2.relative_timelock,
                absolute_timelock: sat2.absolute_timelock,
            },
        }
    }

    // calculate the minimum witness allowing witness malleability
    fn minimum_mall(sat1: Self, sat2: Self) -> Self {
        match (&sat1.stack, &sat2.stack) {
            // If there is only one possible satisfaction, use it regardless
            // of the other one
            (&Witness::Impossible, _) | (&Witness::Unavailable, _) => return sat2,
            (_, &Witness::Impossible) | (_, &Witness::Unavailable) => return sat1,
            _ => {}
        }
        let (stack, absolute_timelock, relative_timelock) = if sat1.stack < sat2.stack {
            (sat1.stack, sat1.absolute_timelock, sat1.relative_timelock)
        } else {
            (sat2.stack, sat2.absolute_timelock, sat2.relative_timelock)
        };
        Self {
            stack,
            // The fragment is has_sig only if both of the
            // fragments are has_sig
            has_sig: sat1.has_sig && sat2.has_sig,
            relative_timelock,
            absolute_timelock,
        }
    }

    /// Try creating the final witness using a [`Satisfier`]
    pub fn try_completing<Sat: Satisfier<Pk>>(&self, stfr: &Sat) -> Option<Satisfaction<Vec<u8>>> {
        let Self { stack, has_sig, relative_timelock, absolute_timelock } = self;
        let stack = match stack {
            Witness::Stack(stack) => Witness::Stack(
                stack
                    .iter()
                    .map(|placeholder| placeholder.satisfy_self(stfr))
                    .collect::<Option<_>>()?,
            ),
            Witness::Unavailable => Witness::Unavailable,
            Witness::Impossible => Witness::Impossible,
        };
        Some(Satisfaction {
            stack,
            has_sig: *has_sig,
            relative_timelock: *relative_timelock,
            absolute_timelock: *absolute_timelock,
        })
    }
}

impl Satisfaction<Vec<u8>> {
    /// Produce a satisfaction non-malleable satisfaction
    pub(super) fn satisfy<Ctx, Pk, Sat>(
        node: &Miniscript<Pk, Ctx>,
        stfr: &Sat,
        root_has_sig: bool,
        leaf_hash: Option<TapLeafHash>,
    ) -> Self
    where
        Ctx: ScriptContext,
        Pk: MiniscriptKey + ToPublicKey,
        Sat: Satisfier<Pk>,
    {
        Satisfaction::<Placeholder<Pk>>::build_template(node, &stfr, root_has_sig, leaf_hash)
            .try_completing(stfr)
            .expect("the same satisfier should manage to complete the template")
    }

    /// Produce a satisfaction(possibly malleable)
    pub(super) fn satisfy_mall<Ctx, Pk, Sat>(
        node: &Miniscript<Pk, Ctx>,
        stfr: &Sat,
        root_has_sig: bool,
        leaf_hash: Option<TapLeafHash>,
    ) -> Self
    where
        Ctx: ScriptContext,
        Pk: MiniscriptKey + ToPublicKey,
        Sat: Satisfier<Pk>,
    {
        Satisfaction::<Placeholder<Pk>>::build_template_mall(node, &stfr, root_has_sig, leaf_hash)
            .try_completing(stfr)
            .expect("the same satisfier should manage to complete the template")
    }
}
