// SPDX-License-Identifier: CC0-1.0

//! A spending plan (or *plan*) is a representation of a particular spending path on a
//! descriptor.
//!
//! This allows us to analayze a choice of spending path without producing any
//! signatures or other witness data for it.
//!
//! To make a plan you provide the descriptor with "assets" like which keys you are able to use, hash
//! pre-images you have access to, absolute/relative timelock constraints etc.
//!
//! Once you've got a plan it can tell you its expected satisfaction weight which can be useful for
//! doing coin selection. Furthermore it provides which subset of those keys and hash pre-images you
//! will actually need as well as what locktime or sequence number you need to set.
//!
//! Once you've obtained signatures, hash pre-images etc required by the plan, it can create a
//! witness/script_sig for the input.

use core::iter::FromIterator;

use bitcoin::hashes::{hash160, ripemd160, sha256};
use bitcoin::key::XOnlyPublicKey;
use bitcoin::script::PushBytesBuf;
use bitcoin::taproot::{ControlBlock, LeafVersion, TapLeafHash};
use bitcoin::{absolute, bip32, psbt, relative, ScriptBuf, WitnessVersion};

use crate::descriptor::{self, Descriptor, DescriptorType, KeyMap};
use crate::miniscript::hash256;
use crate::miniscript::satisfy::{Placeholder, Satisfier, SchnorrSigType};
use crate::prelude::*;
use crate::util::witness_size;
use crate::{DefiniteDescriptorKey, DescriptorPublicKey, Error, MiniscriptKey, ToPublicKey};

/// Trait describing a present/missing lookup table for constructing witness templates
///
/// This trait mirrors the [`Satisfier`] trait, with the difference that most methods just return a
/// boolean indicating the item presence. The methods looking up keys return the key
/// length, the methods looking up public key hashes return the public key, and a few other methods
/// need to return the item itself.
///
/// This trait is automatically implemented for every type that is also a satisfier, and simply
/// proxies the queries to the satisfier and returns whether an item is available or not.
///
/// All the methods have a default implementation that returns `false` or `None`.
pub trait AssetProvider<Pk: MiniscriptKey> {
    /// Given a public key, look up an ECDSA signature with that key, return whether we found it
    fn provider_lookup_ecdsa_sig(&self, _: &Pk) -> bool { false }

    /// Lookup the tap key spend sig and return its size
    fn provider_lookup_tap_key_spend_sig(&self, _: &Pk) -> Option<usize> { None }

    /// Given a public key and a associated leaf hash, look up a schnorr signature with that key
    /// and return its size
    fn provider_lookup_tap_leaf_script_sig(&self, _: &Pk, _: &TapLeafHash) -> Option<usize> { None }

    /// Given a raw `Pkh`, lookup corresponding [`bitcoin::PublicKey`]
    fn provider_lookup_raw_pkh_pk(&self, _: &hash160::Hash) -> Option<bitcoin::PublicKey> { None }

    /// Given a raw `Pkh`, lookup corresponding [`bitcoin::secp256k1::XOnlyPublicKey`]
    fn provider_lookup_raw_pkh_x_only_pk(&self, _: &hash160::Hash) -> Option<XOnlyPublicKey> {
        None
    }

    /// Given a keyhash, look up the EC signature and the associated key.
    ///
    /// Returns the key if a signature is found.
    ///
    /// Even if signatures for public key Hashes are not available, the users
    /// can use this map to provide pkh -> pk mapping which can be useful
    /// for dissatisfying pkh.
    fn provider_lookup_raw_pkh_ecdsa_sig(&self, _: &hash160::Hash) -> Option<bitcoin::PublicKey> {
        None
    }

    /// Given a keyhash, look up the schnorr signature and the associated key.
    ///
    /// Returns the key and sig len if a signature is found.
    ///
    /// Even if signatures for public key Hashes are not available, the users
    /// can use this map to provide pkh -> pk mapping which can be useful
    /// for dissatisfying pkh.
    fn provider_lookup_raw_pkh_tap_leaf_script_sig(
        &self,
        _: &(hash160::Hash, TapLeafHash),
    ) -> Option<(XOnlyPublicKey, usize)> {
        None
    }

    /// Given a SHA256 hash, look up its preimage, return whether we found it
    fn provider_lookup_sha256(&self, _: &Pk::Sha256) -> bool { false }

    /// Given a HASH256 hash, look up its preimage, return whether we found it
    fn provider_lookup_hash256(&self, _: &Pk::Hash256) -> bool { false }

    /// Given a RIPEMD160 hash, look up its preimage, return whether we found it
    fn provider_lookup_ripemd160(&self, _: &Pk::Ripemd160) -> bool { false }

    /// Given a HASH160 hash, look up its preimage, return whether we found it
    fn provider_lookup_hash160(&self, _: &Pk::Hash160) -> bool { false }

    /// Assert whether a relative locktime is satisfied
    fn check_older(&self, _: relative::LockTime) -> bool { false }

    /// Assert whether an absolute locktime is satisfied
    fn check_after(&self, _: absolute::LockTime) -> bool { false }
}

/// Wrapper around [`Assets`] that logs every query and value returned
#[cfg(feature = "std")]
pub struct LoggerAssetProvider<'a>(pub &'a Assets);

#[cfg(feature = "std")]
macro_rules! impl_log_method {
    ( $name:ident, $( <$ctx:ident: ScriptContext > )? $( $arg:ident : $ty:ty, )* -> $ret_ty:ty ) => {
        fn $name $( <$ctx: ScriptContext> )? ( &self, $( $arg:$ty ),* ) -> $ret_ty {
            let ret = (self.0).$name $( ::<$ctx> )*( $( $arg ),* );
            dbg!(stringify!( $name ), ( $( $arg ),* ), &ret);

            ret
        }
    }
}

#[cfg(feature = "std")]
impl AssetProvider<DefiniteDescriptorKey> for LoggerAssetProvider<'_> {
    impl_log_method!(provider_lookup_ecdsa_sig, pk: &DefiniteDescriptorKey, -> bool);
    impl_log_method!(provider_lookup_tap_key_spend_sig, pk: &DefiniteDescriptorKey, -> Option<usize>);
    impl_log_method!(provider_lookup_tap_leaf_script_sig, pk: &DefiniteDescriptorKey, leaf_hash: &TapLeafHash, -> Option<usize>);
    impl_log_method!(provider_lookup_raw_pkh_pk, hash: &hash160::Hash, -> Option<bitcoin::PublicKey>);
    impl_log_method!(provider_lookup_raw_pkh_x_only_pk, hash: &hash160::Hash, -> Option<XOnlyPublicKey>);
    impl_log_method!(provider_lookup_raw_pkh_ecdsa_sig, hash: &hash160::Hash, -> Option<bitcoin::PublicKey>);
    impl_log_method!(provider_lookup_raw_pkh_tap_leaf_script_sig, hash: &(hash160::Hash, TapLeafHash), -> Option<(XOnlyPublicKey, usize)>);
    impl_log_method!(provider_lookup_sha256, hash: &sha256::Hash, -> bool);
    impl_log_method!(provider_lookup_hash256, hash: &hash256::Hash, -> bool);
    impl_log_method!(provider_lookup_ripemd160, hash: &ripemd160::Hash, -> bool);
    impl_log_method!(provider_lookup_hash160, hash: &hash160::Hash, -> bool);
    impl_log_method!(check_older, s: relative::LockTime, -> bool);
    impl_log_method!(check_after, t: absolute::LockTime, -> bool);
}

impl<T, Pk> AssetProvider<Pk> for T
where
    T: Satisfier<Pk>,
    Pk: MiniscriptKey + ToPublicKey,
{
    fn provider_lookup_ecdsa_sig(&self, pk: &Pk) -> bool {
        Satisfier::lookup_ecdsa_sig(self, pk).is_some()
    }

    fn provider_lookup_tap_key_spend_sig(&self, pk: &Pk) -> Option<usize> {
        Satisfier::lookup_tap_key_spend_sig(self, pk).map(|s| s.to_vec().len())
    }

    fn provider_lookup_tap_leaf_script_sig(
        &self,
        pk: &Pk,
        leaf_hash: &TapLeafHash,
    ) -> Option<usize> {
        Satisfier::lookup_tap_leaf_script_sig(self, pk, leaf_hash).map(|s| s.to_vec().len())
    }

    fn provider_lookup_raw_pkh_pk(&self, hash: &hash160::Hash) -> Option<bitcoin::PublicKey> {
        Satisfier::lookup_raw_pkh_pk(self, hash)
    }

    fn provider_lookup_raw_pkh_x_only_pk(&self, hash: &hash160::Hash) -> Option<XOnlyPublicKey> {
        Satisfier::lookup_raw_pkh_x_only_pk(self, hash)
    }

    fn provider_lookup_raw_pkh_ecdsa_sig(
        &self,
        hash: &hash160::Hash,
    ) -> Option<bitcoin::PublicKey> {
        Satisfier::lookup_raw_pkh_ecdsa_sig(self, hash).map(|(pk, _)| pk)
    }

    fn provider_lookup_raw_pkh_tap_leaf_script_sig(
        &self,
        hash: &(hash160::Hash, TapLeafHash),
    ) -> Option<(XOnlyPublicKey, usize)> {
        Satisfier::lookup_raw_pkh_tap_leaf_script_sig(self, hash)
            .map(|(pk, sig)| (pk, sig.to_vec().len()))
    }

    fn provider_lookup_sha256(&self, hash: &Pk::Sha256) -> bool {
        Satisfier::lookup_sha256(self, hash).is_some()
    }

    fn provider_lookup_hash256(&self, hash: &Pk::Hash256) -> bool {
        Satisfier::lookup_hash256(self, hash).is_some()
    }

    fn provider_lookup_ripemd160(&self, hash: &Pk::Ripemd160) -> bool {
        Satisfier::lookup_ripemd160(self, hash).is_some()
    }

    fn provider_lookup_hash160(&self, hash: &Pk::Hash160) -> bool {
        Satisfier::lookup_hash160(self, hash).is_some()
    }

    fn check_older(&self, s: relative::LockTime) -> bool { Satisfier::check_older(self, s) }

    fn check_after(&self, l: absolute::LockTime) -> bool { Satisfier::check_after(self, l) }
}

/// Representation of a particular spending path on a descriptor.
///
/// Contains the witness template
/// and the timelocks needed for satisfying the plan.
/// Calling `plan` on a Descriptor will return this structure,
/// containing the cheapest spending path possible (considering the `Assets` given)
#[derive(Debug, Clone)]
pub struct Plan {
    /// This plan's witness template
    pub(crate) template: Vec<Placeholder<DefiniteDescriptorKey>>,
    /// The absolute timelock this plan uses
    pub absolute_timelock: Option<absolute::LockTime>,
    /// The relative timelock this plan uses
    pub relative_timelock: Option<relative::LockTime>,

    pub(crate) descriptor: Descriptor<DefiniteDescriptorKey>,
}

impl Plan {
    /// Returns the witness template
    pub fn witness_template(&self) -> &Vec<Placeholder<DefiniteDescriptorKey>> { &self.template }

    /// Returns the witness version
    pub fn witness_version(&self) -> Option<WitnessVersion> {
        self.descriptor.desc_type().segwit_version()
    }

    /// The weight, in witness units, needed for satisfying this plan (includes both
    /// the script sig weight and the witness weight)
    pub fn satisfaction_weight(&self) -> usize { self.witness_size() + self.scriptsig_size() * 4 }

    /// The size in bytes of the script sig that satisfies this plan, including the size of the
    /// var-int prefix.
    pub fn scriptsig_size(&self) -> usize {
        match (self.descriptor.desc_type().segwit_version(), self.descriptor.desc_type()) {
            // Entire witness goes in the script_sig
            (None, _) => witness_size(self.template.as_ref()),
            // Taproot doesn't have a "wrapped" version (scriptSig len (1))
            (Some(WitnessVersion::V1), _) => 1,
            // scriptSig len (1) + OP_0 (1) + OP_PUSHBYTES_20 (1) + <pk hash> (20)
            (_, DescriptorType::ShWpkh) => 1 + 1 + 1 + 20,
            // scriptSig len (1) + OP_0 (1) + OP_PUSHBYTES_32 (1) + <script hash> (32)
            (_, DescriptorType::ShWsh) | (_, DescriptorType::ShWshSortedMulti) => 1 + 1 + 1 + 32,
            // Native Segwit v0 (scriptSig len (1))
            _ => 1,
        }
    }

    /// The size in bytes of the witness that satisfies this plan.
    ///
    /// NOTE: Returns 0 if there is no witness. You need to manually take care to count it as 1 byte
    /// if there's at least one segwit input in the tx. See ["Empty script witnesses are encoded as a zero byte"](https://github.com/bitcoin/bips/blob/d8a56c9f2b521bf4af5d588f217e7618cc44952c/bip-0144.mediawiki#serialization).
    pub fn witness_size(&self) -> usize {
        if self.descriptor.desc_type().segwit_version().is_some() {
            witness_size(self.template.as_ref())
        } else {
            0
        }
    }

    /// Try creating the final script_sig and witness using a [`Satisfier`]
    pub fn satisfy<Sat: Satisfier<DefiniteDescriptorKey>>(
        &self,
        stfr: &Sat,
    ) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error> {
        use bitcoin::blockdata::script::Builder;

        let stack = self
            .template
            .iter()
            .map(|placeholder| placeholder.satisfy_self(stfr))
            .collect::<Option<Vec<Vec<u8>>>>()
            .ok_or(Error::CouldNotSatisfy)?;

        Ok(match self.descriptor.desc_type() {
            DescriptorType::Bare
            | DescriptorType::Sh
            | DescriptorType::Pkh
            | DescriptorType::ShSortedMulti => (
                vec![],
                stack
                    .into_iter()
                    .fold(Builder::new(), |builder, item| {
                        let bytes = PushBytesBuf::try_from(item)
                            .expect("All the possible placeholders can be made into PushBytesBuf");
                        builder.push_slice(bytes)
                    })
                    .into_script(),
            ),
            DescriptorType::Wpkh
            | DescriptorType::Wsh
            | DescriptorType::WshSortedMulti
            | DescriptorType::Tr => (stack, ScriptBuf::new()),
            DescriptorType::ShWsh | DescriptorType::ShWshSortedMulti | DescriptorType::ShWpkh => {
                (stack, self.descriptor.unsigned_script_sig())
            }
        })
    }

    /// Update a PSBT input with the metadata required to complete this plan
    ///
    /// This will only add the metadata for items required to complete this plan. For example, if
    /// there are multiple keys present in the descriptor, only the few used by this plan will be
    /// added to the PSBT.
    pub fn update_psbt_input(&self, input: &mut psbt::Input) {
        if let Descriptor::Tr(tr) = &self.descriptor {
            enum SpendType {
                KeySpend { internal_key: XOnlyPublicKey },
                ScriptSpend { leaf_hash: TapLeafHash },
            }

            #[derive(Default)]
            struct TrDescriptorData {
                tap_script: Option<ScriptBuf>,
                control_block: Option<ControlBlock>,
                spend_type: Option<SpendType>,
                key_origins: BTreeMap<XOnlyPublicKey, bip32::KeySource>,
            }

            let spend_info = tr.spend_info();
            input.tap_merkle_root = spend_info.merkle_root();

            let data = self
                .template
                .iter()
                .fold(TrDescriptorData::default(), |mut data, item| {
                    match item {
                        Placeholder::TapScript(script) => data.tap_script = Some(script.clone()),
                        Placeholder::TapControlBlock(cb) => data.control_block = Some(cb.clone()),
                        Placeholder::SchnorrSigPk(pk, sig_type, _) => {
                            let raw_pk = pk.to_x_only_pubkey();

                            match (&data.spend_type, sig_type) {
                                // First encountered schnorr sig, update the `TrDescriptorData` accordingly
                                (None, SchnorrSigType::KeySpend { .. }) => data.spend_type = Some(SpendType::KeySpend { internal_key: raw_pk }),
                                (None, SchnorrSigType::ScriptSpend { leaf_hash }) => data.spend_type = Some(SpendType::ScriptSpend { leaf_hash: *leaf_hash }),

                                // Inconsistent placeholders (should be unreachable with the
                                // current implementation)
                                (Some(SpendType::KeySpend {..}), SchnorrSigType::ScriptSpend { .. }) | (Some(SpendType::ScriptSpend {..}), SchnorrSigType::KeySpend{..}) => unreachable!("Mixed taproot key-spend and script-spend placeholders in the same plan"),

                                _ => {},
                            }

                            for path in pk.full_derivation_paths() {
                                data.key_origins.insert(raw_pk, (pk.master_fingerprint(), path));
                            }
                        }
                        Placeholder::SchnorrSigPkHash(_, tap_leaf_hash, _) => {
                            data.spend_type = Some(SpendType::ScriptSpend { leaf_hash: *tap_leaf_hash });
                        }
                        _ => {}
                    }

                    data
                });

            // TODO: TapTree. we need to re-traverse the tree to build it, sigh

            let leaf_hash = match data.spend_type {
                Some(SpendType::KeySpend { internal_key }) => {
                    input.tap_internal_key = Some(internal_key);
                    None
                }
                Some(SpendType::ScriptSpend { leaf_hash }) => Some(leaf_hash),
                _ => None,
            };
            for (pk, key_source) in data.key_origins {
                input
                    .tap_key_origins
                    .entry(pk)
                    .and_modify(|(leaf_hashes, _)| {
                        if let Some(lh) = leaf_hash {
                            if leaf_hashes.iter().all(|&i| i != lh) {
                                leaf_hashes.push(lh);
                            }
                        }
                    })
                    .or_insert_with(|| (vec![], key_source));
            }
            if let (Some(tap_script), Some(control_block)) = (data.tap_script, data.control_block) {
                input
                    .tap_scripts
                    .insert(control_block, (tap_script, LeafVersion::TapScript));
            }
        } else {
            for item in &self.template {
                if let Placeholder::EcdsaSigPk(pk) = item {
                    let public_key = pk.to_public_key().inner;
                    let master_fingerprint = pk.master_fingerprint();
                    for derivation_path in pk.full_derivation_paths() {
                        input
                            .bip32_derivation
                            .insert(public_key, (master_fingerprint, derivation_path));
                    }
                }
            }

            match &self.descriptor {
                Descriptor::Bare(_) | Descriptor::Pkh(_) | Descriptor::Wpkh(_) => {}
                Descriptor::Sh(sh) => match sh.as_inner() {
                    descriptor::ShInner::Wsh(wsh) => {
                        input.witness_script = Some(wsh.inner_script());
                        input.redeem_script = Some(wsh.inner_script().to_p2wsh());
                    }
                    descriptor::ShInner::Wpkh(..) => input.redeem_script = Some(sh.inner_script()),
                    descriptor::ShInner::SortedMulti(_) | descriptor::ShInner::Ms(_) => {
                        input.redeem_script = Some(sh.inner_script())
                    }
                },
                Descriptor::Wsh(wsh) => input.witness_script = Some(wsh.inner_script()),
                Descriptor::Tr(_) => unreachable!("Tr is dealt with separately"),
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// Signatures which a key can produce
///
/// Defaults to `ecdsa=true` and `taproot=TaprootCanSign::default()`
pub struct CanSign {
    /// Whether the key can produce ECDSA signatures
    pub ecdsa: bool,
    /// Whether the key can produce taproot (Schnorr) signatures
    pub taproot: TaprootCanSign,
}

impl Default for CanSign {
    fn default() -> Self { Self { ecdsa: true, taproot: TaprootCanSign::default() } }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// Signatures which a taproot key can produce
///
/// Defaults to `key_spend=true`, `script_spend=Any` and `sighash_default=true`
pub struct TaprootCanSign {
    /// Can produce key spend signatures
    pub key_spend: bool,
    /// Can produce script spend signatures
    pub script_spend: TaprootAvailableLeaves,
    /// Whether `SIGHASH_DEFAULT` will be used to sign
    pub sighash_default: bool,
}

impl TaprootCanSign {
    fn sig_len(&self) -> usize {
        match self.sighash_default {
            true => 64,
            false => 65,
        }
    }
}

impl Default for TaprootCanSign {
    fn default() -> Self {
        Self {
            key_spend: true,
            script_spend: TaprootAvailableLeaves::Any,
            sighash_default: true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// Which taproot leaves the key can sign for
pub enum TaprootAvailableLeaves {
    /// Cannot sign for any leaf
    None,
    /// Can sign for any leaf
    Any,
    /// Can sign only for a specific leaf
    Single(TapLeafHash),
    /// Can sign for multiple leaves
    Many(Vec<TapLeafHash>),
}

impl TaprootAvailableLeaves {
    fn is_available(&self, lh: &TapLeafHash) -> bool {
        use TaprootAvailableLeaves::*;

        match self {
            None => false,
            Any => true,
            Single(v) => v == lh,
            Many(list) => list.contains(lh),
        }
    }
}

/// The Assets we can use to satisfy a particular spending path
#[derive(Debug, Default)]
pub struct Assets {
    /// Keys the user can sign for, and how.
    ///
    /// A pair `(fingerprint, derivation_path)` is
    /// provided, meaning that the user can sign using the key with `fingerprint`,
    /// derived with either `derivation_path` or a derivation path that extends `derivation_path`
    /// by exactly one child number. For example, if the derivation path `m/0/1` is provided, the
    /// user can sign with either `m/0/1` or `m/0/1/*`.
    pub keys: BTreeSet<(bip32::KeySource, CanSign)>,
    /// Set of available sha256 preimages
    pub sha256_preimages: BTreeSet<sha256::Hash>,
    /// Set of available hash256 preimages
    pub hash256_preimages: BTreeSet<hash256::Hash>,
    /// Set of available ripemd160 preimages
    pub ripemd160_preimages: BTreeSet<ripemd160::Hash>,
    /// Set of available hash160 preimages
    pub hash160_preimages: BTreeSet<hash160::Hash>,
    /// Maximum absolute timelock allowed
    pub absolute_timelock: Option<absolute::LockTime>,
    /// Maximum relative timelock allowed
    pub relative_timelock: Option<relative::LockTime>,
}

// Checks if the `pk` is a "direct child" of the `derivation_path` provided.
// Direct child means that the key derivation path is either the same as the
// `derivation_path`, or the same extened by exactly one child number.
// For example, `pk/0/1/2` is a direct child of `m/0/1` and of `m/0/1/2`,
// but not of `m/0`.
fn is_key_direct_child_of(
    pk: &DefiniteDescriptorKey,
    derivation_path: &bip32::DerivationPath,
) -> bool {
    for pk_derivation_path in pk.full_derivation_paths() {
        if &pk_derivation_path == derivation_path {
            return true;
        }

        let definite_path_len = pk_derivation_path.len();
        if derivation_path.as_ref() == &pk_derivation_path[..(definite_path_len - 1)] {
            return true;
        }
    }

    false
}

impl Assets {
    pub(crate) fn has_ecdsa_key(&self, pk: &DefiniteDescriptorKey) -> bool {
        self.keys.iter().any(|(keysource, can_sign)| {
            can_sign.ecdsa
                && pk.master_fingerprint() == keysource.0
                && is_key_direct_child_of(pk, &keysource.1)
        })
    }

    pub(crate) fn has_taproot_internal_key(&self, pk: &DefiniteDescriptorKey) -> Option<usize> {
        self.keys.iter().find_map(|(keysource, can_sign)| {
            if !can_sign.taproot.key_spend
                || pk.master_fingerprint() != keysource.0
                || !is_key_direct_child_of(pk, &keysource.1)
            {
                None
            } else {
                Some(can_sign.taproot.sig_len())
            }
        })
    }

    pub(crate) fn has_taproot_script_key(
        &self,
        pk: &DefiniteDescriptorKey,
        tap_leaf_hash: &TapLeafHash,
    ) -> Option<usize> {
        self.keys.iter().find_map(|(keysource, can_sign)| {
            if !can_sign.taproot.script_spend.is_available(tap_leaf_hash)
                || pk.master_fingerprint() != keysource.0
                || !is_key_direct_child_of(pk, &keysource.1)
            {
                None
            } else {
                Some(can_sign.taproot.sig_len())
            }
        })
    }
}

impl AssetProvider<DefiniteDescriptorKey> for Assets {
    fn provider_lookup_ecdsa_sig(&self, pk: &DefiniteDescriptorKey) -> bool {
        self.has_ecdsa_key(pk)
    }

    fn provider_lookup_tap_key_spend_sig(&self, pk: &DefiniteDescriptorKey) -> Option<usize> {
        self.has_taproot_internal_key(pk)
    }

    fn provider_lookup_tap_leaf_script_sig(
        &self,
        pk: &DefiniteDescriptorKey,
        tap_leaf_hash: &TapLeafHash,
    ) -> Option<usize> {
        self.has_taproot_script_key(pk, tap_leaf_hash)
    }

    fn provider_lookup_sha256(&self, hash: &sha256::Hash) -> bool {
        self.sha256_preimages.contains(hash)
    }

    fn provider_lookup_hash256(&self, hash: &hash256::Hash) -> bool {
        self.hash256_preimages.contains(hash)
    }

    fn provider_lookup_ripemd160(&self, hash: &ripemd160::Hash) -> bool {
        self.ripemd160_preimages.contains(hash)
    }

    fn provider_lookup_hash160(&self, hash: &hash160::Hash) -> bool {
        self.hash160_preimages.contains(hash)
    }

    fn check_older(&self, s: relative::LockTime) -> bool {
        if let Some(timelock) = self.relative_timelock {
            s.is_implied_by(timelock)
        } else {
            false
        }
    }

    fn check_after(&self, l: absolute::LockTime) -> bool {
        if let Some(timelock) = self.absolute_timelock {
            l.is_implied_by(timelock)
        } else {
            false
        }
    }
}

impl FromIterator<DescriptorPublicKey> for Assets {
    fn from_iter<I: IntoIterator<Item = DescriptorPublicKey>>(iter: I) -> Self {
        let mut keys = BTreeSet::new();
        for pk in iter {
            for deriv_path in pk.full_derivation_paths() {
                keys.insert(((pk.master_fingerprint(), deriv_path), CanSign::default()));
            }
        }
        Self { keys, ..Default::default() }
    }
}

/// Conversion into a `Assets`
pub trait IntoAssets {
    /// Convert `self` into a `Assets` struct
    fn into_assets(self) -> Assets;
}

impl IntoAssets for KeyMap {
    fn into_assets(self) -> Assets { Assets::from_iter(self.into_iter().map(|(k, _)| k)) }
}

impl IntoAssets for DescriptorPublicKey {
    fn into_assets(self) -> Assets { vec![self].into_assets() }
}

impl IntoAssets for Vec<DescriptorPublicKey> {
    fn into_assets(self) -> Assets { Assets::from_iter(self) }
}

impl IntoAssets for sha256::Hash {
    fn into_assets(self) -> Assets {
        Assets { sha256_preimages: vec![self].into_iter().collect(), ..Default::default() }
    }
}

impl IntoAssets for hash256::Hash {
    fn into_assets(self) -> Assets {
        Assets { hash256_preimages: vec![self].into_iter().collect(), ..Default::default() }
    }
}

impl IntoAssets for ripemd160::Hash {
    fn into_assets(self) -> Assets {
        Assets { ripemd160_preimages: vec![self].into_iter().collect(), ..Default::default() }
    }
}

impl IntoAssets for hash160::Hash {
    fn into_assets(self) -> Assets {
        Assets { hash160_preimages: vec![self].into_iter().collect(), ..Default::default() }
    }
}

impl IntoAssets for Assets {
    fn into_assets(self) -> Assets { self }
}

impl Assets {
    /// Contruct an empty instance
    pub fn new() -> Self { Self::default() }

    /// Add some assets
    #[allow(clippy::should_implement_trait)] // looks like the `ops::Add` trait
    pub fn add<A: IntoAssets>(mut self, asset: A) -> Self {
        self.append(asset.into_assets());
        self
    }

    /// Set the maximum relative timelock allowed
    pub fn older(mut self, seq: relative::LockTime) -> Self {
        self.relative_timelock = Some(seq);
        self
    }

    /// Set the maximum absolute timelock allowed
    pub fn after(mut self, lt: absolute::LockTime) -> Self {
        self.absolute_timelock = Some(lt);
        self
    }

    fn append(&mut self, b: Self) {
        self.keys.extend(b.keys);
        self.sha256_preimages.extend(b.sha256_preimages);
        self.hash256_preimages.extend(b.hash256_preimages);
        self.ripemd160_preimages.extend(b.ripemd160_preimages);
        self.hash160_preimages.extend(b.hash160_preimages);

        self.relative_timelock = b.relative_timelock.or(self.relative_timelock);
        self.absolute_timelock = b.absolute_timelock.or(self.absolute_timelock);
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use bitcoin::bip32::Xpub;

    use super::*;
    use crate::*;

    #[allow(clippy::type_complexity)]
    fn test_inner(
        desc: &str,
        keys: Vec<DescriptorPublicKey>,
        hashes: Vec<hash160::Hash>,
        // [ (key_indexes, hash_indexes, older, after, expected) ]
        tests: Vec<(
            Vec<usize>,
            Vec<usize>,
            Option<relative::LockTime>,
            Option<absolute::LockTime>,
            Option<usize>,
        )>,
    ) {
        let desc = Descriptor::<DefiniteDescriptorKey>::from_str(desc).unwrap();

        for (key_indexes, hash_indexes, older, after, expected) in tests {
            let mut assets = Assets::new();
            if let Some(seq) = older {
                assets = assets.older(seq);
            }
            if let Some(locktime) = after {
                assets = assets.after(locktime);
            }
            for ki in key_indexes {
                assets = assets.add(keys[ki].clone());
            }
            for hi in hash_indexes {
                assets = assets.add(hashes[hi]);
            }

            let result = desc.clone().plan(&assets);
            assert_eq!(
                result.as_ref().ok().map(|plan| plan.satisfaction_weight()),
                expected,
                "{:#?}",
                result
            );
        }
    }

    #[test]
    fn test_or() {
        let keys = vec![
            DescriptorPublicKey::from_str(
                "02c2fd50ceae468857bb7eb32ae9cd4083e6c7e42fbbec179d81134b3e3830586c",
            )
            .unwrap(),
            DescriptorPublicKey::from_str(
                "0257f4a2816338436cccabc43aa724cf6e69e43e84c3c8a305212761389dd73a8a",
            )
            .unwrap(),
        ];
        let hashes = vec![];
        let desc = format!("wsh(t:or_c(pk({}),v:pkh({})))", keys[0], keys[1]);

        // expected weight: 4 (scriptSig len) + 1 (witness len) + 73 (sig)
        let tests = vec![
            (vec![], vec![], None, None, None),
            (vec![0], vec![], None, None, Some(4 + 1 + 73)),
            (vec![0, 1], vec![], None, None, Some(4 + 1 + 73)),
        ];

        test_inner(&desc, keys, hashes, tests);
    }

    #[test]
    fn test_and() {
        let keys = vec![
            DescriptorPublicKey::from_str(
                "02c2fd50ceae468857bb7eb32ae9cd4083e6c7e42fbbec179d81134b3e3830586c",
            )
            .unwrap(),
            DescriptorPublicKey::from_str(
                "0257f4a2816338436cccabc43aa724cf6e69e43e84c3c8a305212761389dd73a8a",
            )
            .unwrap(),
        ];
        let hashes = vec![];
        let desc = format!("wsh(and_v(v:pk({}),pk({})))", keys[0], keys[1]);

        // expected weight: 4 (scriptSig len) + 1 (witness len) + 73 (sig) * 2
        let tests = vec![
            (vec![], vec![], None, None, None),
            (vec![0], vec![], None, None, None),
            (vec![0, 1], vec![], None, None, Some(4 + 1 + 73 * 2)),
        ];

        test_inner(&desc, keys, hashes, tests);
    }

    #[test]
    fn test_multi() {
        let keys = vec![
            DescriptorPublicKey::from_str(
                "02c2fd50ceae468857bb7eb32ae9cd4083e6c7e42fbbec179d81134b3e3830586c",
            )
            .unwrap(),
            DescriptorPublicKey::from_str(
                "0257f4a2816338436cccabc43aa724cf6e69e43e84c3c8a305212761389dd73a8a",
            )
            .unwrap(),
            DescriptorPublicKey::from_str(
                "03500a2b48b0f66c8183cc0d6645ab21cc19c7fad8a33ff04d41c3ece54b0bc1c5",
            )
            .unwrap(),
            DescriptorPublicKey::from_str(
                "033ad2d191da4f39512adbaac320cae1f12f298386a4e9d43fd98dec7cf5db2ac9",
            )
            .unwrap(),
        ];
        let hashes = vec![];
        let desc = format!("wsh(multi(3,{},{},{},{}))", keys[0], keys[1], keys[2], keys[3]);

        let tests = vec![
            (vec![], vec![], None, None, None),
            (vec![0, 1], vec![], None, None, None),
            // expected weight: 4 (scriptSig len) + 1 (witness len) + 73 (sig) * 3 + 1 (dummy push)
            (vec![0, 1, 3], vec![], None, None, Some(4 + 1 + 73 * 3 + 1)),
        ];

        test_inner(&desc, keys, hashes, tests);
    }

    #[test]
    fn test_thresh() {
        // relative::LockTime has no constructors except by going through Sequence
        use bitcoin::Sequence;
        let keys = vec![
            DescriptorPublicKey::from_str(
                "02c2fd50ceae468857bb7eb32ae9cd4083e6c7e42fbbec179d81134b3e3830586c",
            )
            .unwrap(),
            DescriptorPublicKey::from_str(
                "0257f4a2816338436cccabc43aa724cf6e69e43e84c3c8a305212761389dd73a8a",
            )
            .unwrap(),
        ];
        let hashes = vec![];
        let desc = format!("wsh(thresh(2,pk({}),s:pk({}),snl:older(144)))", keys[0], keys[1]);

        let tests = vec![
            (vec![], vec![], None, None, None),
            (
                vec![],
                vec![],
                Some(Sequence(1000).to_relative_lock_time().unwrap()),
                None,
                None,
            ),
            (vec![0], vec![], None, None, None),
            // expected weight: 4 (scriptSig len) + 1 (witness len) + 73 (sig) + 1 (OP_0) + 1 (OP_ZERO)
            (
                vec![0],
                vec![],
                Some(Sequence(1000).to_relative_lock_time().unwrap()),
                None,
                Some(80),
            ),
            // expected weight: 4 (scriptSig len) + 1 (witness len) + 73 (sig) * 2 + 2 (OP_PUSHBYTE_1 0x01)
            (vec![0, 1], vec![], None, None, Some(153)),
            // expected weight: 4 (scriptSig len) + 1 (witness len) + 73 (sig) + 1 (OP_0) + 1 (OP_ZERO)
            (
                vec![0, 1],
                vec![],
                Some(Sequence(1000).to_relative_lock_time().unwrap()),
                None,
                Some(80),
            ),
            // expected weight: 4 (scriptSig len) + 1 (witness len) + 73 (sig) * 2 + 2 (OP_PUSHBYTE_1 0x01)
            (
                vec![0, 1],
                vec![],
                Some(
                    Sequence::from_512_second_intervals(10)
                        .to_relative_lock_time()
                        .unwrap(),
                ),
                None,
                Some(153),
            ), // incompatible timelock
        ];

        test_inner(&desc, keys.clone(), hashes.clone(), tests);

        let desc = format!("wsh(thresh(2,pk({}),s:pk({}),snl:after(144)))", keys[0], keys[1]);

        let tests = vec![
            // expected weight: 4 (scriptSig len) + 1 (witness len) + 73 (sig) + 1 (OP_0) + 1 (OP_ZERO)
            (
                vec![0],
                vec![],
                None,
                Some(absolute::LockTime::from_height(1000).unwrap()),
                Some(80),
            ),
            // expected weight: 4 (scriptSig len) + 1 (witness len) + 73 (sig) * 2 + 2 (OP_PUSHBYTE_1 0x01)
            (
                vec![0, 1],
                vec![],
                None,
                Some(absolute::LockTime::from_time(500_001_000).unwrap()),
                Some(153),
            ), // incompatible timelock
        ];

        test_inner(&desc, keys, hashes, tests);
    }

    #[test]
    fn test_taproot() {
        let keys = vec![
            DescriptorPublicKey::from_str(
                "02c2fd50ceae468857bb7eb32ae9cd4083e6c7e42fbbec179d81134b3e3830586c",
            )
            .unwrap(),
            DescriptorPublicKey::from_str(
                "0257f4a2816338436cccabc43aa724cf6e69e43e84c3c8a305212761389dd73a8a",
            )
            .unwrap(),
            DescriptorPublicKey::from_str(
                "03500a2b48b0f66c8183cc0d6645ab21cc19c7fad8a33ff04d41c3ece54b0bc1c5",
            )
            .unwrap(),
            DescriptorPublicKey::from_str(
                "033ad2d191da4f39512adbaac320cae1f12f298386a4e9d43fd98dec7cf5db2ac9",
            )
            .unwrap(),
            DescriptorPublicKey::from_str(
                "023fc33527afab09fa97135f2180bcd22ce637b1d2fbcb2db748b1f2c33f45b2b4",
            )
            .unwrap(),
        ];
        let hashes = vec![];
        //    .
        //   / \
        //  .   .
        //  A  / \
        //    .   .
        //    B   C
        //  where A = pk(key1)
        //        B = multi(1, key2, key3)
        //        C = and(key4, after(10))
        let desc = format!(
            "tr({},{{pk({}),{{multi_a(1,{},{}),and_v(v:pk({}),after(10))}}}})",
            keys[0], keys[1], keys[2], keys[3], keys[4]
        );

        // expected weight: 4 (scriptSig len) + 1 (witness len) + 1 (OP_PUSH) + 64 (sig)
        let internal_key_sat_weight = Some(70);
        // expected weight: 4 (scriptSig len) + 1 (witness len) + 1 (OP_PUSH) + 64 (sig)
        // + 1 (script len)
        // + 34 [script: 1 (OP_PUSHBYTES_32) + 32 (key) + 1 (OP_CHECKSIG)]
        // + 1 (control block len)
        // + 65 [control block: 1 (control byte) + 32 (internal key) + 32 (hash BC)]
        let first_leaf_sat_weight = Some(171);
        // expected weight: 4 (scriptSig len) + 1 (witness len) + 1 (OP_PUSH) + 64 (sig)
        // + 1 (OP_ZERO)
        // + 1 (script len)
        // + 70 [script: 1 (OP_PUSHBYTES_32) + 32 (key) + 1 (OP_CHECKSIG)
        //       + 1 (OP_PUSHBYTES_32) + 32 (key) + 1 (OP_CHECKSIGADD)
        //       + 1 (OP_PUSHNUM1) + 1 (OP_NUMEQUAL)]
        // + 1 (control block len)
        // + 97 [control block: 1 (control byte) + 32 (internal key) + 32 (hash C) + 32 (hash
        //       A)]
        let second_leaf_sat_weight = Some(240);
        // expected weight: 4 (scriptSig len) + 1 (witness len) + 1 (OP_PUSH) + 64 (sig)
        // + 1 (script len)
        // + 36 [script: 1 (OP_PUSHBYTES_32) + 32 (key) + 1 (OP_CHECKSIGVERIFY)
        //       + 1 (OP_PUSHNUM_10) + 1 (OP_CLTV)]
        // + 1 (control block len)
        // + 97 [control block: 1 (control byte) + 32 (internal key) + 32 (hash B) + 32 (hash
        //       A)]
        let third_leaf_sat_weight = Some(205);

        let tests = vec![
            // Don't give assets
            (vec![], vec![], None, None, None),
            // Spend with internal key
            (vec![0], vec![], None, None, internal_key_sat_weight),
            // Spend with first leaf (single pk)
            (vec![1], vec![], None, None, first_leaf_sat_weight),
            // Spend with second leaf (1of2)
            (vec![2], vec![], None, None, second_leaf_sat_weight),
            // Spend with second leaf (1of2)
            (vec![2, 3], vec![], None, None, second_leaf_sat_weight),
            // Spend with third leaf (key + timelock)
            (
                vec![4],
                vec![],
                None,
                Some(absolute::LockTime::from_height(10).unwrap()),
                third_leaf_sat_weight,
            ),
            // Spend with third leaf (key + timelock),
            // but timelock is too low (=impossible)
            (vec![4], vec![], None, Some(absolute::LockTime::from_height(9).unwrap()), None),
            // Spend with third leaf (key + timelock),
            // but timelock is in the wrong unit (=impossible)
            (
                vec![4],
                vec![],
                None,
                Some(absolute::LockTime::from_time(1296000000).unwrap()),
                None,
            ),
            // Spend with third leaf (key + timelock),
            // but don't give the timelock (=impossible)
            (vec![4], vec![], None, None, None),
            // Give all the keys (internal key will be used, as it's cheaper)
            (vec![0, 1, 2, 3, 4], vec![], None, None, internal_key_sat_weight),
            // Give all the leaf keys (uses 1st leaf)
            (vec![1, 2, 3, 4], vec![], None, None, first_leaf_sat_weight),
            // Give 2nd+3rd leaf without timelock (uses 2nd leaf)
            (vec![2, 3, 4], vec![], None, None, second_leaf_sat_weight),
            // Give 2nd+3rd leaf with timelock (uses 3rd leaf)
            (
                vec![2, 3, 4],
                vec![],
                None,
                Some(absolute::LockTime::from_consensus(11)),
                third_leaf_sat_weight,
            ),
        ];

        test_inner(&desc, keys, hashes, tests);
    }

    #[test]
    fn test_hash() {
        let keys = vec![DescriptorPublicKey::from_str(
            "02c2fd50ceae468857bb7eb32ae9cd4083e6c7e42fbbec179d81134b3e3830586c",
        )
        .unwrap()];
        let hashes = vec![hash160::Hash::from_slice(&[0; 20]).unwrap()];
        let desc = format!("wsh(and_v(v:pk({}),hash160({})))", keys[0], hashes[0]);

        let tests = vec![
            // No assets, impossible
            (vec![], vec![], None, None, None),
            // Only key, impossible
            (vec![0], vec![], None, None, None),
            // Only hash, impossible
            (vec![], vec![0], None, None, None),
            // Key + hash
            // expected weight: 4 (scriptSig len) + 1 (witness len) + 73 (sig) + 1 (OP_PUSH) + 32 (preimage)
            (vec![0], vec![0], None, None, Some(111)),
        ];

        test_inner(&desc, keys, hashes, tests);
    }

    #[test]
    fn test_plan_update_psbt_tr() {
        // keys taken from: https://github.com/bitcoin/bips/blob/master/bip-0086.mediawiki#Specifications
        let root_xpub = Xpub::from_str("xpub661MyMwAqRbcFkPHucMnrGNzDwb6teAX1RbKQmqtEF8kK3Z7LZ59qafCjB9eCRLiTVG3uxBxgKvRgbubRhqSKXnGGb1aoaqLrpMBDrVxga8").unwrap();
        let fingerprint = root_xpub.fingerprint();
        let xpub = format!("[{}/86'/0'/0']xpub6BgBgsespWvERF3LHQu6CnqdvfEvtMcQjYrcRzx53QJjSxarj2afYWcLteoGVky7D3UKDP9QyrLprQ3VCECoY49yfdDEHGCtMMj92pReUsQ", fingerprint);
        let desc =
            format!("tr({}/0/0,{{pkh({}/0/1),multi_a(2,{}/1/0,{}/1/1)}})", xpub, xpub, xpub, xpub);

        let desc = Descriptor::from_str(&desc).unwrap();

        let internal_key = DescriptorPublicKey::from_str(&format!("{}/0/0", xpub)).unwrap();
        let first_branch = DescriptorPublicKey::from_str(&format!("{}/0/1", xpub)).unwrap();
        let second_branch = DescriptorPublicKey::from_str(&format!("{}/1/*", xpub)).unwrap(); // Note this is a wildcard key, so it can sign for the whole multi_a

        let mut psbt_input = bitcoin::psbt::Input::default();
        let assets = Assets::new().add(internal_key);
        desc.clone()
            .plan(&assets)
            .unwrap()
            .update_psbt_input(&mut psbt_input);
        assert!(psbt_input.tap_internal_key.is_some(), "Internal key is missing");
        assert!(psbt_input.tap_merkle_root.is_some(), "Merkle root is missing");
        assert_eq!(psbt_input.tap_key_origins.len(), 1, "Unexpected number of tap_key_origins");
        assert_eq!(psbt_input.tap_scripts.len(), 0, "Unexpected number of tap_scripts");

        let mut psbt_input = bitcoin::psbt::Input::default();
        let assets = Assets::new().add(first_branch);
        desc.clone()
            .plan(&assets)
            .unwrap()
            .update_psbt_input(&mut psbt_input);
        assert!(psbt_input.tap_internal_key.is_none(), "Internal key is present");
        assert!(psbt_input.tap_merkle_root.is_some(), "Merkle root is missing");
        assert_eq!(psbt_input.tap_key_origins.len(), 1, "Unexpected number of tap_key_origins");
        assert_eq!(psbt_input.tap_scripts.len(), 1, "Unexpected number of tap_scripts");

        let mut psbt_input = bitcoin::psbt::Input::default();
        let assets = Assets::new().add(second_branch);
        desc.plan(&assets)
            .unwrap()
            .update_psbt_input(&mut psbt_input);
        assert!(psbt_input.tap_internal_key.is_none(), "Internal key is present");
        assert!(psbt_input.tap_merkle_root.is_some(), "Merkle root is missing");
        assert_eq!(psbt_input.tap_key_origins.len(), 2, "Unexpected number of tap_key_origins");
        assert_eq!(psbt_input.tap_scripts.len(), 1, "Unexpected number of tap_scripts");
    }

    #[test]
    fn test_plan_update_psbt_segwit() {
        // keys taken from: https://github.com/bitcoin/bips/blob/master/bip-0086.mediawiki#Specifications
        let root_xpub = Xpub::from_str("xpub661MyMwAqRbcFkPHucMnrGNzDwb6teAX1RbKQmqtEF8kK3Z7LZ59qafCjB9eCRLiTVG3uxBxgKvRgbubRhqSKXnGGb1aoaqLrpMBDrVxga8").unwrap();
        let fingerprint = root_xpub.fingerprint();
        let xpub = format!("[{}/86'/0'/0']xpub6BgBgsespWvERF3LHQu6CnqdvfEvtMcQjYrcRzx53QJjSxarj2afYWcLteoGVky7D3UKDP9QyrLprQ3VCECoY49yfdDEHGCtMMj92pReUsQ", fingerprint);
        let desc = format!("wsh(multi(2,{}/1/0,{}/1/1))", xpub, xpub);

        let desc = Descriptor::from_str(&desc).unwrap();

        let asset_key = DescriptorPublicKey::from_str(&format!("{}/1/*", xpub)).unwrap(); // Note this is a wildcard key, so it can sign for the whole multi

        let mut psbt_input = bitcoin::psbt::Input::default();
        let assets = Assets::new().add(asset_key);
        desc.plan(&assets)
            .unwrap()
            .update_psbt_input(&mut psbt_input);
        assert!(psbt_input.witness_script.is_some(), "Witness script missing");
        assert!(psbt_input.redeem_script.is_none(), "Redeem script present");
        assert_eq!(psbt_input.bip32_derivation.len(), 2, "Unexpected number of bip32_derivation");
    }
}
