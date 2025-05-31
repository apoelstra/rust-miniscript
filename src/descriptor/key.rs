// SPDX-License-Identifier: CC0-1.0

use core::convert::TryInto;
use core::fmt;
use core::str::FromStr;
#[cfg(feature = "std")]
use std::error;

use bitcoin::bip32::{self, XKeyIdentifier};
use bitcoin::hashes::{hash160, ripemd160, sha256, Hash, HashEngine};
use bitcoin::key::{PublicKey, XOnlyPublicKey};
use bitcoin::secp256k1::{Secp256k1, Signing, Verification};
use bitcoin::NetworkKind;

use crate::prelude::*;
#[cfg(feature = "serde")]
use crate::serde::{Deserialize, Deserializer, Serialize, Serializer};
use crate::{hash256, MiniscriptKey, ToPublicKey};

/// The descriptor pubkey, either a single pubkey or an xpub.
#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub enum DescriptorPublicKey {
    /// Single public key.
    Single(SinglePub),
    /// Extended public key (xpub).
    XPub(DescriptorXKey<bip32::Xpub>),
    /// Multiple extended public keys.
    MultiXPub(DescriptorMultiXKey<bip32::Xpub>),
}

/// The descriptor secret key, either a single private key or an xprv.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum DescriptorSecretKey {
    /// Single private key.
    Single(SinglePriv),
    /// Extended private key (xpriv).
    XPrv(DescriptorXKey<bip32::Xpriv>),
    /// Multiple extended private keys.
    MultiXPrv(DescriptorMultiXKey<bip32::Xpriv>),
}

/// A descriptor [`SinglePubKey`] with optional origin information.
#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub struct SinglePub {
    /// Origin information (fingerprint and derivation path).
    pub origin: Option<(bip32::Fingerprint, bip32::DerivationPath)>,
    /// The public key.
    pub key: SinglePubKey,
}

/// A descriptor [`bitcoin::PrivateKey`] with optional origin information.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct SinglePriv {
    /// Origin information (fingerprint and derivation path).
    pub origin: Option<(bip32::Fingerprint, bip32::DerivationPath)>,
    /// The private key.
    pub key: bitcoin::PrivateKey,
}

/// An extended key with origin, derivation path, and wildcard.
#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub struct DescriptorXKey<K: InnerXKey> {
    /// Origin information
    pub origin: Option<(bip32::Fingerprint, bip32::DerivationPath)>,
    /// The extended key
    pub xkey: K,
    /// The derivation path
    pub derivation_path: bip32::DerivationPath,
    /// Whether the descriptor is wildcard
    pub wildcard: Wildcard,
}

/// The derivation paths in a multipath key expression.
#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub struct DerivPaths(Vec<bip32::DerivationPath>);

impl DerivPaths {
    /// Create a non empty derivation paths list.
    pub fn new(paths: Vec<bip32::DerivationPath>) -> Option<Self> {
        if paths.is_empty() {
            None
        } else {
            Some(Self(paths))
        }
    }

    /// Get the list of derivation paths.
    pub fn paths(&self) -> &Vec<bip32::DerivationPath> { &self.0 }

    /// Get the list of derivation paths.
    pub fn into_paths(self) -> Vec<bip32::DerivationPath> { self.0 }
}

/// Instance of one or more extended keys, as specified in BIP 389.
#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub struct DescriptorMultiXKey<K: InnerXKey> {
    /// Origin information
    pub origin: Option<(bip32::Fingerprint, bip32::DerivationPath)>,
    /// The extended key
    pub xkey: K,
    /// The derivation paths. Never empty.
    pub derivation_paths: DerivPaths,
    /// Whether the descriptor is wildcard
    pub wildcard: Wildcard,
}

/// Single public key without any origin or range information.
#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub enum SinglePubKey {
    /// A bitcoin public key (compressed or uncompressed).
    FullKey(bitcoin::PublicKey),
    /// An xonly public key.
    XOnly(XOnlyPublicKey),
}

/// A [`DescriptorPublicKey`] without any wildcards.
#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub struct DefiniteDescriptorKey(DescriptorPublicKey);

/// Network information extracted from extended keys in a descriptor.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum XKeyNetwork {
    /// No extended keys are present in the descriptor.
    NoXKeys,
    /// Extended keys are present but have conflicting network prefixes.
    Mixed,
    /// Extended key(s) are present and all have the same network prefix.
    Single(NetworkKind),
}

impl fmt::Display for DescriptorSecretKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Single(ref sk) => {
                maybe_fmt_master_id(f, &sk.origin)?;
                sk.key.fmt(f)?;
                Ok(())
            }
            Self::XPrv(ref xprv) => {
                maybe_fmt_master_id(f, &xprv.origin)?;
                xprv.xkey.fmt(f)?;
                fmt_derivation_path(f, &xprv.derivation_path)?;
                match xprv.wildcard {
                    Wildcard::None => {}
                    Wildcard::Unhardened => write!(f, "/*")?,
                    Wildcard::Hardened => write!(f, "/*h")?,
                }
                Ok(())
            }
            Self::MultiXPrv(ref xprv) => {
                maybe_fmt_master_id(f, &xprv.origin)?;
                xprv.xkey.fmt(f)?;
                fmt_derivation_paths(f, xprv.derivation_paths.paths())?;
                match xprv.wildcard {
                    Wildcard::None => {}
                    Wildcard::Unhardened => write!(f, "/*")?,
                    Wildcard::Hardened => write!(f, "/*h")?,
                }
                Ok(())
            }
        }
    }
}

/// Trait for "extended key" types like `xpub` and `xprv`. Used internally to generalize parsing and
/// handling of `bip32::Xpub` and `bip32::Xpriv`.
pub trait InnerXKey: fmt::Display + FromStr {
    /// Returns the fingerprint of the key
    fn xkey_fingerprint<C: Signing>(&self, secp: &Secp256k1<C>) -> bip32::Fingerprint;

    /// Returns whether hardened steps can be derived on the key
    ///
    /// `true` for `bip32::Xpriv` and `false` for `bip32::Xpub`.
    fn can_derive_hardened() -> bool;
}

impl InnerXKey for bip32::Xpub {
    fn xkey_fingerprint<C: Signing>(&self, _secp: &Secp256k1<C>) -> bip32::Fingerprint {
        self.fingerprint()
    }

    fn can_derive_hardened() -> bool { false }
}

impl InnerXKey for bip32::Xpriv {
    fn xkey_fingerprint<C: Signing>(&self, secp: &Secp256k1<C>) -> bip32::Fingerprint {
        self.fingerprint(secp)
    }

    fn can_derive_hardened() -> bool { true }
}

/// Whether a descriptor has a wildcard in it
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Wildcard {
    /// No wildcard
    None,
    /// Unhardened wildcard, e.g. *
    Unhardened,
    /// Hardened wildcard, e.g. *h
    Hardened,
}

impl SinglePriv {
    /// Returns the public key of this key.
    fn to_public<C: Signing>(&self, secp: &Secp256k1<C>) -> SinglePub {
        let pub_key = self.key.public_key(secp);

        SinglePub { origin: self.origin.clone(), key: SinglePubKey::FullKey(pub_key) }
    }
}

impl DescriptorXKey<bip32::Xpriv> {
    /// Returns the public version of this key, applying all the hardened derivation steps on the
    /// private key before turning it into a public key.
    ///
    /// If the key already has an origin, the derivation steps applied will be appended to the path
    /// already present, otherwise this key will be treated as a master key and an origin will be
    /// added with this key's fingerprint and the derivation steps applied.
    fn to_public<C: Signing>(
        &self,
        secp: &Secp256k1<C>,
    ) -> Result<DescriptorXKey<bip32::Xpub>, DescriptorKeyParseError> {
        let unhardened = self
            .derivation_path
            .into_iter()
            .rev()
            .take_while(|c| c.is_normal())
            .count();
        let last_hardened_idx = self.derivation_path.len() - unhardened;

        let hardened_path = &self.derivation_path[..last_hardened_idx];
        let unhardened_path = &self.derivation_path[last_hardened_idx..];

        let xprv = self
            .xkey
            .derive_priv(secp, &hardened_path)
            .map_err(DescriptorKeyParseError::DeriveHardenedKey)?;

        let xpub = bip32::Xpub::from_priv(secp, &xprv);

        let origin = match &self.origin {
            Some((fingerprint, path)) => {
                Some((*fingerprint, path.into_iter().chain(hardened_path).copied().collect()))
            }
            None if !hardened_path.is_empty() => {
                Some((self.xkey.fingerprint(secp), hardened_path.into()))
            }
            None => None,
        };

        Ok(DescriptorXKey {
            origin,
            xkey: xpub,
            derivation_path: unhardened_path.into(),
            wildcard: self.wildcard,
        })
    }
}

impl DescriptorMultiXKey<bip32::Xpriv> {
    /// Returns the public version of this multi-key, applying all the hardened derivation steps that
    /// are shared among all derivation paths before turning it into a public key.
    ///
    /// Errors if there are hardened derivation steps that are not shared among all paths.
    fn to_public<C: Signing>(
        &self,
        secp: &Secp256k1<C>,
    ) -> Result<DescriptorMultiXKey<bip32::Xpub>, DescriptorKeyParseError> {
        let deriv_paths = self.derivation_paths.paths();

        let shared_prefix: Vec<_> = deriv_paths[0]
            .into_iter()
            .enumerate()
            .take_while(|(index, child_num)| {
                deriv_paths[1..].iter().all(|other_path| {
                    other_path.len() > *index && other_path[*index] == **child_num
                })
            })
            .map(|(_, child_num)| *child_num)
            .collect();

        let suffixes: Vec<Vec<_>> = deriv_paths
            .iter()
            .map(|path| {
                path.into_iter()
                    .skip(shared_prefix.len())
                    .map(|child_num| {
                        if child_num.is_normal() {
                            Ok(*child_num)
                        } else {
                            Err(DescriptorKeyParseError::MalformedKeyData(
                                MalformedKeyDataKind::InvalidMultiXKeyDerivation,
                            ))
                        }
                    })
                    .collect()
            })
            .collect::<Result<_, _>>()?;

        let unhardened = shared_prefix
            .iter()
            .rev()
            .take_while(|c| c.is_normal())
            .count();
        let last_hardened_idx = shared_prefix.len() - unhardened;
        let hardened_path = &shared_prefix[..last_hardened_idx];
        let unhardened_path = &shared_prefix[last_hardened_idx..];

        let xprv = self
            .xkey
            .derive_priv(secp, &hardened_path)
            .map_err(DescriptorKeyParseError::DeriveHardenedKey)?;
        let xpub = bip32::Xpub::from_priv(secp, &xprv);

        let origin = match &self.origin {
            Some((fingerprint, path)) => {
                Some((*fingerprint, path.into_iter().chain(hardened_path).copied().collect()))
            }
            None if !hardened_path.is_empty() => {
                Some((self.xkey.fingerprint(secp), hardened_path.into()))
            }
            None => None,
        };
        let new_deriv_paths = suffixes
            .into_iter()
            .map(|suffix| {
                let path = unhardened_path.iter().copied().chain(suffix);
                path.collect::<Vec<_>>().into()
            })
            .collect();

        Ok(DescriptorMultiXKey {
            origin,
            xkey: xpub,
            derivation_paths: DerivPaths::new(new_deriv_paths).expect("not empty"),
            wildcard: self.wildcard,
        })
    }
}

/// Kinds of malformed key data
#[derive(Debug, PartialEq, Eq, Clone)]
#[non_exhaustive]
#[allow(missing_docs)]
pub enum NonDefiniteKeyError {
    Wildcard,
    Multipath,
    HardenedStep,
}

impl fmt::Display for NonDefiniteKeyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Wildcard => f.write_str("key with a wildcard cannot be a DerivedDescriptorKey"),
            Self::Multipath => f.write_str("multipath key cannot be a DerivedDescriptorKey"),
            Self::HardenedStep => {
                f.write_str("key with hardened derivation steps cannot be a DerivedDescriptorKey")
            }
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for NonDefiniteKeyError {}

/// Kinds of malformed key data
#[derive(Debug, PartialEq, Eq, Clone)]
#[non_exhaustive]
#[allow(missing_docs)]
pub enum MalformedKeyDataKind {
    EmptyKey,
    EncounteredUnprintableCharacter,
    InvalidFullPublicKeyPrefix,
    InvalidMasterFingerprintLength,
    InvalidMultiIndexStep,
    InvalidMultiXKeyDerivation,
    InvalidPublicKeyLength,
    InvalidWildcardInDerivationPath,
    KeyTooShort,
    MultipleFingerprintsInPublicKey,
    MultipleDerivationPathIndexSteps,
    NoKeyAfterOrigin,
    NoMasterFingerprintFound,
    UnclosedSquareBracket,
}

impl fmt::Display for MalformedKeyDataKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let err = match self {
            Self::EmptyKey => "empty key",
            Self::EncounteredUnprintableCharacter => "encountered an unprintable character",
            Self::InvalidFullPublicKeyPrefix => "only full public keys with prefixes '02', '03' or '04' are allowed",
            Self::InvalidMasterFingerprintLength => "master fingerprint should be 8 characters long",
            Self::InvalidMultiIndexStep => "invalid multi index step in multipath descriptor",
            Self::InvalidMultiXKeyDerivation => "can't make a multi-xpriv with hardened derivation steps that are not shared among all paths into a public key",
            Self::InvalidPublicKeyLength => "public keys must be 64, 66 or 130 characters in size",
            Self::InvalidWildcardInDerivationPath => "'*' may only appear as last element in a derivation path",
            Self::KeyTooShort => "key too short",
            Self::MultipleFingerprintsInPublicKey => "multiple ']' in Descriptor Public Key",
            Self::MultipleDerivationPathIndexSteps => "'<' may only appear once in a derivation path",
            Self::NoKeyAfterOrigin => "no key after origin",
            Self::NoMasterFingerprintFound => "no master fingerprint found after '['",
            Self::UnclosedSquareBracket => "unclosed '['",
        };

        f.write_str(err)
    }
}

/// Descriptor Key parsing errors
#[derive(Debug, PartialEq, Eq, Clone)]
#[non_exhaustive]
pub enum DescriptorKeyParseError {
    /// Error while parsing a BIP32 extended private key
    Bip32Xpriv(bip32::Error),
    /// Error while parsing a BIP32 extended public key
    Bip32Xpub(bip32::Error),
    /// Error while parsing a derivation index
    DerivationIndexError {
        /// The invalid index
        index: String,
        /// The underlying parse error
        err: bitcoin::bip32::Error,
    },
    /// Error deriving the hardened private key.
    DeriveHardenedKey(bip32::Error),
    /// Error indicating the key data was malformed
    MalformedKeyData(MalformedKeyDataKind),
    /// Error while parsing the master derivation path.
    MasterDerivationPath(bip32::Error),
    /// Error indicating a malformed master fingerprint (invalid hex).
    MasterFingerprint {
        /// The invalid fingerprint
        fingerprint: String,
        /// The underlying parse error
        err: bitcoin::hex::HexToArrayError,
    },
    /// Attempt to construct a [`DefiniteDescriptorKey`] from an ambiguous key.
    NonDefiniteKey(NonDefiniteKeyError),
    /// Error while parsing a simple public key.
    FullPublicKey(bitcoin::key::ParsePublicKeyError),
    /// Error while parsing a WIF private key.
    WifPrivateKey(bitcoin::key::FromWifError),
    /// Error while parsing an X-only public key (Secp256k1 error).
    XonlyPublicKey(bitcoin::secp256k1::Error),
}

impl fmt::Display for DescriptorKeyParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Bip32Xpriv(err) => err.fmt(f),
            Self::Bip32Xpub(err) => err.fmt(f),
            Self::DerivationIndexError { index, err } => {
                write!(f, "at derivation index '{index}': {err}")
            }
            Self::DeriveHardenedKey(err) => err.fmt(f),
            Self::MalformedKeyData(err) => err.fmt(f),
            Self::MasterDerivationPath(err) => err.fmt(f),
            Self::MasterFingerprint { fingerprint, err } => {
                write!(f, "on master fingerprint '{fingerprint}': {err}")
            }
            Self::NonDefiniteKey(err) => err.fmt(f),
            Self::FullPublicKey(err) => err.fmt(f),
            Self::WifPrivateKey(err) => err.fmt(f),
            Self::XonlyPublicKey(err) => err.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl error::Error for DescriptorKeyParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Bip32Xpriv(err)
            | Self::Bip32Xpub(err)
            | Self::DerivationIndexError { err, .. }
            | Self::DeriveHardenedKey(err)
            | Self::MasterDerivationPath(err) => Some(err),
            Self::MasterFingerprint { err, .. } => Some(err),
            Self::NonDefiniteKey(err) => Some(err),
            Self::FullPublicKey(err) => Some(err),
            Self::WifPrivateKey(err) => Some(err),
            Self::XonlyPublicKey(err) => Some(err),
            Self::MalformedKeyData(_) => None,
        }
    }
}

impl fmt::Display for DescriptorPublicKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::Single(ref pk) => {
                maybe_fmt_master_id(f, &pk.origin)?;
                match pk.key {
                    SinglePubKey::FullKey(full_key) => full_key.fmt(f),
                    SinglePubKey::XOnly(x_only_key) => x_only_key.fmt(f),
                }?;
                Ok(())
            }
            Self::XPub(ref xpub) => {
                maybe_fmt_master_id(f, &xpub.origin)?;
                xpub.xkey.fmt(f)?;
                fmt_derivation_path(f, &xpub.derivation_path)?;
                match xpub.wildcard {
                    Wildcard::None => {}
                    Wildcard::Unhardened => write!(f, "/*")?,
                    Wildcard::Hardened => write!(f, "/*h")?,
                }
                Ok(())
            }
            Self::MultiXPub(ref xpub) => {
                maybe_fmt_master_id(f, &xpub.origin)?;
                xpub.xkey.fmt(f)?;
                fmt_derivation_paths(f, xpub.derivation_paths.paths())?;
                match xpub.wildcard {
                    Wildcard::None => {}
                    Wildcard::Unhardened => write!(f, "/*")?,
                    Wildcard::Hardened => write!(f, "/*h")?,
                }
                Ok(())
            }
        }
    }
}

impl DescriptorSecretKey {
    /// Returns the public version of this key.
    ///
    /// If the key is an "XPrv", the hardened derivation steps will be applied
    /// before converting it to a public key.
    ///
    /// It will return an error if the key is a "multi-xpriv" that includes
    /// hardened derivation steps not shared for all paths.
    pub fn to_public<C: Signing>(
        &self,
        secp: &Secp256k1<C>,
    ) -> Result<DescriptorPublicKey, DescriptorKeyParseError> {
        let pk = match self {
            Self::Single(prv) => DescriptorPublicKey::Single(prv.to_public(secp)),
            Self::XPrv(xprv) => DescriptorPublicKey::XPub(xprv.to_public(secp)?),
            Self::MultiXPrv(xprv) => DescriptorPublicKey::MultiXPub(xprv.to_public(secp)?),
        };

        Ok(pk)
    }

    /// Whether or not this key has multiple derivation paths.
    pub fn is_multipath(&self) -> bool {
        match *self {
            Self::Single(..) | Self::XPrv(..) => false,
            Self::MultiXPrv(_) => true,
        }
    }

    /// Get as many keys as derivation paths in this key.
    ///
    /// For raw keys and single-path extended keys it will return the key itself.
    /// For multipath extended keys it will return a single-path extended key per derivation
    /// path.
    pub fn into_single_keys(self) -> Vec<Self> {
        match self {
            Self::Single(..) | Self::XPrv(..) => vec![self],
            Self::MultiXPrv(xpub) => {
                let DescriptorMultiXKey { origin, xkey, derivation_paths, wildcard } = xpub;
                derivation_paths
                    .into_paths()
                    .into_iter()
                    .map(|derivation_path| {
                        Self::XPrv(DescriptorXKey {
                            origin: origin.clone(),
                            xkey,
                            derivation_path,
                            wildcard,
                        })
                    })
                    .collect()
            }
        }
    }
}

/// Writes the fingerprint of the origin, if there is one.
fn maybe_fmt_master_id(
    f: &mut fmt::Formatter,
    origin: &Option<(bip32::Fingerprint, bip32::DerivationPath)>,
) -> fmt::Result {
    if let Some((ref master_id, ref master_deriv)) = *origin {
        fmt::Formatter::write_str(f, "[")?;
        for byte in master_id.as_bytes().iter() {
            write!(f, "{:02x}", byte)?;
        }
        fmt_derivation_path(f, master_deriv)?;
        fmt::Formatter::write_str(f, "]")?;
    }

    Ok(())
}

/// Writes a derivation path to the formatter, no leading 'm'
fn fmt_derivation_path(f: &mut fmt::Formatter, path: &bip32::DerivationPath) -> fmt::Result {
    for child in path {
        write!(f, "/{}", child)?;
    }
    Ok(())
}

/// Writes multiple derivation paths to the formatter, no leading 'm'.
/// NOTE: we assume paths only differ at a single index, as prescribed by BIP389.
/// Will panic if the list of paths is empty.
fn fmt_derivation_paths(f: &mut fmt::Formatter, paths: &[bip32::DerivationPath]) -> fmt::Result {
    for (i, child) in paths[0].into_iter().enumerate() {
        if paths.len() > 1 && child != &paths[1][i] {
            write!(f, "/<")?;
            for (j, p) in paths.iter().enumerate() {
                write!(f, "{}", p[i])?;
                if j != paths.len() - 1 {
                    write!(f, ";")?;
                }
            }
            write!(f, ">")?;
        } else {
            write!(f, "/{}", child)?;
        }
    }
    Ok(())
}

impl FromStr for DescriptorPublicKey {
    type Err = DescriptorKeyParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // A "raw" public key without any origin is the least we accept.
        if s.len() < 64 {
            return Err(DescriptorKeyParseError::MalformedKeyData(
                MalformedKeyDataKind::KeyTooShort,
            ));
        }

        let (key_part, origin) = parse_key_origin(s)?;

        if key_part.contains("pub") {
            let (xpub, derivation_paths, wildcard) = parse_xkey_deriv(parse_bip32_xpub, key_part)?;
            if derivation_paths.len() > 1 {
                Ok(Self::MultiXPub(DescriptorMultiXKey {
                    origin,
                    xkey: xpub,
                    derivation_paths: DerivPaths::new(derivation_paths).expect("Not empty"),
                    wildcard,
                }))
            } else {
                Ok(Self::XPub(DescriptorXKey {
                    origin,
                    xkey: xpub,
                    derivation_path: derivation_paths.into_iter().next().unwrap_or_default(),
                    wildcard,
                }))
            }
        } else {
            let key = match key_part.len() {
                64 => {
                    let x_only_key = XOnlyPublicKey::from_str(key_part)
                        .map_err(DescriptorKeyParseError::XonlyPublicKey)?;
                    SinglePubKey::XOnly(x_only_key)
                }
                66 | 130 => {
                    if !(&key_part[0..2] == "02"
                        || &key_part[0..2] == "03"
                        || &key_part[0..2] == "04")
                    {
                        return Err(DescriptorKeyParseError::MalformedKeyData(
                            MalformedKeyDataKind::InvalidFullPublicKeyPrefix,
                        ));
                    }
                    let key = bitcoin::PublicKey::from_str(key_part)
                        .map_err(DescriptorKeyParseError::FullPublicKey)?;
                    SinglePubKey::FullKey(key)
                }
                _ => {
                    return Err(DescriptorKeyParseError::MalformedKeyData(
                        MalformedKeyDataKind::InvalidPublicKeyLength,
                    ))
                }
            };
            Ok(Self::Single(SinglePub { key, origin }))
        }
    }
}

impl From<XOnlyPublicKey> for DescriptorPublicKey {
    fn from(key: XOnlyPublicKey) -> Self {
        DescriptorPublicKey::Single(SinglePub { origin: None, key: SinglePubKey::XOnly(key) })
    }
}

impl From<PublicKey> for DescriptorPublicKey {
    fn from(key: PublicKey) -> Self {
        DescriptorPublicKey::Single(SinglePub { origin: None, key: SinglePubKey::FullKey(key) })
    }
}

impl DescriptorPublicKey {
    /// The fingerprint of the master key associated with this key, `0x00000000` if none.
    pub fn master_fingerprint(&self) -> bip32::Fingerprint {
        match *self {
            Self::XPub(ref xpub) => {
                if let Some((fingerprint, _)) = xpub.origin {
                    fingerprint
                } else {
                    xpub.xkey.fingerprint()
                }
            }
            Self::MultiXPub(ref xpub) => {
                if let Some((fingerprint, _)) = xpub.origin {
                    fingerprint
                } else {
                    xpub.xkey.fingerprint()
                }
            }
            Self::Single(ref single) => {
                if let Some((fingerprint, _)) = single.origin {
                    fingerprint
                } else {
                    let mut engine = XKeyIdentifier::engine();
                    match single.key {
                        SinglePubKey::FullKey(pk) => {
                            pk.write_into(&mut engine).expect("engines don't error")
                        }
                        SinglePubKey::XOnly(x_only_pk) => engine.input(&x_only_pk.serialize()),
                    };
                    bip32::Fingerprint::from(
                        &XKeyIdentifier::from_engine(engine)[..4]
                            .try_into()
                            .expect("4 byte slice"),
                    )
                }
            }
        }
    }

    /// Full path, from the master key
    ///
    /// For wildcard keys this will return the path up to the wildcard, so you
    /// can get full paths by appending one additional derivation step, according
    /// to the wildcard type (hardened or normal).
    ///
    /// For multipath extended keys, this returns `None`.
    pub fn full_derivation_path(&self) -> Option<bip32::DerivationPath> {
        match *self {
            Self::XPub(ref xpub) => {
                let origin_path = if let Some((_, ref path)) = xpub.origin {
                    path.clone()
                } else {
                    bip32::DerivationPath::from(vec![])
                };
                Some(origin_path.extend(&xpub.derivation_path))
            }
            Self::Single(ref single) => Some(if let Some((_, ref path)) = single.origin {
                path.clone()
            } else {
                bip32::DerivationPath::from(vec![])
            }),
            Self::MultiXPub(_) => None,
        }
    }

    /// Returns a vector containing the full derivation paths from the master key.
    /// The vector will contain just one element for single keys, and multiple elements
    /// for multipath extended keys.
    ///
    /// For wildcard keys this will return the path up to the wildcard, so you
    /// can get full paths by appending one additional derivation step, according
    /// to the wildcard type (hardened or normal).
    pub fn full_derivation_paths(&self) -> Vec<bip32::DerivationPath> {
        match self {
            Self::MultiXPub(xpub) => {
                let origin_path = if let Some((_, ref path)) = xpub.origin {
                    path.clone()
                } else {
                    bip32::DerivationPath::from(vec![])
                };
                xpub.derivation_paths
                    .paths()
                    .iter()
                    .map(|p| origin_path.extend(p))
                    .collect()
            }
            _ => vec![self
                .full_derivation_path()
                .expect("Must be Some for non-multipath keys")],
        }
    }

    /// Whether or not the key has a wildcard
    pub fn has_wildcard(&self) -> bool {
        match *self {
            Self::Single(..) => false,
            Self::XPub(ref xpub) => xpub.wildcard != Wildcard::None,
            Self::MultiXPub(ref xpub) => xpub.wildcard != Wildcard::None,
        }
    }

    /// Whether or not the key has a wildcard
    pub fn has_hardened_step(&self) -> bool {
        let paths = match self {
            DescriptorPublicKey::Single(..) => &[],
            DescriptorPublicKey::XPub(xpub) => core::slice::from_ref(&xpub.derivation_path),
            DescriptorPublicKey::MultiXPub(xpub) => &xpub.derivation_paths.paths()[..],
        };
        for p in paths {
            for step in p.into_iter() {
                if step.is_hardened() {
                    return true;
                }
            }
        }
        false
    }

    /// Replaces any wildcard (i.e. `/*`) in the key with a particular derivation index, turning it into a
    /// *definite* key (i.e. one where all the derivation paths are set).
    ///
    /// # Returns
    ///
    /// - If this key is not an xpub, returns `self`.
    /// - If this key is an xpub but does not have a wildcard, returns `self`.
    /// - Otherwise, returns the xpub at derivation `index` (removing the wildcard).
    ///
    /// # Errors
    ///
    /// - If `index` is hardened.
    /// - If the key contains multi-path derivations
    pub fn at_derivation_index(
        self,
        index: u32,
    ) -> Result<DefiniteDescriptorKey, NonDefiniteKeyError> {
        let definite = match self {
            Self::Single(_) => self,
            Self::XPub(xpub) => {
                let derivation_path = match xpub.wildcard {
                    Wildcard::None => xpub.derivation_path,
                    Wildcard::Unhardened => xpub.derivation_path.into_child(
                        bip32::ChildNumber::from_normal_idx(index)
                            .ok()
                            .ok_or(NonDefiniteKeyError::HardenedStep)?,
                    ),
                    Wildcard::Hardened => xpub.derivation_path.into_child(
                        bip32::ChildNumber::from_hardened_idx(index)
                            .ok()
                            .ok_or(NonDefiniteKeyError::HardenedStep)?,
                    ),
                };
                Self::XPub(DescriptorXKey {
                    origin: xpub.origin,
                    xkey: xpub.xkey,
                    derivation_path,
                    wildcard: Wildcard::None,
                })
            }
            Self::MultiXPub(_) => return Err(NonDefiniteKeyError::Multipath),
        };

        Ok(DefiniteDescriptorKey::new(definite)
            .expect("The key should not contain any wildcards at this point"))
    }

    /// Whether or not this key has multiple derivation paths.
    pub fn is_multipath(&self) -> bool {
        match *self {
            Self::Single(..) | Self::XPub(..) => false,
            Self::MultiXPub(_) => true,
        }
    }

    /// Get as many keys as derivation paths in this key.
    ///
    /// For raw public key and single-path extended keys it will return the key itself.
    /// For multipath extended keys it will return a single-path extended key per derivation
    /// path.
    pub fn into_single_keys(self) -> Vec<Self> {
        match self {
            Self::Single(..) | Self::XPub(..) => vec![self],
            Self::MultiXPub(xpub) => {
                let DescriptorMultiXKey { origin, xkey, derivation_paths, wildcard } = xpub;
                derivation_paths
                    .into_paths()
                    .into_iter()
                    .map(|derivation_path| {
                        Self::XPub(DescriptorXKey {
                            origin: origin.clone(),
                            xkey,
                            derivation_path,
                            wildcard,
                        })
                    })
                    .collect()
            }
        }
    }

    /// Get the network of this key, if it's an extended key.
    ///
    /// Returns `None` for single keys (non-extended keys), `Some(NetworkKind)` for extended keys.
    pub fn xkey_network(&self) -> Option<NetworkKind> {
        match self {
            DescriptorPublicKey::Single(_) => None,
            DescriptorPublicKey::XPub(xpub) => Some(xpub.xkey.network),
            DescriptorPublicKey::MultiXPub(multi_xpub) => Some(multi_xpub.xkey.network),
        }
    }
}

impl FromStr for DescriptorSecretKey {
    type Err = DescriptorKeyParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (key_part, origin) = parse_key_origin(s)?;

        if key_part.len() <= 52 {
            let sk = bitcoin::PrivateKey::from_str(key_part)
                .map_err(DescriptorKeyParseError::WifPrivateKey)?;
            Ok(Self::Single(SinglePriv { key: sk, origin }))
        } else {
            let (xpriv, derivation_paths, wildcard) =
                parse_xkey_deriv(parse_bip32_xpriv, key_part)?;
            if derivation_paths.len() > 1 {
                Ok(Self::MultiXPrv(DescriptorMultiXKey {
                    origin,
                    xkey: xpriv,
                    derivation_paths: DerivPaths::new(derivation_paths).expect("Not empty"),
                    wildcard,
                }))
            } else {
                Ok(Self::XPrv(DescriptorXKey {
                    origin,
                    xkey: xpriv,
                    derivation_path: derivation_paths.into_iter().next().unwrap_or_default(),
                    wildcard,
                }))
            }
        }
    }
}

// Parse the origin information part of a descriptor key.
fn parse_key_origin(s: &str) -> Result<(&str, Option<bip32::KeySource>), DescriptorKeyParseError> {
    for ch in s.as_bytes() {
        if *ch < 20 || *ch > 127 {
            return Err(DescriptorKeyParseError::MalformedKeyData(
                MalformedKeyDataKind::EncounteredUnprintableCharacter,
            ));
        }
    }

    if s.is_empty() {
        return Err(DescriptorKeyParseError::MalformedKeyData(MalformedKeyDataKind::EmptyKey));
    }
    let mut parts = s[1..].split(']');

    if let Some('[') = s.chars().next() {
        let mut raw_origin = parts
            .next()
            .ok_or(DescriptorKeyParseError::MalformedKeyData(
                MalformedKeyDataKind::UnclosedSquareBracket,
            ))?
            .split('/');

        let origin_id_hex = raw_origin
            .next()
            .ok_or(DescriptorKeyParseError::MalformedKeyData(
                MalformedKeyDataKind::NoMasterFingerprintFound,
            ))?;

        if origin_id_hex.len() != 8 {
            return Err(DescriptorKeyParseError::MalformedKeyData(
                MalformedKeyDataKind::InvalidMasterFingerprintLength,
            ));
        }
        let parent_fingerprint = bip32::Fingerprint::from_hex(origin_id_hex).map_err(|err| {
            DescriptorKeyParseError::MasterFingerprint {
                fingerprint: origin_id_hex.to_owned(),
                err,
            }
        })?;
        let origin_path = raw_origin
            .map(bip32::ChildNumber::from_str)
            .collect::<Result<bip32::DerivationPath, bip32::Error>>()
            .map_err(DescriptorKeyParseError::MasterDerivationPath)?;

        let key = parts
            .next()
            .ok_or(DescriptorKeyParseError::MalformedKeyData(
                MalformedKeyDataKind::NoKeyAfterOrigin,
            ))?;

        if parts.next().is_some() {
            Err(DescriptorKeyParseError::MalformedKeyData(
                MalformedKeyDataKind::MultipleFingerprintsInPublicKey,
            ))
        } else {
            Ok((key, Some((parent_fingerprint, origin_path))))
        }
    } else {
        Ok((s, None))
    }
}

fn parse_bip32_xpub(xkey_str: &str) -> Result<bip32::Xpub, DescriptorKeyParseError> {
    bip32::Xpub::from_str(xkey_str).map_err(DescriptorKeyParseError::Bip32Xpub)
}

fn parse_bip32_xpriv(xkey_str: &str) -> Result<bip32::Xpriv, DescriptorKeyParseError> {
    bip32::Xpriv::from_str(xkey_str).map_err(DescriptorKeyParseError::Bip32Xpriv)
}

fn parse_xkey_deriv<Key>(
    parse_xkey_fn: impl Fn(&str) -> Result<Key, DescriptorKeyParseError>,
    key_deriv: &str,
) -> Result<(Key, Vec<bip32::DerivationPath>, Wildcard), DescriptorKeyParseError> {
    let mut key_deriv = key_deriv.split('/');
    let xkey_str = key_deriv
        .next()
        .ok_or(DescriptorKeyParseError::MalformedKeyData(
            MalformedKeyDataKind::NoKeyAfterOrigin,
        ))?;

    let xkey = parse_xkey_fn(xkey_str)?;

    let mut wildcard = Wildcard::None;
    let mut multipath = false;
    let derivation_paths = key_deriv
        .filter_map(|p| {
            if wildcard == Wildcard::None && p == "*" {
                wildcard = Wildcard::Unhardened;
                None
            } else if wildcard == Wildcard::None && (p == "*'" || p == "*h") {
                wildcard = Wildcard::Hardened;
                None
            } else if wildcard != Wildcard::None {
                Some(Err(DescriptorKeyParseError::MalformedKeyData(
                    MalformedKeyDataKind::InvalidWildcardInDerivationPath,
                )))
            } else {
                // BIP389 defines a new step in the derivation path. This step contains two or more
                // derivation indexes in the form '<1;2;3';4h;5H;6>'.
                if p.starts_with('<') && p.ends_with('>') {
                    // There may only be one occurrence of this step.
                    if multipath {
                        return Some(Err(DescriptorKeyParseError::MalformedKeyData(
                            MalformedKeyDataKind::MultipleDerivationPathIndexSteps,
                        )));
                    }
                    multipath = true;

                    // The step must contain at least two derivation indexes.
                    // So it's at least '<' + a number + ';' + a number + '>'.
                    if p.len() < 5 || !p.contains(';') {
                        return Some(Err(DescriptorKeyParseError::MalformedKeyData(
                            MalformedKeyDataKind::InvalidMultiIndexStep,
                        )));
                    }

                    // Collect all derivation indexes at this step.
                    let indexes = p[1..p.len() - 1].split(';');
                    Some(
                        indexes
                            .into_iter()
                            .map(|s| {
                                bip32::ChildNumber::from_str(s).map_err(|err| {
                                    DescriptorKeyParseError::DerivationIndexError {
                                        index: s.to_owned(),
                                        err,
                                    }
                                })
                            })
                            .collect::<Result<Vec<bip32::ChildNumber>, _>>(),
                    )
                } else {
                    // Not a BIP389 step, just a regular derivation index.
                    Some(
                        bip32::ChildNumber::from_str(p)
                            .map(|i| vec![i])
                            .map_err(|err| DescriptorKeyParseError::DerivationIndexError {
                                index: p.to_owned(),
                                err,
                            }),
                    )
                }
            }
        })
        // Now we've got all derivation indexes in a list of vectors of indexes. If the derivation
        // path was empty then this list is empty. If the derivation path didn't contain any BIP389
        // step all the vectors of indexes contain a single element. If it did though, one of the
        // vectors contains more than one element.
        // Now transform this list of vectors of steps into distinct derivation paths.
        .try_fold(Vec::new(), |mut paths, index_list| {
            let mut index_list = index_list?.into_iter();
            let first_index = index_list
                .next()
                .expect("There is always at least one element");

            if paths.is_empty() {
                paths.push(vec![first_index]);
            } else {
                for path in paths.iter_mut() {
                    path.push(first_index);
                }
            }

            // If the step is a BIP389 one, create as many paths as there is indexes.
            for (i, index) in index_list.enumerate() {
                paths.push(paths[0].clone());
                *paths[i + 1].last_mut().expect("Never empty") = index;
            }

            Ok(paths)
        })?
        .into_iter()
        .map(|index_list| index_list.into_iter().collect::<bip32::DerivationPath>())
        .collect::<Vec<bip32::DerivationPath>>();

    Ok((xkey, derivation_paths, wildcard))
}

impl<K: InnerXKey> DescriptorXKey<K> {
    /// Compares this key with a `keysource` and returns the matching derivation path, if any.
    ///
    /// For keys that have an origin, the `keysource`'s fingerprint will be compared
    /// with the origin's fingerprint, and the `keysource`'s path will be compared with the concatenation of the
    /// origin's and key's paths.
    ///
    /// If the key `wildcard`, the last item of the `keysource`'s path will be ignored,
    ///
    /// ## Examples
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # fn body() -> Result<(), ()> {
    /// use miniscript::bitcoin::bip32;
    /// use miniscript::descriptor::DescriptorPublicKey;
    ///
    /// let ctx = miniscript::bitcoin::secp256k1::Secp256k1::signing_only();
    ///
    /// let key = DescriptorPublicKey::from_str("[d34db33f/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*").or(Err(()))?;
    /// let xpub = match key {
    ///     DescriptorPublicKey::XPub(xpub) => xpub,
    ///     _ => panic!("Parsing Error"),
    /// };
    ///
    /// assert_eq!(
    ///     xpub.matches(&(
    ///         bip32::Fingerprint::from_str("d34db33f").or(Err(()))?,
    ///         bip32::DerivationPath::from_str("m/44'/0'/0'/1/42").or(Err(()))?
    ///     ), &ctx),
    ///     Some(bip32::DerivationPath::from_str("m/44'/0'/0'/1").or(Err(()))?)
    /// );
    /// assert_eq!(
    ///     xpub.matches(&(
    ///         bip32::Fingerprint::from_str("ffffffff").or(Err(()))?,
    ///         bip32::DerivationPath::from_str("m/44'/0'/0'/1/42").or(Err(()))?
    ///     ), &ctx),
    ///     None
    /// );
    /// assert_eq!(
    ///     xpub.matches(&(
    ///         bip32::Fingerprint::from_str("d34db33f").or(Err(()))?,
    ///         bip32::DerivationPath::from_str("m/44'/0'/0'/100/0").or(Err(()))?
    ///     ), &ctx),
    ///     None
    /// );
    /// # Ok(())
    /// # }
    /// # body().unwrap()
    /// ```
    pub fn matches<C: Signing>(
        &self,
        keysource: &bip32::KeySource,
        secp: &Secp256k1<C>,
    ) -> Option<bip32::DerivationPath> {
        let (fingerprint, path) = keysource;

        let (compare_fingerprint, compare_path) = match self.origin {
            Some((fingerprint, ref path)) => {
                (fingerprint, path.into_iter().chain(&self.derivation_path).collect())
            }
            None => (
                self.xkey.xkey_fingerprint(secp),
                self.derivation_path.into_iter().collect::<Vec<_>>(),
            ),
        };

        let path_excluding_wildcard = if self.wildcard != Wildcard::None && !path.is_empty() {
            path.into_iter()
                .take(path.as_ref().len() - 1)
                .cloned()
                .collect()
        } else {
            path.clone()
        };

        if &compare_fingerprint == fingerprint
            && compare_path.into_iter().eq(&path_excluding_wildcard)
        {
            Some(path_excluding_wildcard)
        } else {
            None
        }
    }
}

impl MiniscriptKey for DescriptorPublicKey {
    type Sha256 = sha256::Hash;
    type Hash256 = hash256::Hash;
    type Ripemd160 = ripemd160::Hash;
    type Hash160 = hash160::Hash;

    fn is_uncompressed(&self) -> bool {
        match self {
            Self::Single(SinglePub { key: SinglePubKey::FullKey(ref key), .. }) => {
                key.is_uncompressed()
            }
            _ => false,
        }
    }

    fn is_x_only_key(&self) -> bool {
        matches!(self, Self::Single(SinglePub { key: SinglePubKey::XOnly(ref _key), .. }))
    }

    fn num_der_paths(&self) -> usize {
        match self {
            Self::Single(_) => 0,
            Self::XPub(_) => 1,
            Self::MultiXPub(xpub) => xpub.derivation_paths.paths().len(),
        }
    }
}

impl DefiniteDescriptorKey {
    /// Computes the public key corresponding to this descriptor key.
    /// When deriving from an XOnlyPublicKey, it adds the default 0x02 y-coordinate
    /// and returns the obtained full [`bitcoin::PublicKey`]. All BIP32 derivations
    /// always return a compressed key
    ///
    /// Will return an error if the descriptor key has any hardened derivation steps in its path. To
    /// avoid this error you should replace any such public keys first with [`crate::Descriptor::translate_pk`].
    pub fn derive_public_key<C: Verification>(&self, secp: &Secp256k1<C>) -> bitcoin::PublicKey {
        match self.0 {
            DescriptorPublicKey::Single(ref pk) => match pk.key {
                SinglePubKey::FullKey(pk) => pk,
                SinglePubKey::XOnly(xpk) => xpk.to_public_key(),
            },
            DescriptorPublicKey::XPub(ref xpk) => match xpk.wildcard {
                Wildcard::Unhardened | Wildcard::Hardened => {
                    unreachable!("impossible by construction of DefiniteDescriptorKey")
                }
                Wildcard::None => match xpk.xkey.derive_pub(secp, &xpk.derivation_path.as_ref()) {
                    Ok(xpub) => bitcoin::PublicKey::new(xpub.public_key),
                    Err(bip32::Error::CannotDeriveFromHardenedKey) => {
                        unreachable!("impossible by construction of DefiniteDescriptorKey")
                    }
                    Err(e) => unreachable!("cryptographically unreachable: {}", e),
                },
            },
            DescriptorPublicKey::MultiXPub(_) => {
                unreachable!("impossible by construction of DefiniteDescriptorKey")
            }
        }
    }

    /// Construct an instance from a descriptor key and a derivation index
    ///
    /// Returns `None` if the key contains a wildcard
    pub fn new(key: DescriptorPublicKey) -> Result<Self, NonDefiniteKeyError> {
        if key.has_wildcard() {
            Err(NonDefiniteKeyError::Wildcard)
        } else if key.has_hardened_step() {
            Err(NonDefiniteKeyError::HardenedStep)
        } else if key.is_multipath() {
            Err(NonDefiniteKeyError::Multipath)
        } else {
            Ok(Self(key))
        }
    }

    /// The fingerprint of the master key associated with this key, `0x00000000` if none.
    pub fn master_fingerprint(&self) -> bip32::Fingerprint { self.0.master_fingerprint() }

    /// Full path from the master key if not a multipath extended key.
    pub fn full_derivation_path(&self) -> Option<bip32::DerivationPath> {
        self.0.full_derivation_path()
    }

    /// Full paths from the master key. The vector will contain just one path for single
    /// keys, and multiple ones for multipath extended keys
    pub fn full_derivation_paths(&self) -> Vec<bip32::DerivationPath> {
        self.0.full_derivation_paths()
    }

    /// Reference to the underlying `DescriptorPublicKey`
    pub fn as_descriptor_public_key(&self) -> &DescriptorPublicKey { &self.0 }

    /// Converts the definite key into a generic one
    pub fn into_descriptor_public_key(self) -> DescriptorPublicKey { self.0 }
}

impl FromStr for DefiniteDescriptorKey {
    type Err = DescriptorKeyParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let d = DescriptorPublicKey::from_str(s)?;
        Self::new(d).map_err(DescriptorKeyParseError::NonDefiniteKey)
    }
}

impl fmt::Display for DefiniteDescriptorKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

impl MiniscriptKey for DefiniteDescriptorKey {
    type Sha256 = sha256::Hash;
    type Hash256 = hash256::Hash;
    type Ripemd160 = ripemd160::Hash;
    type Hash160 = hash160::Hash;

    fn is_uncompressed(&self) -> bool { self.0.is_uncompressed() }

    fn is_x_only_key(&self) -> bool { self.0.is_x_only_key() }

    fn num_der_paths(&self) -> usize { self.0.num_der_paths() }
}

impl ToPublicKey for DefiniteDescriptorKey {
    fn to_public_key(&self) -> bitcoin::PublicKey {
        let secp = Secp256k1::verification_only();
        self.derive_public_key(&secp)
    }

    fn to_sha256(hash: &sha256::Hash) -> sha256::Hash { *hash }

    fn to_hash256(hash: &hash256::Hash) -> hash256::Hash { *hash }

    fn to_ripemd160(hash: &ripemd160::Hash) -> ripemd160::Hash { *hash }

    fn to_hash160(hash: &hash160::Hash) -> hash160::Hash { *hash }
}

impl From<DefiniteDescriptorKey> for DescriptorPublicKey {
    fn from(d: DefiniteDescriptorKey) -> Self { d.0 }
}

impl Borrow<DescriptorPublicKey> for DefiniteDescriptorKey {
    fn borrow(&self) -> &DescriptorPublicKey { &self.0 }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for DescriptorPublicKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Self::from_str(&s).map_err(crate::serde::de::Error::custom)
    }
}

#[cfg(feature = "serde")]
impl Serialize for DescriptorPublicKey {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

#[cfg(test)]
mod test {
    use core::str::FromStr;

    use bitcoin::bip32;
    #[cfg(feature = "serde")]
    use serde_test::{assert_tokens, Token};

    use super::{
        DescriptorMultiXKey, DescriptorPublicKey, DescriptorSecretKey, MiniscriptKey, Wildcard,
    };
    use crate::descriptor::key::NonDefiniteKeyError;
    use crate::prelude::*;
    use crate::DefiniteDescriptorKey;

    #[test]
    fn parse_descriptor_key_errors() {
        // And ones with misplaced wildcard
        let desc = "[78412e3a/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*/44";
        assert_eq!(
            DescriptorPublicKey::from_str(desc).unwrap_err().to_string(),
            "\'*\' may only appear as last element in a derivation path"
        );

        // And ones with invalid fingerprints
        let desc = "[NonHexor]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*";
        assert_eq!(
            DescriptorPublicKey::from_str(desc).unwrap_err().to_string(),
            "on master fingerprint 'NonHexor': failed to parse hex digit"
        );

        // And ones with invalid xpubs..
        let desc = "[78412e3a]xpub1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaLcgJvLJuZZvRcEL/1/*";
        assert_eq!(
            DescriptorPublicKey::from_str(desc).unwrap_err().to_string(),
            "base58 encoding error"
        );

        // ..or invalid raw keys
        let desc = "[78412e3a]0208a117f3897c3a13c9384b8695eed98dc31bc2500feb19a1af424cd47a5d83/1/*";
        assert_eq!(
            DescriptorPublicKey::from_str(desc).unwrap_err().to_string(),
            "public keys must be 64, 66 or 130 characters in size",
        );

        // ..or invalid separators
        let desc = "[78412e3a]]03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8";
        assert_eq!(
            DescriptorPublicKey::from_str(desc).unwrap_err().to_string(),
            "multiple \']\' in Descriptor Public Key"
        );

        // fuzzer errors
        let desc = "[11111f11]033333333333333333333333333333323333333333333333333333333433333333]]333]]3]]101333333333333433333]]]10]333333mmmm";
        assert_eq!(
            DescriptorPublicKey::from_str(desc).unwrap_err().to_string(),
            "multiple \']\' in Descriptor Public Key"
        );

        // fuzz failure, hybrid keys
        let desc = "0777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777";
        assert_eq!(
            DescriptorPublicKey::from_str(desc).unwrap_err().to_string(),
            "only full public keys with prefixes '02', '03' or '04' are allowed"
        );
    }

    #[test]
    fn parse_descriptor_secret_key_error() {
        // Xpubs are invalid
        let secret_key = "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL";
        assert_eq!(
            DescriptorSecretKey::from_str(secret_key)
                .unwrap_err()
                .to_string(),
            "unknown version magic bytes: [4, 136, 178, 30]"
        );

        // And ones with invalid fingerprints
        let desc = "[NonHexor]tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/1/*";
        assert_eq!(
            DescriptorSecretKey::from_str(desc).unwrap_err().to_string(),
            "on master fingerprint 'NonHexor': failed to parse hex digit"
        );

        // ..or invalid raw keys
        let desc = "[78412e3a]L32jTfVLei6BYTPUpwpJSkrHx8iL9GZzeErVS8y4Y/1/*";
        assert_eq!(DescriptorSecretKey::from_str(desc).unwrap_err().to_string(), "invalid base58");
    }

    #[test]
    fn test_wildcard() {
        let public_key = DescriptorPublicKey::from_str("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2").unwrap();
        assert_eq!(public_key.master_fingerprint().to_string(), "abcdef00");
        assert_eq!(public_key.full_derivation_path().unwrap().to_string(), "0'/1'/2");
        assert!(!public_key.has_wildcard());

        let public_key = DescriptorPublicKey::from_str("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/*").unwrap();
        assert_eq!(public_key.master_fingerprint().to_string(), "abcdef00");
        assert_eq!(public_key.full_derivation_path().unwrap().to_string(), "0'/1'");
        assert!(public_key.has_wildcard());

        let public_key = DescriptorPublicKey::from_str("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/*h").unwrap();
        assert_eq!(public_key.master_fingerprint().to_string(), "abcdef00");
        assert_eq!(public_key.full_derivation_path().unwrap().to_string(), "0'/1'");
        assert!(public_key.has_wildcard());
    }

    #[test]
    fn test_deriv_on_xprv() {
        let secp = secp256k1::Secp256k1::signing_only();

        let secret_key = DescriptorSecretKey::from_str("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/0'/1'/2").unwrap();
        let public_key = secret_key.to_public(&secp).unwrap();
        assert_eq!(public_key.to_string(), "[2cbe2a6d/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2");
        assert_eq!(public_key.master_fingerprint().to_string(), "2cbe2a6d");
        assert_eq!(public_key.full_derivation_path().unwrap().to_string(), "0'/1'/2");
        assert!(!public_key.has_wildcard());

        let secret_key = DescriptorSecretKey::from_str("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/0'/1'/2'").unwrap();
        let public_key = secret_key.to_public(&secp).unwrap();
        assert_eq!(public_key.to_string(), "[2cbe2a6d/0'/1'/2']tpubDDPuH46rv4dbFtmF6FrEtJEy1CvLZonyBoVxF6xsesHdYDdTBrq2mHhm8AbsPh39sUwL2nZyxd6vo4uWNTU9v4t893CwxjqPnwMoUACLvMV");
        assert_eq!(public_key.master_fingerprint().to_string(), "2cbe2a6d");
        assert_eq!(public_key.full_derivation_path().unwrap().to_string(), "0'/1'/2'");

        let secret_key = DescriptorSecretKey::from_str("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/0/1/2").unwrap();
        let public_key = secret_key.to_public(&secp).unwrap();
        assert_eq!(public_key.to_string(), "tpubD6NzVbkrYhZ4WQdzxL7NmJN7b85ePo4p6RSj9QQHF7te2RR9iUeVSGgnGkoUsB9LBRosgvNbjRv9bcsJgzgBd7QKuxDm23ZewkTRzNSLEDr/0/1/2");
        assert_eq!(public_key.master_fingerprint().to_string(), "2cbe2a6d");
        assert_eq!(public_key.full_derivation_path().unwrap().to_string(), "0/1/2");

        let secret_key = DescriptorSecretKey::from_str("[aabbccdd]tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/0/1/2").unwrap();
        let public_key = secret_key.to_public(&secp).unwrap();
        assert_eq!(public_key.to_string(), "[aabbccdd]tpubD6NzVbkrYhZ4WQdzxL7NmJN7b85ePo4p6RSj9QQHF7te2RR9iUeVSGgnGkoUsB9LBRosgvNbjRv9bcsJgzgBd7QKuxDm23ZewkTRzNSLEDr/0/1/2");
        assert_eq!(public_key.master_fingerprint().to_string(), "aabbccdd");
        assert_eq!(public_key.full_derivation_path().unwrap().to_string(), "0/1/2");

        let secret_key = DescriptorSecretKey::from_str("[aabbccdd/90']tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/0'/1'/2").unwrap();
        let public_key = secret_key.to_public(&secp).unwrap();
        assert_eq!(public_key.to_string(), "[aabbccdd/90'/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2");
        assert_eq!(public_key.master_fingerprint().to_string(), "aabbccdd");
        assert_eq!(public_key.full_derivation_path().unwrap().to_string(), "90'/0'/1'/2");
    }

    #[test]
    fn test_master_fingerprint() {
        assert_eq!(
            DescriptorPublicKey::from_str(
                "02a489e0ea42b56148d212d325b7c67c6460483ff931c303ea311edfef667c8f35",
            )
            .unwrap()
            .master_fingerprint()
            .as_bytes(),
            b"\xb0\x59\x11\x6a"
        );
    }

    fn get_multipath_xpub(key_str: &str, num_paths: usize) -> DescriptorMultiXKey<bip32::Xpub> {
        let desc_key = DescriptorPublicKey::from_str(key_str).unwrap();
        assert_eq!(desc_key.num_der_paths(), num_paths);
        match desc_key {
            DescriptorPublicKey::MultiXPub(xpub) => xpub,
            _ => unreachable!(),
        }
    }

    fn get_multipath_xprv(key_str: &str) -> DescriptorMultiXKey<bip32::Xpriv> {
        let desc_key = DescriptorSecretKey::from_str(key_str).unwrap();
        match desc_key {
            DescriptorSecretKey::MultiXPrv(xprv) => xprv,
            _ => unreachable!(),
        }
    }

    #[test]
    fn multipath_extended_keys() {
        let secp = secp256k1::Secp256k1::signing_only();

        // We can have a key in a descriptor that has multiple paths
        let xpub = get_multipath_xpub("tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2/<0;1;42;9854>", 4);
        assert_eq!(
            xpub.derivation_paths.paths(),
            &vec![
                bip32::DerivationPath::from_str("m/2/0").unwrap(),
                bip32::DerivationPath::from_str("m/2/1").unwrap(),
                bip32::DerivationPath::from_str("m/2/42").unwrap(),
                bip32::DerivationPath::from_str("m/2/9854").unwrap()
            ],
        );
        assert_eq!(
            xpub,
            get_multipath_xpub(&DescriptorPublicKey::MultiXPub(xpub.clone()).to_string(), 4)
        );
        // Even if it's in the middle of the derivation path.
        let xpub = get_multipath_xpub("tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2/<0;1;9854>/0/5/10", 3);
        assert_eq!(
            xpub.derivation_paths.paths(),
            &vec![
                bip32::DerivationPath::from_str("m/2/0/0/5/10").unwrap(),
                bip32::DerivationPath::from_str("m/2/1/0/5/10").unwrap(),
                bip32::DerivationPath::from_str("m/2/9854/0/5/10").unwrap()
            ],
        );
        assert_eq!(
            xpub,
            get_multipath_xpub(&DescriptorPublicKey::MultiXPub(xpub.clone()).to_string(), 3)
        );
        // Even if it is a wildcard extended key.
        let xpub = get_multipath_xpub("tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2/<0;1;9854>/3456/9876/*", 3);
        assert_eq!(xpub.wildcard, Wildcard::Unhardened);
        assert_eq!(
            xpub.derivation_paths.paths(),
            &vec![
                bip32::DerivationPath::from_str("m/2/0/3456/9876").unwrap(),
                bip32::DerivationPath::from_str("m/2/1/3456/9876").unwrap(),
                bip32::DerivationPath::from_str("m/2/9854/3456/9876").unwrap()
            ],
        );
        assert_eq!(
            xpub,
            get_multipath_xpub(&DescriptorPublicKey::MultiXPub(xpub.clone()).to_string(), 3)
        );
        // Also even if it has an origin.
        let xpub = get_multipath_xpub("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/<0;1>/*", 2);
        assert_eq!(xpub.wildcard, Wildcard::Unhardened);
        assert_eq!(
            xpub.derivation_paths.paths(),
            &vec![
                bip32::DerivationPath::from_str("m/0").unwrap(),
                bip32::DerivationPath::from_str("m/1").unwrap(),
            ],
        );
        assert_eq!(
            xpub,
            get_multipath_xpub(&DescriptorPublicKey::MultiXPub(xpub.clone()).to_string(), 2)
        );
        // Also if it has hardened steps in the derivation path. In fact, it can also have hardened
        // indexes even at the step with multiple indexes!
        let xpub = get_multipath_xpub("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/9478'/<0';1h>/8h/*'", 2);
        assert_eq!(xpub.wildcard, Wildcard::Hardened);
        assert_eq!(
            xpub.derivation_paths.paths(),
            &vec![
                bip32::DerivationPath::from_str("m/9478'/0'/8'").unwrap(),
                bip32::DerivationPath::from_str("m/9478h/1h/8h").unwrap(),
            ],
        );
        assert_eq!(
            xpub,
            get_multipath_xpub(&DescriptorPublicKey::MultiXPub(xpub.clone()).to_string(), 2)
        );
        // You can't get the "full derivation path" for a multipath extended public key.
        let desc_key = DescriptorPublicKey::from_str("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/9478'/<0';1>/8h/*'").unwrap();
        assert!(desc_key.full_derivation_path().is_none());
        assert!(desc_key.is_multipath());
        // But you can get all the derivation paths
        assert_eq!(
            desc_key.full_derivation_paths(),
            vec![
                bip32::DerivationPath::from_str("m/0'/1'/9478'/0'/8'").unwrap(),
                bip32::DerivationPath::from_str("m/0'/1'/9478'/1/8'").unwrap(),
            ],
        );
        assert_eq!(desc_key.into_single_keys(), vec![DescriptorPublicKey::from_str("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/9478'/0'/8h/*'").unwrap(), DescriptorPublicKey::from_str("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/9478'/1/8h/*'").unwrap()]);

        // All the same but with extended private keys instead of xpubs.
        let xprv = get_multipath_xprv("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/2/<0;1;42;9854>");
        assert_eq!(
            xprv.derivation_paths.paths(),
            &vec![
                bip32::DerivationPath::from_str("m/2/0").unwrap(),
                bip32::DerivationPath::from_str("m/2/1").unwrap(),
                bip32::DerivationPath::from_str("m/2/42").unwrap(),
                bip32::DerivationPath::from_str("m/2/9854").unwrap()
            ],
        );
        assert_eq!(
            xprv,
            get_multipath_xprv(&DescriptorSecretKey::MultiXPrv(xprv.clone()).to_string())
        );
        let xprv = get_multipath_xprv("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/2/<0;1;9854>/0/5/10");
        assert_eq!(
            xprv.derivation_paths.paths(),
            &vec![
                bip32::DerivationPath::from_str("m/2/0/0/5/10").unwrap(),
                bip32::DerivationPath::from_str("m/2/1/0/5/10").unwrap(),
                bip32::DerivationPath::from_str("m/2/9854/0/5/10").unwrap()
            ],
        );
        assert_eq!(
            xprv,
            get_multipath_xprv(&DescriptorSecretKey::MultiXPrv(xprv.clone()).to_string())
        );
        let xprv = get_multipath_xprv("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/2/<0;1;9854>/3456/9876/*");
        assert_eq!(xprv.wildcard, Wildcard::Unhardened);
        assert_eq!(
            xprv.derivation_paths.paths(),
            &vec![
                bip32::DerivationPath::from_str("m/2/0/3456/9876").unwrap(),
                bip32::DerivationPath::from_str("m/2/1/3456/9876").unwrap(),
                bip32::DerivationPath::from_str("m/2/9854/3456/9876").unwrap()
            ],
        );
        assert_eq!(
            xprv,
            get_multipath_xprv(&DescriptorSecretKey::MultiXPrv(xprv.clone()).to_string())
        );
        let xprv = get_multipath_xprv("[abcdef00/0'/1']tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/<0;1>/*");
        assert_eq!(xprv.wildcard, Wildcard::Unhardened);
        assert_eq!(
            xprv.derivation_paths.paths(),
            &vec![
                bip32::DerivationPath::from_str("m/0").unwrap(),
                bip32::DerivationPath::from_str("m/1").unwrap(),
            ],
        );
        assert_eq!(
            xprv,
            get_multipath_xprv(&DescriptorSecretKey::MultiXPrv(xprv.clone()).to_string())
        );
        let xprv = get_multipath_xprv("[abcdef00/0'/1']tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/9478'/<0';1h>/8h/*'");
        assert_eq!(xprv.wildcard, Wildcard::Hardened);
        assert_eq!(
            xprv.derivation_paths.paths(),
            &vec![
                bip32::DerivationPath::from_str("m/9478'/0'/8'").unwrap(),
                bip32::DerivationPath::from_str("m/9478h/1h/8h").unwrap(),
            ],
        );
        assert_eq!(
            xprv,
            get_multipath_xprv(&DescriptorSecretKey::MultiXPrv(xprv.clone()).to_string())
        );
        let desc_key = DescriptorSecretKey::from_str("[abcdef00/0'/1']tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/9478'/<0';1>/8h/*'").unwrap();
        assert!(desc_key.to_public(&secp).is_err());
        assert!(desc_key.is_multipath());
        assert_eq!(desc_key.into_single_keys(), vec![DescriptorSecretKey::from_str("[abcdef00/0'/1']tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/9478'/0'/8h/*'").unwrap(), DescriptorSecretKey::from_str("[abcdef00/0'/1']tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/9478'/1/8h/*'").unwrap()]);

        // It's invalid to:
        // - Not have opening or closing brackets
        // - Have multiple steps with different indexes
        // - Only have one index within the brackets
        DescriptorPublicKey::from_str("tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2/<0;1;42;9854").unwrap_err();
        DescriptorPublicKey::from_str("tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2/0;1;42;9854>").unwrap_err();
        DescriptorPublicKey::from_str("tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2/4/<0;1>/96/<0;1>").unwrap_err();
        DescriptorPublicKey::from_str("tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2/4/<0>").unwrap_err();
        DescriptorPublicKey::from_str("tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2/4/<0;>").unwrap_err();
        DescriptorPublicKey::from_str("tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2/4/<;1>").unwrap_err();
        DescriptorPublicKey::from_str("tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2/4/<0;1;>").unwrap_err();
    }

    #[test]
    fn test_multixprv_to_public() {
        let secp = secp256k1::Secp256k1::signing_only();

        // Works if all hardended derivation steps are part of the shared path
        let xprv = get_multipath_xprv("[01020304/5]tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/1'/2'/3/<4;5>/6");
        let xpub = DescriptorPublicKey::MultiXPub(xprv.to_public(&secp).unwrap()); // wrap in a DescriptorPublicKey to have Display
        assert_eq!(xpub.to_string(), "[01020304/5/1'/2']tpubDBTRkEMEFkUbk3WTz6CFSULyswkTPpPr38AWibf5TVkB5GxuBxbSbmdFGr3jmswwemknyYxAGoX7BJnKfyPy4WXaHmcrxZhfzFwoUFvFtm5/3/<4;5>/6");

        // Fails if they're part of the multi-path specifier or following it
        get_multipath_xprv("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/1/2/<3';4'>/5").to_public(&secp).unwrap_err();
        get_multipath_xprv("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/1/2/<3;4>/5/6'").to_public(&secp).unwrap_err();
    }

    #[test]
    fn test_parse_wif() {
        let secret_key = "[0dd03d09/0'/1/2']5HueCGU8rMjxEXxiPuD5BDku4MkFqeZyd4dZ1jvhTVqvbTLvyTJ"
            .parse()
            .unwrap();
        if let DescriptorSecretKey::Single(single) = secret_key {
            assert_eq!(
                single.key.inner,
                "0C28FCA386C7A227600B2FE50B7CAE11EC86D3BF1FBE471BE89827E19D72AA1D"
                    .parse()
                    .unwrap()
            );
            assert_eq!(
                single.origin,
                Some(("0dd03d09".parse().unwrap(), "m/0'/1/2'".parse().unwrap()))
            );
        } else {
            panic!("expected a DescriptorSecretKey::Single");
        }
    }

    #[test]
    #[cfg(feature = "serde")]
    fn test_descriptor_public_key_serde() {
        let desc = "[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2";
        let public_key = DescriptorPublicKey::from_str(desc).unwrap();
        assert_tokens(&public_key, &[Token::String(desc)]);
    }

    #[test]
    fn definite_keys() {
        // basic xpub
        let desc = "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8"
            .parse::<DescriptorPublicKey>()
            .unwrap();
        assert!(matches!(DefiniteDescriptorKey::new(desc), Ok(..)));
        // xpub with wildcard
        let desc = "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8/*"
            .parse::<DescriptorPublicKey>()
            .unwrap();
        assert!(matches!(DefiniteDescriptorKey::new(desc), Err(NonDefiniteKeyError::Wildcard)));
        // multipath xpub
        let desc = "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8/<0;1>"
            .parse::<DescriptorPublicKey>()
            .unwrap();
        assert!(matches!(DefiniteDescriptorKey::new(desc), Err(NonDefiniteKeyError::Multipath)));
        // xpub with hardened path
        let desc = "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8/1'/2"
            .parse::<DescriptorPublicKey>()
            .unwrap();
        assert!(matches!(
            DefiniteDescriptorKey::new(desc),
            Err(NonDefiniteKeyError::HardenedStep)
        ));
    }

    #[test]
    fn test_xkey_network() {
        use bitcoin::NetworkKind;

        // Test mainnet xpub
        let mainnet_xpub = "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8"
            .parse::<DescriptorPublicKey>()
            .unwrap();
        assert_eq!(mainnet_xpub.xkey_network(), Some(NetworkKind::Main));

        // Test testnet xpub
        let testnet_xpub = "tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi"
            .parse::<DescriptorPublicKey>()
            .unwrap();
        assert_eq!(testnet_xpub.xkey_network(), Some(NetworkKind::Test));

        // Test single public key (no extended key)
        let single_key = "021d4ea7132d4e1a362ee5efd8d0b59dd4d1fe8906eefa7dd812b05a46b73d829b"
            .parse::<DescriptorPublicKey>()
            .unwrap();
        assert_eq!(single_key.xkey_network(), None);
    }
}
