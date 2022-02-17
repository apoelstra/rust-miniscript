use std::{error, fmt, str::FromStr};

use bitcoin::{
    self,
    hashes::Hash,
    hashes::{hex::FromHex, HashEngine},
    secp256k1,
    secp256k1::{Secp256k1, Signing},
    util::bip32,
    XOnlyPublicKey, XpubIdentifier,
};

use {MiniscriptKey, ToPublicKey};

/// Single public key without any origin or range information
#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub enum SinglePubKey {
    /// FullKey (compressed or uncompressed)
    FullKey(bitcoin::PublicKey),
    /// XOnlyPublicKey
    XOnly(XOnlyPublicKey),
}

/// The MiniscriptKey corresponding to Descriptors. This can
/// either be Single public key or a Xpub
#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub enum DescriptorPublicKey {
    /// Single Public Key
    SinglePub(DescriptorSinglePub),
    /// Xpub
    XPub(DescriptorXKey<bip32::ExtendedPubKey>),
}

/// A Single Descriptor Key with optional origin information
#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub struct DescriptorSinglePub {
    /// Origin information
    pub origin: Option<(bip32::Fingerprint, bip32::DerivationPath)>,
    /// The key
    pub key: SinglePubKey,
}

/// A Single Descriptor Secret Key with optional origin information
#[derive(Debug)]
pub struct DescriptorSinglePriv {
    /// Origin information
    pub origin: Option<bip32::KeySource>,
    /// The key
    pub key: bitcoin::PrivateKey,
}

/// A Secret Key that can be either a single key or an Xprv
#[derive(Debug)]
pub enum DescriptorSecretKey {
    /// Single Secret Key
    SinglePriv(DescriptorSinglePriv),
    /// Xprv
    XPrv(DescriptorXKey<bip32::ExtendedPrivKey>),
}

impl fmt::Display for DescriptorSecretKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &DescriptorSecretKey::SinglePriv(ref sk) => {
                maybe_fmt_master_id(f, &sk.origin)?;
                sk.key.fmt(f)?;
                Ok(())
            }
            &DescriptorSecretKey::XPrv(ref xprv) => {
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
        }
    }
}

/// Trait for "extended key" types like `xpub` and `xprv`. Used internally to generalize parsing and
/// handling of `bip32::ExtendedPubKey` and `bip32::ExtendedPrivKey`.
pub trait InnerXKey: fmt::Display + FromStr {
    /// Returns the fingerprint of the key
    fn xkey_fingerprint<C: Signing>(&self, secp: &Secp256k1<C>) -> bip32::Fingerprint;

    /// Returns whether hardened steps can be derived on the key
    ///
    /// `true` for `bip32::ExtendedPrivKey` and `false` for `bip32::ExtendedPubKey`.
    fn can_derive_hardened() -> bool;
}

impl InnerXKey for bip32::ExtendedPubKey {
    fn xkey_fingerprint<C: Signing>(&self, _secp: &Secp256k1<C>) -> bip32::Fingerprint {
        self.fingerprint()
    }

    fn can_derive_hardened() -> bool {
        false
    }
}

impl InnerXKey for bip32::ExtendedPrivKey {
    fn xkey_fingerprint<C: Signing>(&self, secp: &Secp256k1<C>) -> bip32::Fingerprint {
        self.fingerprint(secp)
    }

    fn can_derive_hardened() -> bool {
        true
    }
}

/// Whether a descriptor has a wildcard in it
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Wildcard {
    /// No wildcard
    None,
    /// Unhardened wildcard, e.g. *
    Unhardened,
    /// Unhardened wildcard, e.g. *h
    Hardened,
}

/// Instance of an extended key with origin and derivation path
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

impl DescriptorSinglePriv {
    /// Returns the public key of this key
    fn as_public<C: Signing>(
        &self,
        secp: &Secp256k1<C>,
    ) -> Result<DescriptorSinglePub, DescriptorKeyParseError> {
        let pub_key = self.key.public_key(secp);

        Ok(DescriptorSinglePub {
            origin: self.origin.clone(),
            key: SinglePubKey::FullKey(pub_key),
        })
    }
}

impl DescriptorXKey<bip32::ExtendedPrivKey> {
    /// Returns the public version of this key, applying all the hardened derivation steps on the
    /// private key before turning it into a public key.
    ///
    /// If the key already has an origin, the derivation steps applied will be appended to the path
    /// already present, otherwise this key will be treated as "root" key and an origin will be
    /// added with this key's fingerprint and the derivation steps applied.
    fn as_public<C: Signing>(
        &self,
        secp: &Secp256k1<C>,
    ) -> Result<DescriptorXKey<bip32::ExtendedPubKey>, DescriptorKeyParseError> {
        let path_len = (&self.derivation_path).as_ref().len();
        let public_suffix_len = (&self.derivation_path)
            .into_iter()
            .rev()
            .take_while(|c| c.is_normal())
            .count();

        let derivation_path = &self.derivation_path[(path_len - public_suffix_len)..];
        let deriv_on_hardened = &self.derivation_path[..(path_len - public_suffix_len)];

        let derived_xprv = self
            .xkey
            .derive_priv(&secp, &deriv_on_hardened)
            .map_err(|_| DescriptorKeyParseError("Unable to derive the hardened steps"))?;
        let xpub = bip32::ExtendedPubKey::from_priv(&secp, &derived_xprv);

        let origin = match &self.origin {
            &Some((fingerprint, ref origin_path)) => Some((
                fingerprint,
                origin_path
                    .into_iter()
                    .chain(deriv_on_hardened.into_iter())
                    .cloned()
                    .collect(),
            )),
            &None if !deriv_on_hardened.as_ref().is_empty() => {
                Some((self.xkey.fingerprint(&secp), deriv_on_hardened.into()))
            }
            _ => self.origin.clone(),
        };

        Ok(DescriptorXKey {
            origin,
            xkey: xpub,
            derivation_path: derivation_path.into(),
            wildcard: self.wildcard,
        })
    }
}

/// Descriptor Key parsing errors
// FIXME: replace with error enums
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct DescriptorKeyParseError(&'static str);

impl fmt::Display for DescriptorKeyParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl error::Error for DescriptorKeyParseError {}

impl fmt::Display for DescriptorPublicKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DescriptorPublicKey::SinglePub(ref pk) => {
                maybe_fmt_master_id(f, &pk.origin)?;
                match pk.key {
                    SinglePubKey::FullKey(full_key) => full_key.fmt(f),
                    SinglePubKey::XOnly(x_only_key) => x_only_key.fmt(f),
                }?;
                Ok(())
            }
            DescriptorPublicKey::XPub(ref xpub) => {
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
        }
    }
}

impl DescriptorSecretKey {
    /// Return the public version of this key, by applying either
    /// [`DescriptorSinglePriv::as_public`] or [`DescriptorXKey<bip32::ExtendedPrivKey>::as_public`]
    /// depending on the type of key.
    ///
    /// If the key is an "XPrv", the hardened derivation steps will be applied before converting it
    /// to a public key. See the documentation of [`DescriptorXKey<bip32::ExtendedPrivKey>::as_public`]
    /// for more details.
    pub fn as_public<C: Signing>(
        &self,
        secp: &Secp256k1<C>,
    ) -> Result<DescriptorPublicKey, DescriptorKeyParseError> {
        Ok(match self {
            &DescriptorSecretKey::SinglePriv(ref sk) => {
                DescriptorPublicKey::SinglePub(sk.as_public(secp)?)
            }
            &DescriptorSecretKey::XPrv(ref xprv) => {
                DescriptorPublicKey::XPub(xprv.as_public(secp)?)
            }
        })
    }
}

/// Writes the fingerprint of the origin, if there is one.
fn maybe_fmt_master_id(
    f: &mut fmt::Formatter,
    origin: &Option<(bip32::Fingerprint, bip32::DerivationPath)>,
) -> fmt::Result {
    if let Some((ref master_id, ref master_deriv)) = *origin {
        fmt::Formatter::write_str(f, "[")?;
        for byte in master_id.into_bytes().iter() {
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

impl FromStr for DescriptorPublicKey {
    type Err = DescriptorKeyParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // A "raw" public key without any origin is the least we accept.
        if s.len() < 64 {
            return Err(DescriptorKeyParseError(
                "Key too short (<66 char), doesn't match any format",
            ));
        }

        let (key_part, origin) = DescriptorXKey::<bip32::ExtendedPubKey>::parse_xkey_origin(s)?;

        if key_part.contains("pub") {
            let (xpub, derivation_path, wildcard) =
                DescriptorXKey::<bip32::ExtendedPubKey>::parse_xkey_deriv(key_part)?;

            Ok(DescriptorPublicKey::XPub(DescriptorXKey {
                origin,
                xkey: xpub,
                derivation_path,
                wildcard,
            }))
        } else {
            let key = match key_part.len() {
                64 => {
                    let x_only_key = XOnlyPublicKey::from_str(key_part).map_err(|_| {
                        DescriptorKeyParseError("Error while parsing simple xonly key")
                    })?;
                    SinglePubKey::XOnly(x_only_key)
                }
                66 | 130 => {
                    if !(&key_part[0..2] == "02"
                        || &key_part[0..2] == "03"
                        || &key_part[0..2] == "04")
                    {
                        return Err(DescriptorKeyParseError(
                            "Only publickeys with prefixes 02/03/04 are allowed",
                        ));
                    }
                    let key = bitcoin::PublicKey::from_str(key_part).map_err(|_| {
                        DescriptorKeyParseError("Error while parsing simple public key")
                    })?;
                    SinglePubKey::FullKey(key)
                }
                _ => {
                    return Err(DescriptorKeyParseError(
                        "Public keys must be 64/66/130 characters in size",
                    ))
                }
            };
            Ok(DescriptorPublicKey::SinglePub(DescriptorSinglePub {
                key,
                origin,
            }))
        }
    }
}

/// Descriptor key conversion error
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum ConversionError {
    /// Attempted to convert a key with a wildcard to a bitcoin public key
    Wildcard,
    /// Attempted to convert a key with hardened derivations to a bitcoin public key
    HardenedChild,
    /// Attempted to convert a key with a hardened wildcard to a bitcoin public key
    HardenedWildcard,
}

impl fmt::Display for ConversionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match *self {
            ConversionError::Wildcard => "uninstantiated wildcard in bip32 path",
            ConversionError::HardenedChild => "hardened child step in bip32 path",
            ConversionError::HardenedWildcard => {
                "hardened and uninstantiated wildcard in bip32 path"
            }
        })
    }
}

impl error::Error for ConversionError {}

impl DescriptorPublicKey {
    /// The fingerprint of the master key associated with this key, `0x00000000` if none.
    pub fn master_fingerprint(&self) -> bip32::Fingerprint {
        match *self {
            DescriptorPublicKey::XPub(ref xpub) => {
                if let Some((fingerprint, _)) = xpub.origin {
                    fingerprint
                } else {
                    xpub.xkey.fingerprint()
                }
            }
            DescriptorPublicKey::SinglePub(ref single) => {
                if let Some((fingerprint, _)) = single.origin {
                    fingerprint
                } else {
                    let mut engine = XpubIdentifier::engine();
                    match single.key {
                        SinglePubKey::FullKey(pk) => {
                            pk.write_into(&mut engine).expect("engines don't error")
                        }
                        SinglePubKey::XOnly(x_only_pk) => engine.input(&x_only_pk.serialize()),
                    };
                    bip32::Fingerprint::from(&XpubIdentifier::from_engine(engine)[..4])
                }
            }
        }
    }

    /// Full path, from the master key
    ///
    /// For wildcard keys this will return the path up to the wildcard, so you
    /// can get full paths by appending one additional derivation step, according
    /// to the wildcard type (hardened or normal)
    pub fn full_derivation_path(&self) -> bip32::DerivationPath {
        match *self {
            DescriptorPublicKey::XPub(ref xpub) => {
                let origin_path = if let Some((_, ref path)) = xpub.origin {
                    path.clone()
                } else {
                    bip32::DerivationPath::from(vec![])
                };
                origin_path.extend(&xpub.derivation_path)
            }
            DescriptorPublicKey::SinglePub(ref single) => {
                if let Some((_, ref path)) = single.origin {
                    path.clone()
                } else {
                    bip32::DerivationPath::from(vec![])
                }
            }
        }
    }

    /// Whether or not the key has a wildcards
    pub fn is_deriveable(&self) -> bool {
        match *self {
            DescriptorPublicKey::SinglePub(..) => false,
            DescriptorPublicKey::XPub(ref xpub) => xpub.wildcard != Wildcard::None,
        }
    }

    /// If this public key has a wildcard, replace it by the given index
    ///
    /// Panics if given an index ≥ 2^31
    pub fn derive(mut self, index: u32) -> DescriptorPublicKey {
        if let DescriptorPublicKey::XPub(mut xpub) = self {
            match xpub.wildcard {
                Wildcard::None => {}
                Wildcard::Unhardened => {
                    xpub.derivation_path = xpub
                        .derivation_path
                        .into_child(bip32::ChildNumber::from_normal_idx(index).unwrap())
                }
                Wildcard::Hardened => {
                    xpub.derivation_path = xpub
                        .derivation_path
                        .into_child(bip32::ChildNumber::from_hardened_idx(index).unwrap())
                }
            }
            xpub.wildcard = Wildcard::None;
            self = DescriptorPublicKey::XPub(xpub);
        }
        self
    }

    /// Computes the public key corresponding to this descriptor key.
    /// When deriving from an XOnlyPublicKey, it adds the default 0x02 y-coordinate
    /// and returns the obtained full [`bitcoin::PublicKey`]. All BIP32 derivations
    /// always return a compressed key
    ///
    /// Will return an error if the descriptor key has any hardened
    /// derivation steps in its path, or if the key has any wildcards.
    ///
    /// To ensure there are no wildcards, call `.derive(0)` or similar;
    /// to avoid hardened derivation steps, start from a `DescriptorSecretKey`
    /// and call `as_public`, or call `TranslatePk2::translate_pk2` with
    /// some function which has access to secret key data.
    pub fn derive_public_key<C: secp256k1::Verification>(
        &self,
        secp: &Secp256k1<C>,
    ) -> Result<bitcoin::PublicKey, ConversionError> {
        match *self {
            DescriptorPublicKey::SinglePub(ref pk) => match pk.key {
                SinglePubKey::FullKey(pk) => Ok(pk),
                SinglePubKey::XOnly(xpk) => Ok(xpk.to_public_key()),
            },
            DescriptorPublicKey::XPub(ref xpk) => match xpk.wildcard {
                Wildcard::Unhardened => Err(ConversionError::Wildcard),
                Wildcard::Hardened => Err(ConversionError::HardenedWildcard),
                Wildcard::None => match xpk.xkey.derive_pub(secp, &xpk.derivation_path.as_ref()) {
                    Ok(xpub) => Ok(bitcoin::PublicKey::new(xpub.public_key)),
                    Err(bip32::Error::CannotDeriveFromHardenedKey) => {
                        Err(ConversionError::HardenedChild)
                    }
                    Err(e) => unreachable!("cryptographically unreachable: {}", e),
                },
            },
        }
    }
}

impl FromStr for DescriptorSecretKey {
    type Err = DescriptorKeyParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (key_part, origin) = DescriptorXKey::<bip32::ExtendedPubKey>::parse_xkey_origin(s)?;

        if key_part.len() <= 52 {
            let sk = bitcoin::PrivateKey::from_str(key_part)
                .map_err(|_| DescriptorKeyParseError("Error while parsing a WIF private key"))?;
            Ok(DescriptorSecretKey::SinglePriv(DescriptorSinglePriv {
                key: sk,
                origin: None,
            }))
        } else {
            let (xprv, derivation_path, wildcard) =
                DescriptorXKey::<bip32::ExtendedPrivKey>::parse_xkey_deriv(key_part)?;
            Ok(DescriptorSecretKey::XPrv(DescriptorXKey {
                origin,
                xkey: xprv,
                derivation_path,
                wildcard,
            }))
        }
    }
}

impl<K: InnerXKey> DescriptorXKey<K> {
    fn parse_xkey_origin(
        s: &str,
    ) -> Result<(&str, Option<(bip32::Fingerprint, bip32::DerivationPath)>), DescriptorKeyParseError>
    {
        for ch in s.as_bytes() {
            if *ch < 20 || *ch > 127 {
                return Err(DescriptorKeyParseError(
                    "Encountered an unprintable character",
                ));
            }
        }

        if s.is_empty() {
            return Err(DescriptorKeyParseError("Empty key"));
        }
        let mut parts = s[1..].split(']');

        if let Some('[') = s.chars().next() {
            let mut raw_origin = parts
                .next()
                .ok_or(DescriptorKeyParseError("Unclosed '['"))?
                .split('/');

            let origin_id_hex = raw_origin.next().ok_or(DescriptorKeyParseError(
                "No master fingerprint found after '['",
            ))?;

            if origin_id_hex.len() != 8 {
                return Err(DescriptorKeyParseError(
                    "Master fingerprint should be 8 characters long",
                ));
            }
            let parent_fingerprint = bip32::Fingerprint::from_hex(origin_id_hex).map_err(|_| {
                DescriptorKeyParseError("Malformed master fingerprint, expected 8 hex chars")
            })?;
            let origin_path = raw_origin
                .map(|p| bip32::ChildNumber::from_str(p))
                .collect::<Result<bip32::DerivationPath, bip32::Error>>()
                .map_err(|_| {
                    DescriptorKeyParseError("Error while parsing master derivation path")
                })?;

            let key = parts
                .next()
                .ok_or(DescriptorKeyParseError("No key after origin."))?;

            if parts.next().is_some() {
                Err(DescriptorKeyParseError(
                    "Multiple ']' in Descriptor Public Key",
                ))
            } else {
                Ok((key, Some((parent_fingerprint, origin_path))))
            }
        } else {
            Ok((s, None))
        }
    }

    /// Parse an extended key concatenated to a derivation path.
    fn parse_xkey_deriv(
        key_deriv: &str,
    ) -> Result<(K, bip32::DerivationPath, Wildcard), DescriptorKeyParseError> {
        let mut key_deriv = key_deriv.split('/');
        let xkey_str = key_deriv.next().ok_or(DescriptorKeyParseError(
            "No key found after origin description",
        ))?;
        let xkey = K::from_str(xkey_str)
            .map_err(|_| DescriptorKeyParseError("Error while parsing xkey."))?;

        let mut wildcard = Wildcard::None;
        let derivation_path = key_deriv
            .filter_map(|p| {
                if wildcard == Wildcard::None && p == "*" {
                    wildcard = Wildcard::Unhardened;
                    None
                } else if wildcard == Wildcard::None && (p == "*'" || p == "*h") {
                    wildcard = Wildcard::Hardened;
                    None
                } else if wildcard != Wildcard::None {
                    Some(Err(DescriptorKeyParseError(
                        "'*' may only appear as last element in a derivation path.",
                    )))
                } else {
                    Some(bip32::ChildNumber::from_str(p).map_err(|_| {
                        DescriptorKeyParseError("Error while parsing key derivation path")
                    }))
                }
            })
            .collect::<Result<bip32::DerivationPath, _>>()?;

        Ok((xkey, derivation_path, wildcard))
    }

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
    /// # fn body() -> Result<(), Box<dyn std::error::Error>> {
    /// use miniscript::bitcoin::util::bip32;
    /// use miniscript::descriptor::DescriptorPublicKey;
    ///
    /// let ctx = miniscript::bitcoin::secp256k1::Secp256k1::signing_only();
    ///
    /// let key = DescriptorPublicKey::from_str("[d34db33f/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*")?;
    /// let xpub = match key {
    ///     DescriptorPublicKey::XPub(xpub) => xpub,
    ///     _ => panic!("Parsing Error"),
    /// };
    ///
    /// assert_eq!(xpub.matches(&(bip32::Fingerprint::from_str("d34db33f")?, bip32::DerivationPath::from_str("m/44'/0'/0'/1/42")?), &ctx), Some(bip32::DerivationPath::from_str("m/44'/0'/0'/1")?));
    /// assert_eq!(xpub.matches(&(bip32::Fingerprint::from_str("ffffffff")?, bip32::DerivationPath::from_str("m/44'/0'/0'/1/42")?), &ctx), None);
    /// assert_eq!(xpub.matches(&(bip32::Fingerprint::from_str("d34db33f")?, bip32::DerivationPath::from_str("m/44'/0'/0'/100/0")?), &ctx), None);
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

        let (compare_fingerprint, compare_path) = match &self.origin {
            &Some((fingerprint, ref path)) => (
                fingerprint,
                path.into_iter()
                    .chain(self.derivation_path.into_iter())
                    .collect(),
            ),
            &None => (
                self.xkey.xkey_fingerprint(secp),
                self.derivation_path.into_iter().collect::<Vec<_>>(),
            ),
        };

        let path_excluding_wildcard = if self.wildcard != Wildcard::None && path.as_ref().len() > 0
        {
            path.into_iter()
                .take(path.as_ref().len() - 1)
                .cloned()
                .collect()
        } else {
            path.clone()
        };

        if &compare_fingerprint == fingerprint
            && compare_path
                .into_iter()
                .eq(path_excluding_wildcard.into_iter())
        {
            Some(path_excluding_wildcard)
        } else {
            None
        }
    }
}

impl MiniscriptKey for DescriptorPublicKey {
    // This allows us to be able to derive public keys even for PkH s
    type Hash = Self;

    fn is_uncompressed(&self) -> bool {
        match self {
            DescriptorPublicKey::SinglePub(DescriptorSinglePub {
                key: SinglePubKey::FullKey(ref key),
                ..
            }) => key.is_uncompressed(),
            _ => false,
        }
    }

    fn is_x_only_key(&self) -> bool {
        match self {
            DescriptorPublicKey::SinglePub(DescriptorSinglePub {
                key: SinglePubKey::FullKey(ref key),
                ..
            }) => key.is_x_only_key(),
            _ => false,
        }
    }

    fn to_pubkeyhash(&self) -> Self {
        self.clone()
    }
}

#[cfg(test)]
mod test {
    use super::{DescriptorKeyParseError, DescriptorPublicKey, DescriptorSecretKey};

    use bitcoin::secp256k1;

    use std::str::FromStr;

    #[test]
    fn parse_descriptor_key_errors() {
        // And ones with misplaced wildcard
        let desc = "[78412e3a/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*/44";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "\'*\' may only appear as last element in a derivation path."
            ))
        );

        // And ones with invalid fingerprints
        let desc = "[NonHexor]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Malformed master fingerprint, expected 8 hex chars"
            ))
        );

        // And ones with invalid xpubs..
        let desc = "[78412e3a]xpub1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaLcgJvLJuZZvRcEL/1/*";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError("Error while parsing xkey."))
        );

        // ..or invalid raw keys
        let desc = "[78412e3a]0208a117f3897c3a13c9384b8695eed98dc31bc2500feb19a1af424cd47a5d83/1/*";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Public keys must be 64/66/130 characters in size"
            ))
        );

        // ..or invalid separators
        let desc = "[78412e3a]]03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Multiple \']\' in Descriptor Public Key"
            ))
        );

        // fuzzer errors
        let desc = "[11111f11]033333333333333333333333333333323333333333333333333333333433333333]]333]]3]]101333333333333433333]]]10]333333mmmm";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Multiple \']\' in Descriptor Public Key"
            ))
        );

        // fuzz failure, hybrid keys
        let desc = "0777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Only publickeys with prefixes 02/03/04 are allowed"
            ))
        );
    }

    #[test]
    fn parse_descriptor_secret_key_error() {
        // Xpubs are invalid
        let secret_key = "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL";
        assert_eq!(
            DescriptorSecretKey::from_str(secret_key),
            Err(DescriptorKeyParseError("Error while parsing xkey."))
        );

        // And ones with invalid fingerprints
        let desc = "[NonHexor]tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/1/*";
        assert_eq!(
            DescriptorSecretKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Malformed master fingerprint, expected 8 hex chars"
            ))
        );

        // ..or invalid raw keys
        let desc = "[78412e3a]L32jTfVLei6BYTPUpwpJSkrHx8iL9GZzeErVS8y4Y/1/*";
        assert_eq!(
            DescriptorSecretKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Error while parsing a WIF private key"
            ))
        );
    }

    #[test]
    fn test_wildcard() {
        let public_key = DescriptorPublicKey::from_str("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2").unwrap();
        assert_eq!(public_key.master_fingerprint().to_string(), "abcdef00");
        assert_eq!(public_key.full_derivation_path().to_string(), "m/0'/1'/2");
        assert_eq!(public_key.is_deriveable(), false);

        let public_key = DescriptorPublicKey::from_str("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/*").unwrap();
        assert_eq!(public_key.master_fingerprint().to_string(), "abcdef00");
        assert_eq!(public_key.full_derivation_path().to_string(), "m/0'/1'");
        assert_eq!(public_key.is_deriveable(), true);

        let public_key = DescriptorPublicKey::from_str("[abcdef00/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/*h").unwrap();
        assert_eq!(public_key.master_fingerprint().to_string(), "abcdef00");
        assert_eq!(public_key.full_derivation_path().to_string(), "m/0'/1'");
        assert_eq!(public_key.is_deriveable(), true);
    }

    #[test]
    fn test_deriv_on_xprv() {
        let secp = secp256k1::Secp256k1::signing_only();

        let secret_key = DescriptorSecretKey::from_str("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/0'/1'/2").unwrap();
        let public_key = secret_key.as_public(&secp).unwrap();
        assert_eq!(public_key.to_string(), "[2cbe2a6d/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2");
        assert_eq!(public_key.master_fingerprint().to_string(), "2cbe2a6d");
        assert_eq!(public_key.full_derivation_path().to_string(), "m/0'/1'/2");
        assert_eq!(public_key.is_deriveable(), false);

        let secret_key = DescriptorSecretKey::from_str("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/0'/1'/2'").unwrap();
        let public_key = secret_key.as_public(&secp).unwrap();
        assert_eq!(public_key.to_string(), "[2cbe2a6d/0'/1'/2']tpubDDPuH46rv4dbFtmF6FrEtJEy1CvLZonyBoVxF6xsesHdYDdTBrq2mHhm8AbsPh39sUwL2nZyxd6vo4uWNTU9v4t893CwxjqPnwMoUACLvMV");
        assert_eq!(public_key.master_fingerprint().to_string(), "2cbe2a6d");
        assert_eq!(public_key.full_derivation_path().to_string(), "m/0'/1'/2'");

        let secret_key = DescriptorSecretKey::from_str("tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/0/1/2").unwrap();
        let public_key = secret_key.as_public(&secp).unwrap();
        assert_eq!(public_key.to_string(), "tpubD6NzVbkrYhZ4WQdzxL7NmJN7b85ePo4p6RSj9QQHF7te2RR9iUeVSGgnGkoUsB9LBRosgvNbjRv9bcsJgzgBd7QKuxDm23ZewkTRzNSLEDr/0/1/2");
        assert_eq!(public_key.master_fingerprint().to_string(), "2cbe2a6d");
        assert_eq!(public_key.full_derivation_path().to_string(), "m/0/1/2");

        let secret_key = DescriptorSecretKey::from_str("[aabbccdd]tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/0/1/2").unwrap();
        let public_key = secret_key.as_public(&secp).unwrap();
        assert_eq!(public_key.to_string(), "[aabbccdd]tpubD6NzVbkrYhZ4WQdzxL7NmJN7b85ePo4p6RSj9QQHF7te2RR9iUeVSGgnGkoUsB9LBRosgvNbjRv9bcsJgzgBd7QKuxDm23ZewkTRzNSLEDr/0/1/2");
        assert_eq!(public_key.master_fingerprint().to_string(), "aabbccdd");
        assert_eq!(public_key.full_derivation_path().to_string(), "m/0/1/2");

        let secret_key = DescriptorSecretKey::from_str("[aabbccdd/90']tprv8ZgxMBicQKsPcwcD4gSnMti126ZiETsuX7qwrtMypr6FBwAP65puFn4v6c3jrN9VwtMRMph6nyT63NrfUL4C3nBzPcduzVSuHD7zbX2JKVc/0'/1'/2").unwrap();
        let public_key = secret_key.as_public(&secp).unwrap();
        assert_eq!(public_key.to_string(), "[aabbccdd/90'/0'/1']tpubDBrgjcxBxnXyL575sHdkpKohWu5qHKoQ7TJXKNrYznh5fVEGBv89hA8ENW7A8MFVpFUSvgLqc4Nj1WZcpePX6rrxviVtPowvMuGF5rdT2Vi/2");
        assert_eq!(public_key.master_fingerprint().to_string(), "aabbccdd");
        assert_eq!(
            public_key.full_derivation_path().to_string(),
            "m/90'/0'/1'/2"
        );
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
}
