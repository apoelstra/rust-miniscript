// Written in 2024 by Andrew Poelstra <apoelstra@wpsoftware.net>
// SPDX-License-Identifier: CC0-1.0

//! Public Keys
//!
//! This module contains traits that decsribe the various key capabilities
//! needed by Miniscript.
//!

use core::{fmt, hash};

use bitcoin::hashes::{hash160, ripemd160, sha256, Hash as _};

use crate::{hash256, SigType};

/// Public key trait which can be converted to Hash type
pub trait MiniscriptKey: Clone + Eq + Ord + fmt::Debug + fmt::Display + hash::Hash {
    /// Returns true if the pubkey is uncompressed. Defaults to `false`.
    fn is_uncompressed(&self) -> bool { false }

    /// Returns true if the pubkey is an x-only pubkey. Defaults to `false`.
    // This is required to know what in DescriptorPublicKey to know whether the inner
    // key in allowed in descriptor context
    fn is_x_only_key(&self) -> bool { false }

    /// Returns the number of different derivation paths in this key. Only >1 for keys
    /// in BIP389 multipath descriptors.
    fn num_der_paths(&self) -> usize { 0 }

    /// The associated [`bitcoin::hashes::sha256::Hash`] for this [`MiniscriptKey`], used in the
    /// sha256 fragment.
    type Sha256: Clone + Eq + Ord + fmt::Display + fmt::Debug + hash::Hash;

    /// The associated [`miniscript::hash256::Hash`] for this [`MiniscriptKey`], used in the
    /// hash256 fragment.
    type Hash256: Clone + Eq + Ord + fmt::Display + fmt::Debug + hash::Hash;

    /// The associated [`bitcoin::hashes::ripemd160::Hash`] for this [`MiniscriptKey`] type, used
    /// in the ripemd160 fragment.
    type Ripemd160: Clone + Eq + Ord + fmt::Display + fmt::Debug + hash::Hash;

    /// The associated [`bitcoin::hashes::hash160::Hash`] for this [`MiniscriptKey`] type, used in
    /// the hash160 fragment.
    type Hash160: Clone + Eq + Ord + fmt::Display + fmt::Debug + hash::Hash;
}

impl MiniscriptKey for bitcoin::secp256k1::PublicKey {
    type Sha256 = sha256::Hash;
    type Hash256 = hash256::Hash;
    type Ripemd160 = ripemd160::Hash;
    type Hash160 = hash160::Hash;
}

impl MiniscriptKey for bitcoin::PublicKey {
    /// Returns the compressed-ness of the underlying secp256k1 key.
    fn is_uncompressed(&self) -> bool { !self.compressed }

    type Sha256 = sha256::Hash;
    type Hash256 = hash256::Hash;
    type Ripemd160 = ripemd160::Hash;
    type Hash160 = hash160::Hash;
}

impl MiniscriptKey for bitcoin::secp256k1::XOnlyPublicKey {
    type Sha256 = sha256::Hash;
    type Hash256 = hash256::Hash;
    type Ripemd160 = ripemd160::Hash;
    type Hash160 = hash160::Hash;

    fn is_x_only_key(&self) -> bool { true }
}

impl MiniscriptKey for String {
    type Sha256 = String; // specify hashes as string
    type Hash256 = String;
    type Ripemd160 = String;
    type Hash160 = String;
}

/// Trait describing public key types which can be converted to bitcoin pubkeys
pub trait ToPublicKey: MiniscriptKey {
    /// Converts an object to a public key
    fn to_public_key(&self) -> bitcoin::PublicKey;

    /// Convert an object to x-only pubkey
    fn to_x_only_pubkey(&self) -> bitcoin::secp256k1::XOnlyPublicKey {
        let pk = self.to_public_key();
        bitcoin::secp256k1::XOnlyPublicKey::from(pk.inner)
    }

    /// Obtain the public key hash for this MiniscriptKey
    /// Expects an argument to specify the signature type.
    /// This would determine whether to serialize the key as 32 byte x-only pubkey
    /// or regular public key when computing the hash160
    fn to_pubkeyhash(&self, sig_type: SigType) -> hash160::Hash {
        match sig_type {
            SigType::Ecdsa => hash160::Hash::hash(&self.to_public_key().to_bytes()),
            SigType::Schnorr => hash160::Hash::hash(&self.to_x_only_pubkey().serialize()),
        }
    }

    /// Converts the generic associated [`MiniscriptKey::Sha256`] to [`sha256::Hash`]
    fn to_sha256(hash: &<Self as MiniscriptKey>::Sha256) -> sha256::Hash;

    /// Converts the generic associated [`MiniscriptKey::Hash256`] to [`hash256::Hash`]
    fn to_hash256(hash: &<Self as MiniscriptKey>::Hash256) -> hash256::Hash;

    /// Converts the generic associated [`MiniscriptKey::Ripemd160`] to [`ripemd160::Hash`]
    fn to_ripemd160(hash: &<Self as MiniscriptKey>::Ripemd160) -> ripemd160::Hash;

    /// Converts the generic associated [`MiniscriptKey::Hash160`] to [`hash160::Hash`]
    fn to_hash160(hash: &<Self as MiniscriptKey>::Hash160) -> hash160::Hash;
}

impl ToPublicKey for bitcoin::PublicKey {
    fn to_public_key(&self) -> bitcoin::PublicKey { *self }

    fn to_sha256(hash: &sha256::Hash) -> sha256::Hash { *hash }

    fn to_hash256(hash: &hash256::Hash) -> hash256::Hash { *hash }

    fn to_ripemd160(hash: &ripemd160::Hash) -> ripemd160::Hash { *hash }

    fn to_hash160(hash: &hash160::Hash) -> hash160::Hash { *hash }
}

impl ToPublicKey for bitcoin::secp256k1::PublicKey {
    fn to_public_key(&self) -> bitcoin::PublicKey { bitcoin::PublicKey::new(*self) }

    fn to_sha256(hash: &sha256::Hash) -> sha256::Hash { *hash }

    fn to_hash256(hash: &hash256::Hash) -> hash256::Hash { *hash }

    fn to_ripemd160(hash: &ripemd160::Hash) -> ripemd160::Hash { *hash }

    fn to_hash160(hash: &hash160::Hash) -> hash160::Hash { *hash }
}

impl ToPublicKey for bitcoin::secp256k1::XOnlyPublicKey {
    fn to_public_key(&self) -> bitcoin::PublicKey {
        // This code should never be used.
        // But is implemented for completeness
        let mut data: Vec<u8> = vec![0x02];
        data.extend(self.serialize().iter());
        bitcoin::PublicKey::from_slice(&data)
            .expect("Failed to construct 33 Publickey from 0x02 appended x-only key")
    }

    fn to_x_only_pubkey(&self) -> bitcoin::secp256k1::XOnlyPublicKey { *self }

    fn to_sha256(hash: &sha256::Hash) -> sha256::Hash { *hash }

    fn to_hash256(hash: &hash256::Hash) -> hash256::Hash { *hash }

    fn to_ripemd160(hash: &ripemd160::Hash) -> ripemd160::Hash { *hash }

    fn to_hash160(hash: &hash160::Hash) -> hash160::Hash { *hash }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::*;

    #[test]
    fn regression_bitcoin_key_hash() {
        use bitcoin::PublicKey;

        // Uncompressed key.
        let pk = PublicKey::from_str(
            "042e58afe51f9ed8ad3cc7897f634d881fdbe49a81564629ded8156bebd2ffd1af191923a2964c177f5b5923ae500fca49e99492d534aa3759d6b25a8bc971b133"
        ).unwrap();

        let want = hash160::Hash::from_str("ac2e7daf42d2c97418fd9f78af2de552bb9c6a7a").unwrap();
        let got = pk.to_pubkeyhash(SigType::Ecdsa);
        assert_eq!(got, want)
    }

    #[test]
    fn regression_secp256k1_key_hash() {
        use bitcoin::secp256k1::PublicKey;

        // Compressed key.
        let pk = PublicKey::from_str(
            "032e58afe51f9ed8ad3cc7897f634d881fdbe49a81564629ded8156bebd2ffd1af",
        )
        .unwrap();

        let want = hash160::Hash::from_str("9511aa27ef39bbfa4e4f3dd15f4d66ea57f475b4").unwrap();
        let got = pk.to_pubkeyhash(SigType::Ecdsa);
        assert_eq!(got, want)
    }

    #[test]
    fn regression_xonly_key_hash() {
        use bitcoin::secp256k1::XOnlyPublicKey;

        let pk = XOnlyPublicKey::from_str(
            "cc8a4bc64d897bddc5fbc2f670f7a8ba0b386779106cf1223c6fc5d7cd6fc115",
        )
        .unwrap();

        let want = hash160::Hash::from_str("eb8ac65f971ae688a94aeabf223506865e7e08f2").unwrap();
        let got = pk.to_pubkeyhash(SigType::Schnorr);
        assert_eq!(got, want)
    }
}
