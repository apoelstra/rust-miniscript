// SPDX-License-Identifier: CC0-1.0

use core::convert::TryFrom;

use bitcoin::constants::MAX_SCRIPT_ELEMENT_SIZE;
use bitcoin::hashes::Hash;
use bitcoin::script::{self, PushBytes, ScriptBuf};
use bitcoin::PubkeyHash;

use crate::miniscript::context;
use crate::miniscript::satisfy::Placeholder;
use crate::prelude::*;
use crate::{MiniscriptKey, ScriptContext, ToPublicKey};
pub(crate) fn varint_len(n: usize) -> usize { bitcoin::VarInt(n as u64).size() }

pub(crate) trait ItemSize {
    fn size(&self) -> usize;
}

impl<Pk: MiniscriptKey> ItemSize for Placeholder<Pk> {
    fn size(&self) -> usize {
        match self {
            Self::Pubkey(_, size) => *size,
            Self::PubkeyHash(_, size) => *size,
            Self::EcdsaSigPk(_) | Self::EcdsaSigPkHash(_) => 73,
            Self::SchnorrSigPk(_, _, size) | Self::SchnorrSigPkHash(_, _, size) => size + 1, // +1 for the OP_PUSH
            Self::HashDissatisfaction
            | Self::Sha256Preimage(_)
            | Self::Hash256Preimage(_)
            | Self::Ripemd160Preimage(_)
            | Self::Hash160Preimage(_) => 33,
            Self::PushOne => 2, // On legacy this should be 1 ?
            Self::PushZero => 1,
            Self::TapScript(s) => s.len() + varint_len(s.len()),
            Self::TapControlBlock(cb) => {
                let block_len = cb.serialize().len();
                block_len + varint_len(block_len)
            }
        }
    }
}

impl ItemSize for Vec<u8> {
    fn size(&self) -> usize { self.len() }
}

// Helper function to calculate witness size
pub(crate) fn witness_size<T: ItemSize>(wit: &[T]) -> usize {
    wit.iter().map(T::size).sum::<usize>() + varint_len(wit.len())
}

pub(crate) fn witness_to_scriptsig(witness: &[Vec<u8>]) -> ScriptBuf {
    let mut b = script::Builder::new();
    for (i, wit) in witness.iter().enumerate() {
        if let Ok(n) = script::read_scriptint(wit) {
            b = b.push_int(n);
        } else {
            if i != witness.len() - 1 {
                assert!(wit.len() < 73, "All pushes in miniscript are < 73 bytes");
            } else {
                assert!(wit.len() <= MAX_SCRIPT_ELEMENT_SIZE, "P2SH redeem script is <= 520 bytes");
            }
            let push = <&PushBytes>::try_from(wit.as_slice()).expect("checked above");
            b = b.push_slice(push)
        }
    }
    b.into_script()
}

// trait for pushing key that depend on context
pub(crate) trait MsKeyBuilder {
    /// Serialize the key as bytes based on script context. Used when encoding miniscript into bitcoin script
    fn push_ms_key<Pk, Ctx>(self, key: &Pk) -> Self
    where
        Pk: ToPublicKey,
        Ctx: ScriptContext;

    /// Serialize the key hash as bytes based on script context. Used when encoding miniscript into bitcoin script
    fn push_ms_key_hash<Pk, Ctx>(self, key: &Pk) -> Self
    where
        Pk: ToPublicKey,
        Ctx: ScriptContext;
}

impl MsKeyBuilder for script::Builder {
    fn push_ms_key<Pk, Ctx>(self, key: &Pk) -> Self
    where
        Pk: ToPublicKey,
        Ctx: ScriptContext,
    {
        match Ctx::sig_type() {
            context::SigType::Ecdsa => self.push_key(&key.to_public_key()),
            context::SigType::Schnorr => self.push_slice(key.to_x_only_pubkey().serialize()),
        }
    }

    fn push_ms_key_hash<Pk, Ctx>(self, key: &Pk) -> Self
    where
        Pk: ToPublicKey,
        Ctx: ScriptContext,
    {
        match Ctx::sig_type() {
            context::SigType::Ecdsa => self.push_slice(key.to_public_key().pubkey_hash()),
            context::SigType::Schnorr => {
                self.push_slice(PubkeyHash::hash(&key.to_x_only_pubkey().serialize()))
            }
        }
    }
}
