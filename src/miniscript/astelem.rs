// SPDX-License-Identifier: CC0-1.0

//! AST Elements
//!
//! Datatype describing a Miniscript "script fragment", which are the
//! building blocks of all Miniscripts. Each fragment has a unique
//! encoding in Bitcoin script, as well as a datatype. Full details
//! are given on the Miniscript website.

use bitcoin::hashes::Hash;
use bitcoin::{absolute, opcodes, script};
use sync::Arc;

use crate::miniscript::context::SigType;
use crate::miniscript::ScriptContext;
use crate::prelude::*;
use crate::util::MsKeyBuilder;
use crate::{expression, Error, FromStrKey, Miniscript, MiniscriptKey, Terminal, ToPublicKey};

impl<Pk: FromStrKey, Ctx: ScriptContext> crate::expression::FromTree for Arc<Terminal<Pk, Ctx>> {
    fn from_tree(top: &expression::Tree) -> Result<Arc<Terminal<Pk, Ctx>>, Error> {
        Ok(Arc::new(expression::FromTree::from_tree(top)?))
    }
}

impl<Pk: FromStrKey, Ctx: ScriptContext> crate::expression::FromTree for Terminal<Pk, Ctx> {
    fn from_tree(top: &expression::Tree) -> Result<Terminal<Pk, Ctx>, Error> {
        let binary =
            |node: &expression::Tree, name, termfn: fn(_, _) -> Self| -> Result<Self, Error> {
                node.verify_binary(name)
                    .map_err(From::from)
                    .map_err(Error::Parse)
                    .and_then(|(x, y)| {
                        let x = Arc::<Miniscript<Pk, Ctx>>::from_tree(x)?;
                        let y = Arc::<Miniscript<Pk, Ctx>>::from_tree(y)?;
                        Ok(termfn(x, y))
                    })
            };

        let (frag_wrap, frag_name) = top
            .name_separated(':')
            .map_err(From::from)
            .map_err(Error::Parse)?;
        // "pk" and "pkh" are aliases for "c:pk_k" and "c:pk_h" respectively.
        let unwrapped = match frag_name {
            "expr_raw_pkh" => top
                .verify_terminal_parent("expr_raw_pkh", "public key hash")
                .map(Terminal::RawPkH)
                .map_err(Error::Parse),
            "pk" => top
                .verify_terminal_parent("pk", "public key")
                .map(Terminal::PkK)
                .map_err(Error::Parse)
                .and_then(|term| Miniscript::from_ast(term))
                .map(|ms| Terminal::Check(Arc::new(ms))),
            "pkh" => top
                .verify_terminal_parent("pkh", "public key")
                .map(Terminal::PkH)
                .map_err(Error::Parse)
                .and_then(|term| Miniscript::from_ast(term))
                .map(|ms| Terminal::Check(Arc::new(ms))),
            "pk_k" => top
                .verify_terminal_parent("pk_k", "public key")
                .map(Terminal::PkK)
                .map_err(Error::Parse),
            "pk_h" => top
                .verify_terminal_parent("pk_h", "public key")
                .map(Terminal::PkH)
                .map_err(Error::Parse),
            "after" => top
                .verify_after()
                .map_err(Error::Parse)
                .map(Terminal::After),
            "older" => top
                .verify_older()
                .map_err(Error::Parse)
                .map(Terminal::Older),
            "sha256" => top
                .verify_terminal_parent("sha256", "hash")
                .map(Terminal::Sha256)
                .map_err(Error::Parse),
            "hash256" => top
                .verify_terminal_parent("hash256", "hash")
                .map(Terminal::Hash256)
                .map_err(Error::Parse),
            "ripemd160" => top
                .verify_terminal_parent("ripemd160", "hash")
                .map(Terminal::Ripemd160)
                .map_err(Error::Parse),
            "hash160" => top
                .verify_terminal_parent("hash160", "hash")
                .map(Terminal::Hash160)
                .map_err(Error::Parse),
            "1" => {
                top.verify_n_children("1", 0..=0)
                    .map_err(From::from)
                    .map_err(Error::Parse)?;
                Ok(Terminal::True)
            }
            "0" => {
                top.verify_n_children("0", 0..=0)
                    .map_err(From::from)
                    .map_err(Error::Parse)?;
                Ok(Terminal::False)
            }
            "and_v" => binary(top, "and_v", Terminal::AndV),
            "and_b" => binary(top, "and_b", Terminal::AndB),
            "and_n" => {
                binary(top, "and_n", |x, y| Terminal::AndOr(x, y, Arc::new(Miniscript::FALSE)))
            }
            "andor" => {
                top.verify_n_children("andor", 3..=3)
                    .map_err(From::from)
                    .map_err(Error::Parse)?;
                let x = Arc::<Miniscript<Pk, Ctx>>::from_tree(&top.args[0])?;
                let y = Arc::<Miniscript<Pk, Ctx>>::from_tree(&top.args[1])?;
                let z = Arc::<Miniscript<Pk, Ctx>>::from_tree(&top.args[2])?;
                Ok(Terminal::AndOr(x, y, z))
            }
            "or_b" => binary(top, "or_b", Terminal::OrB),
            "or_d" => binary(top, "or_d", Terminal::OrD),
            "or_c" => binary(top, "or_c", Terminal::OrC),
            "or_i" => binary(top, "or_i", Terminal::OrI),
            "thresh" => top
                .verify_threshold(|sub| Miniscript::from_tree(sub).map(Arc::new))
                .map(Terminal::Thresh),
            "multi" => top
                .verify_threshold(|sub| sub.verify_terminal("public_key").map_err(Error::Parse))
                .map(Terminal::Multi),
            "multi_a" => top
                .verify_threshold(|sub| sub.verify_terminal("public_key").map_err(Error::Parse))
                .map(Terminal::MultiA),
            x => Err(Error::Parse(crate::ParseError::Tree(crate::ParseTreeError::UnknownName {
                name: x.to_owned(),
            }))),
        }?;

        if frag_wrap == Some("") {
            return Err(Error::Parse(crate::ParseError::Tree(
                crate::ParseTreeError::UnknownName { name: top.name.to_owned() },
            )));
        }
        let ms = super::wrap_into_miniscript(unwrapped, frag_wrap.unwrap_or(""))?;
        Ok(ms.node)
    }
}

/// Helper trait to add a `push_astelem` method to `script::Builder`
trait PushAstElem<Pk: MiniscriptKey, Ctx: ScriptContext> {
    fn push_astelem(self, ast: &Miniscript<Pk, Ctx>) -> Self
    where
        Pk: ToPublicKey;
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> PushAstElem<Pk, Ctx> for script::Builder {
    fn push_astelem(self, ast: &Miniscript<Pk, Ctx>) -> Self
    where
        Pk: ToPublicKey,
    {
        ast.node.encode(self)
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Terminal<Pk, Ctx> {
    /// Encode the element as a fragment of Bitcoin Script. The inverse
    /// function, from Script to an AST element, is implemented in the
    /// `parse` module.
    pub fn encode(&self, mut builder: script::Builder) -> script::Builder
    where
        Pk: ToPublicKey,
    {
        match *self {
            Terminal::PkK(ref pk) => builder.push_ms_key::<_, Ctx>(pk),
            Terminal::PkH(ref pk) => builder
                .push_opcode(opcodes::all::OP_DUP)
                .push_opcode(opcodes::all::OP_HASH160)
                .push_ms_key_hash::<_, Ctx>(pk)
                .push_opcode(opcodes::all::OP_EQUALVERIFY),
            Terminal::RawPkH(ref hash) => builder
                .push_opcode(opcodes::all::OP_DUP)
                .push_opcode(opcodes::all::OP_HASH160)
                .push_slice(hash.to_byte_array())
                .push_opcode(opcodes::all::OP_EQUALVERIFY),
            Terminal::After(t) => builder
                .push_int(absolute::LockTime::from(t).to_consensus_u32() as i64)
                .push_opcode(opcodes::all::OP_CLTV),
            Terminal::Older(t) => builder
                .push_int(t.to_consensus_u32().into())
                .push_opcode(opcodes::all::OP_CSV),
            Terminal::Sha256(ref h) => builder
                .push_opcode(opcodes::all::OP_SIZE)
                .push_int(32)
                .push_opcode(opcodes::all::OP_EQUALVERIFY)
                .push_opcode(opcodes::all::OP_SHA256)
                .push_slice(Pk::to_sha256(h).to_byte_array())
                .push_opcode(opcodes::all::OP_EQUAL),
            Terminal::Hash256(ref h) => builder
                .push_opcode(opcodes::all::OP_SIZE)
                .push_int(32)
                .push_opcode(opcodes::all::OP_EQUALVERIFY)
                .push_opcode(opcodes::all::OP_HASH256)
                .push_slice(Pk::to_hash256(h).to_byte_array())
                .push_opcode(opcodes::all::OP_EQUAL),
            Terminal::Ripemd160(ref h) => builder
                .push_opcode(opcodes::all::OP_SIZE)
                .push_int(32)
                .push_opcode(opcodes::all::OP_EQUALVERIFY)
                .push_opcode(opcodes::all::OP_RIPEMD160)
                .push_slice(Pk::to_ripemd160(h).to_byte_array())
                .push_opcode(opcodes::all::OP_EQUAL),
            Terminal::Hash160(ref h) => builder
                .push_opcode(opcodes::all::OP_SIZE)
                .push_int(32)
                .push_opcode(opcodes::all::OP_EQUALVERIFY)
                .push_opcode(opcodes::all::OP_HASH160)
                .push_slice(Pk::to_hash160(h).to_byte_array())
                .push_opcode(opcodes::all::OP_EQUAL),
            Terminal::True => builder.push_opcode(opcodes::OP_TRUE),
            Terminal::False => builder.push_opcode(opcodes::OP_FALSE),
            Terminal::Alt(ref sub) => builder
                .push_opcode(opcodes::all::OP_TOALTSTACK)
                .push_astelem(sub)
                .push_opcode(opcodes::all::OP_FROMALTSTACK),
            Terminal::Swap(ref sub) => builder.push_opcode(opcodes::all::OP_SWAP).push_astelem(sub),
            Terminal::Check(ref sub) => builder
                .push_astelem(sub)
                .push_opcode(opcodes::all::OP_CHECKSIG),
            Terminal::DupIf(ref sub) => builder
                .push_opcode(opcodes::all::OP_DUP)
                .push_opcode(opcodes::all::OP_IF)
                .push_astelem(sub)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::Verify(ref sub) => builder.push_astelem(sub).push_verify(),
            Terminal::NonZero(ref sub) => builder
                .push_opcode(opcodes::all::OP_SIZE)
                .push_opcode(opcodes::all::OP_0NOTEQUAL)
                .push_opcode(opcodes::all::OP_IF)
                .push_astelem(sub)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::ZeroNotEqual(ref sub) => builder
                .push_astelem(sub)
                .push_opcode(opcodes::all::OP_0NOTEQUAL),
            Terminal::AndV(ref left, ref right) => builder.push_astelem(left).push_astelem(right),
            Terminal::AndB(ref left, ref right) => builder
                .push_astelem(left)
                .push_astelem(right)
                .push_opcode(opcodes::all::OP_BOOLAND),
            Terminal::AndOr(ref a, ref b, ref c) => builder
                .push_astelem(a)
                .push_opcode(opcodes::all::OP_NOTIF)
                .push_astelem(c)
                .push_opcode(opcodes::all::OP_ELSE)
                .push_astelem(b)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::OrB(ref left, ref right) => builder
                .push_astelem(left)
                .push_astelem(right)
                .push_opcode(opcodes::all::OP_BOOLOR),
            Terminal::OrD(ref left, ref right) => builder
                .push_astelem(left)
                .push_opcode(opcodes::all::OP_IFDUP)
                .push_opcode(opcodes::all::OP_NOTIF)
                .push_astelem(right)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::OrC(ref left, ref right) => builder
                .push_astelem(left)
                .push_opcode(opcodes::all::OP_NOTIF)
                .push_astelem(right)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::OrI(ref left, ref right) => builder
                .push_opcode(opcodes::all::OP_IF)
                .push_astelem(left)
                .push_opcode(opcodes::all::OP_ELSE)
                .push_astelem(right)
                .push_opcode(opcodes::all::OP_ENDIF),
            Terminal::Thresh(ref thresh) => {
                builder = builder.push_astelem(&thresh.data()[0]);
                for sub in &thresh.data()[1..] {
                    builder = builder.push_astelem(sub).push_opcode(opcodes::all::OP_ADD);
                }
                builder
                    .push_int(thresh.k() as i64)
                    .push_opcode(opcodes::all::OP_EQUAL)
            }
            Terminal::Multi(ref thresh) => {
                debug_assert!(Ctx::sig_type() == SigType::Ecdsa);
                builder = builder.push_int(thresh.k() as i64);
                for pk in thresh.data() {
                    builder = builder.push_key(&pk.to_public_key());
                }
                builder
                    .push_int(thresh.n() as i64)
                    .push_opcode(opcodes::all::OP_CHECKMULTISIG)
            }
            Terminal::MultiA(ref thresh) => {
                debug_assert!(Ctx::sig_type() == SigType::Schnorr);
                // keys must be atleast len 1 here, guaranteed by typing rules
                builder = builder.push_ms_key::<_, Ctx>(&thresh.data()[0]);
                builder = builder.push_opcode(opcodes::all::OP_CHECKSIG);
                for pk in thresh.iter().skip(1) {
                    builder = builder.push_ms_key::<_, Ctx>(pk);
                    builder = builder.push_opcode(opcodes::all::OP_CHECKSIGADD);
                }
                builder
                    .push_int(thresh.k() as i64)
                    .push_opcode(opcodes::all::OP_NUMEQUAL)
            }
        }
    }
}
