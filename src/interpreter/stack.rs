// Miniscript
// Written in 2020 by
//     Sanket Kanjular and Andrew Poelstra
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

//! Interpreter stack

use bitcoin;
use bitcoin::blockdata::{opcodes, script};
use bitcoin::hashes::{hash160, ripemd160, sha256, sha256d, Hash};

use super::error::PkEvalErrInner;
use super::{
    verify_sersig, BitcoinKey, Error, HashLockType, KeySigPair, SatisfiedConstraint, TaggedHash160,
};

/// Definition of Stack Element of the Stack used for interpretation of Miniscript.
/// All stack elements with vec![] go to Dissatisfied and vec![1] are marked to Satisfied.
/// Others are directly pushed as witness
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Element<'txin> {
    /// Result of a satisfied Miniscript fragment
    /// Translated from `vec![1]` from input stack
    Satisfied,
    /// Result of a dissatisfied Miniscript fragment
    /// Translated from `vec![]` from input stack
    Dissatisfied,
    /// Input from the witness stack
    Push(&'txin [u8]),
}

impl<'txin> From<&'txin Vec<u8>> for Element<'txin> {
    fn from(v: &'txin Vec<u8>) -> Element<'txin> {
        From::from(&v[..])
    }
}

impl<'txin> From<&'txin [u8]> for Element<'txin> {
    fn from(v: &'txin [u8]) -> Element<'txin> {
        if *v == [1] {
            Element::Satisfied
        } else if v.is_empty() {
            Element::Dissatisfied
        } else {
            Element::Push(v)
        }
    }
}

impl<'txin> Element<'txin> {
    /// Converts a Bitcoin `script::Instruction` to a stack element
    ///
    /// Supports `OP_1` but no other numbers since these are not used by Miniscript
    pub fn from_instruction(
        ins: Result<script::Instruction<'txin>, bitcoin::blockdata::script::Error>,
    ) -> Result<Self, Error> {
        match ins {
            //Also covers the dissatisfied case as PushBytes0
            Ok(script::Instruction::PushBytes(v)) => Ok(Element::from(v)),
            Ok(script::Instruction::Op(opcodes::all::OP_PUSHNUM_1)) => Ok(Element::Satisfied),
            _ => Err(Error::ExpectedPush),
        }
    }
}

/// Stack Data structure representing the stack input to Miniscript. This Stack
/// is created from the combination of ScriptSig and Witness stack.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Stack<'txin>(Vec<Element<'txin>>);

impl<'txin> From<Vec<Element<'txin>>> for Stack<'txin> {
    fn from(v: Vec<Element<'txin>>) -> Self {
        Stack(v)
    }
}

impl<'txin> Default for Stack<'txin> {
    fn default() -> Self {
        Stack(vec![])
    }
}

impl<'txin> Stack<'txin> {
    /// Whether the stack is empty
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Number of elements on the stack
    pub fn len(&mut self) -> usize {
        self.0.len()
    }

    /// Removes the top stack element, if the stack is nonempty
    pub fn pop(&mut self) -> Option<Element<'txin>> {
        self.0.pop()
    }

    /// Pushes an element onto the top of the stack
    pub fn push(&mut self, elem: Element<'txin>) -> () {
        self.0.push(elem);
    }

    /// Returns a new stack representing the top `k` elements of the stack,
    /// removing these elements from the original
    pub fn split_off(&mut self, k: usize) -> Vec<Element<'txin>> {
        self.0.split_off(k)
    }

    /// Returns a reference to the top stack element, if the stack is nonempty
    pub fn last(&self) -> Option<&Element<'txin>> {
        self.0.last()
    }

    /// Helper function to evaluate a Pk Node which takes the
    /// top of the stack as input signature and validates it.
    /// Sat: If the signature witness is correct, 1 is pushed
    /// Unsat: For empty witness a 0 is pushed
    /// Err: All of other witness result in errors.
    /// `pk` CHECKSIG
    pub(super) fn evaluate_pk<'intp>(
        &mut self,
        verify_sig: &mut Box<dyn FnMut(&KeySigPair) -> bool + 'intp>,
        pk: &'intp BitcoinKey,
    ) -> Option<Result<SatisfiedConstraint, Error>> {
        if let Some(sigser) = self.pop() {
            match sigser {
                Element::Dissatisfied => {
                    self.push(Element::Dissatisfied);
                    None
                }
                Element::Push(sigser) => {
                    let key_sig = verify_sersig(verify_sig, pk, sigser);
                    match key_sig {
                        Ok(key_sig) => {
                            self.push(Element::Satisfied);
                            Some(Ok(SatisfiedConstraint::PublicKey { key_sig }))
                        }
                        Err(e) => return Some(Err(e)),
                    }
                }
                Element::Satisfied => {
                    return Some(Err(Error::PkEvaluationError(PkEvalErrInner::from(*pk))));
                }
            }
        } else {
            Some(Err(Error::UnexpectedStackEnd))
        }
    }

    /// Helper function to evaluate a Pkh Node. Takes input as pubkey and sig
    /// from the top of the stack and outputs Sat if the pubkey, sig is valid
    /// Sat: If the pubkey hash matches and signature witness is correct,
    /// Unsat: For an empty witness
    /// Err: All of other witness result in errors.
    /// `DUP HASH160 <keyhash> EQUALVERIY CHECKSIG`
    pub(super) fn evaluate_pkh<'intp>(
        &mut self,
        verify_sig: &mut Box<dyn FnMut(&KeySigPair) -> bool + 'intp>,
        pkh: &'intp TaggedHash160,
    ) -> Option<Result<SatisfiedConstraint, Error>> {
        // Parse a bitcoin key from witness data slice depending on hash context
        // when we encounter a pkh(hash)
        // Depending on the tag of hash, we parse the as full key or x-only-key
        // TODO: All keys parse errors are currently captured in a single BadPubErr
        // We don't really store information about which key error.
        fn bitcoin_key_from_slice(sl: &[u8], tag: TaggedHash160) -> Option<BitcoinKey> {
            let key: BitcoinKey = match tag {
                TaggedHash160::XonlyKey(_) => bitcoin::XOnlyPublicKey::from_slice(sl).ok()?.into(),
                TaggedHash160::FullKey(_) => bitcoin::PublicKey::from_slice(sl).ok()?.into(),
            };
            Some(key)
        }
        if let Some(Element::Push(pk)) = self.pop() {
            let pk_hash = hash160::Hash::hash(pk);
            if pk_hash != pkh.hash160() {
                return Some(Err(Error::PkHashVerifyFail(pkh.hash160())));
            }
            match bitcoin_key_from_slice(pk, *pkh) {
                Some(pk) => {
                    if let Some(sigser) = self.pop() {
                        match sigser {
                            Element::Dissatisfied => {
                                self.push(Element::Dissatisfied);
                                None
                            }
                            Element::Push(sigser) => {
                                let key_sig = verify_sersig(verify_sig, &pk, sigser);
                                match key_sig {
                                    Ok(key_sig) => {
                                        self.push(Element::Satisfied);
                                        Some(Ok(SatisfiedConstraint::PublicKeyHash {
                                            keyhash: pkh.hash160(),
                                            key_sig: key_sig,
                                        }))
                                    }
                                    Err(e) => return Some(Err(e)),
                                }
                            }
                            Element::Satisfied => {
                                return Some(Err(Error::PkEvaluationError(pk.into())))
                            }
                        }
                    } else {
                        Some(Err(Error::UnexpectedStackEnd))
                    }
                }
                None => Some(Err(Error::PubkeyParseError)),
            }
        } else {
            Some(Err(Error::UnexpectedStackEnd))
        }
    }

    /// Helper function to evaluate a After Node. Takes no argument from stack
    /// `n CHECKLOCKTIMEVERIFY 0NOTEQUAL` and `n CHECKLOCKTIMEVERIFY`
    /// Ideally this should return int value as n: build_scriptint(t as i64)),
    /// The reason we don't need to copy the Script semantics is that
    /// Miniscript never evaluates integers and it is safe to treat them as
    /// booleans
    pub(super) fn evaluate_after<'intp>(
        &mut self,
        n: &'intp u32,
        age: u32,
    ) -> Option<Result<SatisfiedConstraint, Error>> {
        if age >= *n {
            self.push(Element::Satisfied);
            Some(Ok(SatisfiedConstraint::AbsoluteTimeLock { time: *n }))
        } else {
            Some(Err(Error::AbsoluteLocktimeNotMet(*n)))
        }
    }

    /// Helper function to evaluate a Older Node. Takes no argument from stack
    /// `n CHECKSEQUENCEVERIFY 0NOTEQUAL` and `n CHECKSEQUENCEVERIFY`
    /// Ideally this should return int value as n: build_scriptint(t as i64)),
    /// The reason we don't need to copy the Script semantics is that
    /// Miniscript never evaluates integers and it is safe to treat them as
    /// booleans
    pub(super) fn evaluate_older<'intp>(
        &mut self,
        n: &'intp u32,
        height: u32,
    ) -> Option<Result<SatisfiedConstraint, Error>> {
        if height >= *n {
            self.push(Element::Satisfied);
            Some(Ok(SatisfiedConstraint::RelativeTimeLock { time: *n }))
        } else {
            Some(Err(Error::RelativeLocktimeNotMet(*n)))
        }
    }

    /// Helper function to evaluate a Sha256 Node.
    /// `SIZE 32 EQUALVERIFY SHA256 h EQUAL`
    pub(super) fn evaluate_sha256<'intp>(
        &mut self,
        hash: &'intp sha256::Hash,
    ) -> Option<Result<SatisfiedConstraint, Error>> {
        if let Some(Element::Push(preimage)) = self.pop() {
            if preimage.len() != 32 {
                return Some(Err(Error::HashPreimageLengthMismatch));
            }
            if sha256::Hash::hash(preimage) == *hash {
                self.push(Element::Satisfied);
                Some(Ok(SatisfiedConstraint::HashLock {
                    hash: HashLockType::Sha256(*hash),
                    preimage: preimage_from_sl(preimage),
                }))
            } else {
                self.push(Element::Dissatisfied);
                None
            }
        } else {
            Some(Err(Error::UnexpectedStackEnd))
        }
    }

    /// Helper function to evaluate a Hash256 Node.
    /// `SIZE 32 EQUALVERIFY HASH256 h EQUAL`
    pub(super) fn evaluate_hash256<'intp>(
        &mut self,
        hash: &'intp sha256d::Hash,
    ) -> Option<Result<SatisfiedConstraint, Error>> {
        if let Some(Element::Push(preimage)) = self.pop() {
            if preimage.len() != 32 {
                return Some(Err(Error::HashPreimageLengthMismatch));
            }
            if sha256d::Hash::hash(preimage) == *hash {
                self.push(Element::Satisfied);
                Some(Ok(SatisfiedConstraint::HashLock {
                    hash: HashLockType::Hash256(*hash),
                    preimage: preimage_from_sl(preimage),
                }))
            } else {
                self.push(Element::Dissatisfied);
                None
            }
        } else {
            Some(Err(Error::UnexpectedStackEnd))
        }
    }

    /// Helper function to evaluate a Hash160 Node.
    /// `SIZE 32 EQUALVERIFY HASH160 h EQUAL`
    pub(super) fn evaluate_hash160<'intp>(
        &mut self,
        hash: &'intp hash160::Hash,
    ) -> Option<Result<SatisfiedConstraint, Error>> {
        if let Some(Element::Push(preimage)) = self.pop() {
            if preimage.len() != 32 {
                return Some(Err(Error::HashPreimageLengthMismatch));
            }
            if hash160::Hash::hash(preimage) == *hash {
                self.push(Element::Satisfied);
                Some(Ok(SatisfiedConstraint::HashLock {
                    hash: HashLockType::Hash160(*hash),
                    preimage: preimage_from_sl(preimage),
                }))
            } else {
                self.push(Element::Dissatisfied);
                None
            }
        } else {
            Some(Err(Error::UnexpectedStackEnd))
        }
    }

    /// Helper function to evaluate a RipeMd160 Node.
    /// `SIZE 32 EQUALVERIFY RIPEMD160 h EQUAL`
    pub(super) fn evaluate_ripemd160<'intp>(
        &mut self,
        hash: &'intp ripemd160::Hash,
    ) -> Option<Result<SatisfiedConstraint, Error>> {
        if let Some(Element::Push(preimage)) = self.pop() {
            if preimage.len() != 32 {
                return Some(Err(Error::HashPreimageLengthMismatch));
            }
            if ripemd160::Hash::hash(preimage) == *hash {
                self.push(Element::Satisfied);
                Some(Ok(SatisfiedConstraint::HashLock {
                    hash: HashLockType::Ripemd160(*hash),
                    preimage: preimage_from_sl(preimage),
                }))
            } else {
                self.push(Element::Dissatisfied);
                None
            }
        } else {
            Some(Err(Error::UnexpectedStackEnd))
        }
    }

    /// Helper function to evaluate a checkmultisig which takes the top of the
    /// stack as input signatures and validates it in order of pubkeys.
    /// For example, if the first signature is satisfied by second public key,
    /// other signatures are not checked against the first pubkey.
    /// `multi(2,pk1,pk2)` would be satisfied by `[0 sig2 sig1]` and Err on
    /// `[0 sig2 sig1]`
    pub(super) fn evaluate_multi<'intp>(
        &mut self,
        verify_sig: &mut Box<dyn FnMut(&KeySigPair) -> bool + 'intp>,
        pk: &'intp BitcoinKey,
    ) -> Option<Result<SatisfiedConstraint, Error>> {
        if let Some(witness_sig) = self.pop() {
            if let Element::Push(sigser) = witness_sig {
                let key_sig = verify_sersig(verify_sig, pk, sigser);
                match key_sig {
                    Ok(key_sig) => return Some(Ok(SatisfiedConstraint::PublicKey { key_sig })),
                    Err(..) => {
                        self.push(witness_sig);
                        return None;
                    }
                }
            } else {
                Some(Err(Error::UnexpectedStackBoolean))
            }
        } else {
            Some(Err(Error::UnexpectedStackEnd))
        }
    }
}

// Helper function to compute preimage from slice
fn preimage_from_sl(sl: &[u8]) -> [u8; 32] {
    if sl.len() != 32 {
        unreachable!("Internal: Preimage length checked to be 32")
    } else {
        let mut preimage = [0u8; 32];
        preimage.copy_from_slice(sl);
        preimage
    }
}
