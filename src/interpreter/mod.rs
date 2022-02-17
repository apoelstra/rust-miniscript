// Miniscript
// Written in 2019 by
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

//! Interpreter
//!
//! Provides a Miniscript-based script interpreter which can be used to
//! iterate over the set of conditions satisfied by a spending transaction,
//! assuming that the spent coin was descriptor controlled.
//!

use bitcoin::blockdata::witness::Witness;
use bitcoin::hashes::{hash160, ripemd160, sha256, sha256d};
use bitcoin::util::sighash;
use bitcoin::{self, secp256k1};
use miniscript::context::NoChecksEcdsa;
use miniscript::ScriptContext;
use Miniscript;
use Terminal;
use {Descriptor, ToPublicKey};

mod error;
mod inner;
mod stack;

pub use self::error::Error;
use self::stack::Stack;

/// An iterable Miniscript-structured representation of the spending of a coin
pub struct Interpreter<'txin> {
    inner: inner::Inner,
    stack: Stack<'txin>,
    script_code: bitcoin::Script,
    age: u32,
    height: u32,
}

impl<'txin> Interpreter<'txin> {
    /// Constructs an interpreter from the data of a spending transaction
    ///
    /// Accepts a signature-validating function. If you are willing to trust
    /// that ECSDA signatures are valid, this can be set to the constant true
    /// function; otherwise, it should be a closure containing a sighash and
    /// secp context, which can actually verify a given signature.
    pub fn from_txdata(
        spk: &bitcoin::Script,
        script_sig: &'txin bitcoin::Script,
        witness: &'txin Witness,
        age: u32,
        height: u32,
    ) -> Result<Self, Error> {
        let (inner, stack, script_code) = inner::from_txdata(spk, script_sig, witness)?;
        Ok(Interpreter {
            inner,
            stack,
            script_code,
            age,
            height,
        })
    }

    /// Creates an iterator over the satisfied spending conditions
    ///
    /// Returns all satisfied constraints, even if they were redundant (i.e. did
    /// not contribute to the script being satisfied). For example, if a signature
    /// were provided for an `and_b(Pk,false)` fragment, that signature will be
    /// returned, even though the entire and_b must have failed and must not have
    /// been used.
    ///
    /// In case the script is actually dissatisfied, this may return several values
    /// before ultimately returning an error.
    ///
    /// Running the iterator through will consume the internal stack of the
    /// `Iterpreter`, and it should not be used again after this.
    pub fn iter<'iter, F: FnMut(&bitcoin::PublicKey, bitcoin::EcdsaSig) -> bool>(
        &'iter mut self,
        verify_sig: F,
    ) -> Iter<'txin, 'iter, F> {
        Iter {
            verify_sig: verify_sig,
            public_key: if let inner::Inner::PublicKey(ref pk, _) = self.inner {
                Some(pk)
            } else {
                None
            },
            state: if let inner::Inner::Script(ref script, _) = self.inner {
                vec![NodeEvaluationState {
                    node: script,
                    n_evaluated: 0,
                    n_satisfied: 0,
                }]
            } else {
                vec![]
            },
            stack: &mut self.stack,
            age: self.age,
            height: self.height,
            has_errored: false,
        }
    }

    /// Outputs a "descriptor" string which reproduces the spent coins
    ///
    /// This may not represent the original descriptor used to produce the transaction,
    /// since it cannot distinguish between sorted and unsorted multisigs (and anyway
    /// it can only see the final keys, keyorigin info is lost in serializing to Bitcoin).
    ///
    /// If you are using the interpreter as a sanity check on a transaction,
    /// it is worthwhile to try to parse this as a descriptor using `from_str`
    /// which will check standardness and consensus limits, which the interpreter
    /// does not do on its own. Or use the `inferred_descriptor` method which
    /// does this for you.
    pub fn inferred_descriptor_string(&self) -> String {
        match self.inner {
            inner::Inner::PublicKey(ref pk, inner::PubkeyType::Pk) => format!("pk({})", pk),
            inner::Inner::PublicKey(ref pk, inner::PubkeyType::Pkh) => format!("pkh({})", pk),
            inner::Inner::PublicKey(ref pk, inner::PubkeyType::Wpkh) => format!("wpkh({})", pk),
            inner::Inner::PublicKey(ref pk, inner::PubkeyType::ShWpkh) => {
                format!("sh(wpkh({}))", pk)
            }
            inner::Inner::Script(ref ms, inner::ScriptType::Bare) => format!("{}", ms),
            inner::Inner::Script(ref ms, inner::ScriptType::Sh) => format!("sh({})", ms),
            inner::Inner::Script(ref ms, inner::ScriptType::Wsh) => format!("wsh({})", ms),
            inner::Inner::Script(ref ms, inner::ScriptType::ShWsh) => format!("sh(wsh({}))", ms),
        }
    }

    /// Whether this is a pre-segwit spend
    pub fn is_legacy(&self) -> bool {
        match self.inner {
            inner::Inner::PublicKey(_, inner::PubkeyType::Pk) => true,
            inner::Inner::PublicKey(_, inner::PubkeyType::Pkh) => true,
            inner::Inner::PublicKey(_, inner::PubkeyType::Wpkh) => false,
            inner::Inner::PublicKey(_, inner::PubkeyType::ShWpkh) => false, // lol "sorta"
            inner::Inner::Script(_, inner::ScriptType::Bare) => true,
            inner::Inner::Script(_, inner::ScriptType::Sh) => true,
            inner::Inner::Script(_, inner::ScriptType::Wsh) => false,
            inner::Inner::Script(_, inner::ScriptType::ShWsh) => false, // lol "sorta"
        }
    }

    /// Outputs a "descriptor" which reproduces the spent coins
    ///
    /// This may not represent the original descriptor used to produce the transaction,
    /// since it cannot distinguish between sorted and unsorted multisigs (and anyway
    /// it can only see the final keys, keyorigin info is lost in serializing to Bitcoin).
    pub fn inferred_descriptor(&self) -> Result<Descriptor<bitcoin::PublicKey>, ::Error> {
        use std::str::FromStr;
        Descriptor::from_str(&self.inferred_descriptor_string())
    }

    /// Returns a sighash over the entire transaction which can be used to verify signatures
    /// in the descriptor
    ///
    /// Not all fields are used by legacy descriptors; if you are sure this is a legacy
    /// spend (you can check with the `is_legacy` method) you can provide dummy data for
    /// the amount.
    pub fn sighash_message(
        &self,
        unsigned_tx: &bitcoin::Transaction,
        input_idx: usize,
        amount: u64,
        sighash_type: bitcoin::EcdsaSigHashType,
    ) -> Result<secp256k1::Message, Error> {
        let mut cache = sighash::SigHashCache::new(unsigned_tx);
        let hash = if self.is_legacy() {
            cache.legacy_signature_hash(input_idx, &self.script_code, sighash_type.as_u32())?
        } else {
            cache.segwit_signature_hash(input_idx, &self.script_code, amount, sighash_type)?
        };

        Ok(secp256k1::Message::from_slice(&hash[..])
            .expect("cryptographically unreachable for this to fail"))
    }

    /// Returns a closure which can be given to the `iter` method to check all signatures
    pub fn sighash_verify<'a, C: secp256k1::Verification>(
        &self,
        secp: &'a secp256k1::Secp256k1<C>,
        unsigned_tx: &'a bitcoin::Transaction,
        input_idx: usize,
        amount: u64,
    ) -> Result<impl Fn(&bitcoin::PublicKey, bitcoin::EcdsaSig) -> bool + 'a, Error> {
        // Precompute all sighash types because the borrowck doesn't like us
        // pulling self into the closure
        let sighashes = [
            self.sighash_message(
                unsigned_tx,
                input_idx,
                amount,
                bitcoin::EcdsaSigHashType::All,
            )?,
            self.sighash_message(
                unsigned_tx,
                input_idx,
                amount,
                bitcoin::EcdsaSigHashType::None,
            )?,
            self.sighash_message(
                unsigned_tx,
                input_idx,
                amount,
                bitcoin::EcdsaSigHashType::Single,
            )?,
            self.sighash_message(
                unsigned_tx,
                input_idx,
                amount,
                bitcoin::EcdsaSigHashType::AllPlusAnyoneCanPay,
            )?,
            self.sighash_message(
                unsigned_tx,
                input_idx,
                amount,
                bitcoin::EcdsaSigHashType::NonePlusAnyoneCanPay,
            )?,
            self.sighash_message(
                unsigned_tx,
                input_idx,
                amount,
                bitcoin::EcdsaSigHashType::SinglePlusAnyoneCanPay,
            )?,
        ];

        Ok(
            move |pk: &bitcoin::PublicKey, ecdsa_sig: bitcoin::EcdsaSig| {
                // This is an awkward way to do this lookup, but it lets us do exhaustiveness
                // checking in case future rust-bitcoin versions add new sighash types
                let sighash = match ecdsa_sig.hash_ty {
                    bitcoin::EcdsaSigHashType::All => sighashes[0],
                    bitcoin::EcdsaSigHashType::None => sighashes[1],
                    bitcoin::EcdsaSigHashType::Single => sighashes[2],
                    bitcoin::EcdsaSigHashType::AllPlusAnyoneCanPay => sighashes[3],
                    bitcoin::EcdsaSigHashType::NonePlusAnyoneCanPay => sighashes[4],
                    bitcoin::EcdsaSigHashType::SinglePlusAnyoneCanPay => sighashes[5],
                };
                secp.verify_ecdsa(&sighash, &ecdsa_sig.sig, &pk.inner)
                    .is_ok()
            },
        )
    }
}

/// Type of HashLock used for SatisfiedConstraint structure
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum HashLockType<'intp> {
    ///SHA 256 hashlock
    Sha256(&'intp sha256::Hash),
    ///Hash 256 hashlock
    Hash256(&'intp sha256d::Hash),
    ///Hash160 hashlock
    Hash160(&'intp hash160::Hash),
    ///Ripemd160 hashlock
    Ripemd160(&'intp ripemd160::Hash),
}

/// A satisfied Miniscript condition (Signature, Hashlock, Timelock)
/// 'intp represents the lifetime of descriptor and `stack represents
/// the lifetime of witness
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SatisfiedConstraint<'intp, 'txin> {
    ///Public key and corresponding signature
    PublicKey {
        /// The bitcoin key
        key: &'intp bitcoin::PublicKey,
        /// corresponding signature
        sig: secp256k1::ecdsa::Signature,
    },
    ///PublicKeyHash, corresponding pubkey and signature
    PublicKeyHash {
        /// The pubkey hash
        keyhash: &'intp hash160::Hash,
        /// Corresponding public key
        key: bitcoin::PublicKey,
        /// Corresponding signature for the hash
        sig: secp256k1::ecdsa::Signature,
    },
    ///Hashlock and preimage for SHA256
    HashLock {
        /// The type of Hashlock
        hash: HashLockType<'intp>,
        /// The preimage used for satisfaction
        preimage: &'txin [u8],
    },
    ///Relative Timelock for CSV.
    RelativeTimeLock {
        /// The value of RelativeTimelock
        time: &'intp u32,
    },
    ///Absolute Timelock for CLTV.
    AbsoluteTimeLock {
        /// The value of Absolute timelock
        time: &'intp u32,
    },
}

///This is used by the interpreter to know which evaluation state a AstemElem is.
///This is required because whenever a same node(for eg. OrB) appears on the stack, we don't
///know if the left child has been evaluated or not. And based on the result on
///the top of the stack, we need to decide whether to execute right child or not.
///This is also useful for wrappers and thresholds which push a value on the stack
///depending on evaluation of the children.
struct NodeEvaluationState<'intp> {
    ///The node which is being evaluated
    node: &'intp Miniscript<bitcoin::PublicKey, NoChecksEcdsa>,
    ///number of children evaluated
    n_evaluated: usize,
    ///number of children satisfied
    n_satisfied: usize,
}

/// Iterator over all the constraints satisfied by a completed scriptPubKey
/// and witness stack
///
/// Returns all satisfied constraints, even if they were redundant (i.e. did
/// not contribute to the script being satisfied). For example, if a signature
/// were provided for an `and_b(Pk,false)` fragment, that signature will be
/// returned, even though the entire and_b must have failed and must not have
/// been used.
///
/// In case the script is actually dissatisfied, this may return several values
/// before ultimately returning an error.
pub struct Iter<'intp, 'txin: 'intp, F: FnMut(&bitcoin::PublicKey, bitcoin::EcdsaSig) -> bool> {
    verify_sig: F,
    public_key: Option<&'intp bitcoin::PublicKey>,
    state: Vec<NodeEvaluationState<'intp>>,
    stack: &'intp mut Stack<'txin>,
    age: u32,
    height: u32,
    has_errored: bool,
}

///Iterator for Iter
impl<'intp, 'txin: 'intp, F> Iterator for Iter<'intp, 'txin, F>
where
    NoChecksEcdsa: ScriptContext,
    F: FnMut(&bitcoin::PublicKey, bitcoin::EcdsaSig) -> bool,
{
    type Item = Result<SatisfiedConstraint<'intp, 'txin>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_errored {
            // Stop yielding values after the first error
            None
        } else {
            let res = self.iter_next();
            if let Some(Err(_)) = res {
                self.has_errored = true;
            }
            res
        }
    }
}

impl<'intp, 'txin: 'intp, F> Iter<'intp, 'txin, F>
where
    NoChecksEcdsa: ScriptContext,
    F: FnMut(&bitcoin::PublicKey, bitcoin::EcdsaSig) -> bool,
{
    /// Helper function to push a NodeEvaluationState on state stack
    fn push_evaluation_state(
        &mut self,
        node: &'intp Miniscript<bitcoin::PublicKey, NoChecksEcdsa>,
        n_evaluated: usize,
        n_satisfied: usize,
    ) -> () {
        self.state.push(NodeEvaluationState {
            node,
            n_evaluated,
            n_satisfied,
        })
    }

    /// Helper function to step the iterator
    fn iter_next(&mut self) -> Option<Result<SatisfiedConstraint<'intp, 'txin>, Error>> {
        while let Some(node_state) = self.state.pop() {
            //non-empty stack
            match node_state.node.node {
                Terminal::True => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    self.stack.push(stack::Element::Satisfied);
                }
                Terminal::False => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    self.stack.push(stack::Element::Dissatisfied);
                }
                Terminal::PkK(ref pk) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    let res = self.stack.evaluate_pk(&mut self.verify_sig, pk);
                    if res.is_some() {
                        return res;
                    }
                }
                Terminal::PkH(ref pkh) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    let res = self.stack.evaluate_pkh(&mut self.verify_sig, pkh);
                    if res.is_some() {
                        return res;
                    }
                }
                Terminal::After(ref n) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    let res = self.stack.evaluate_after(n, self.age);
                    if res.is_some() {
                        return res;
                    }
                }
                Terminal::Older(ref n) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    let res = self.stack.evaluate_older(n, self.height);
                    if res.is_some() {
                        return res;
                    }
                }
                Terminal::Sha256(ref hash) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    let res = self.stack.evaluate_sha256(hash);
                    if res.is_some() {
                        return res;
                    }
                }
                Terminal::Hash256(ref hash) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    let res = self.stack.evaluate_hash256(hash);
                    if res.is_some() {
                        return res;
                    }
                }
                Terminal::Hash160(ref hash) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    let res = self.stack.evaluate_hash160(hash);
                    if res.is_some() {
                        return res;
                    }
                }
                Terminal::Ripemd160(ref hash) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    let res = self.stack.evaluate_ripemd160(hash);
                    if res.is_some() {
                        return res;
                    }
                }
                Terminal::Alt(ref sub) | Terminal::Swap(ref sub) | Terminal::Check(ref sub) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    self.push_evaluation_state(sub, 0, 0);
                }
                Terminal::DupIf(ref sub) if node_state.n_evaluated == 0 => match self.stack.pop() {
                    Some(stack::Element::Dissatisfied) => {
                        self.stack.push(stack::Element::Dissatisfied);
                    }
                    Some(stack::Element::Satisfied) => {
                        self.push_evaluation_state(node_state.node, 1, 1);
                        self.push_evaluation_state(sub, 0, 0);
                    }
                    Some(stack::Element::Push(_v)) => {
                        return Some(Err(Error::UnexpectedStackElementPush))
                    }
                    None => return Some(Err(Error::UnexpectedStackEnd)),
                },
                Terminal::DupIf(ref _sub) if node_state.n_evaluated == 1 => {
                    self.stack.push(stack::Element::Satisfied);
                }
                Terminal::ZeroNotEqual(ref sub) | Terminal::Verify(ref sub)
                    if node_state.n_evaluated == 0 =>
                {
                    self.push_evaluation_state(node_state.node, 1, 0);
                    self.push_evaluation_state(sub, 0, 0);
                }
                Terminal::Verify(ref _sub) if node_state.n_evaluated == 1 => {
                    match self.stack.pop() {
                        Some(stack::Element::Satisfied) => (),
                        Some(_) => return Some(Err(Error::VerifyFailed)),
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::ZeroNotEqual(ref _sub) if node_state.n_evaluated == 1 => {
                    match self.stack.pop() {
                        Some(stack::Element::Dissatisfied) => {
                            self.stack.push(stack::Element::Dissatisfied)
                        }
                        Some(_) => self.stack.push(stack::Element::Satisfied),
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::NonZero(ref sub) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    match self.stack.last() {
                        Some(&stack::Element::Dissatisfied) => (),
                        Some(_) => self.push_evaluation_state(sub, 0, 0),
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::AndV(ref left, ref right) => {
                    debug_assert_eq!(node_state.n_evaluated, 0);
                    debug_assert_eq!(node_state.n_satisfied, 0);
                    self.push_evaluation_state(right, 0, 0);
                    self.push_evaluation_state(left, 0, 0);
                }
                Terminal::OrB(ref left, ref _right) | Terminal::AndB(ref left, ref _right)
                    if node_state.n_evaluated == 0 =>
                {
                    self.push_evaluation_state(node_state.node, 1, 0);
                    self.push_evaluation_state(left, 0, 0);
                }
                Terminal::OrB(ref _left, ref right) | Terminal::AndB(ref _left, ref right)
                    if node_state.n_evaluated == 1 =>
                {
                    match self.stack.pop() {
                        Some(stack::Element::Dissatisfied) => {
                            self.push_evaluation_state(node_state.node, 2, 0);
                            self.push_evaluation_state(right, 0, 0);
                        }
                        Some(stack::Element::Satisfied) => {
                            self.push_evaluation_state(node_state.node, 2, 1);
                            self.push_evaluation_state(right, 0, 0);
                        }
                        Some(stack::Element::Push(_v)) => {
                            return Some(Err(Error::UnexpectedStackElementPush))
                        }
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::AndB(ref _left, ref _right) if node_state.n_evaluated == 2 => {
                    match self.stack.pop() {
                        Some(stack::Element::Satisfied) if node_state.n_satisfied == 1 => {
                            self.stack.push(stack::Element::Satisfied)
                        }
                        Some(_) => self.stack.push(stack::Element::Dissatisfied),
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::AndOr(ref left, ref _right, _)
                | Terminal::OrC(ref left, ref _right)
                | Terminal::OrD(ref left, ref _right)
                    if node_state.n_evaluated == 0 =>
                {
                    self.push_evaluation_state(node_state.node, 1, 0);
                    self.push_evaluation_state(left, 0, 0);
                }
                Terminal::OrB(ref _left, ref _right) if node_state.n_evaluated == 2 => {
                    match self.stack.pop() {
                        Some(stack::Element::Dissatisfied) if node_state.n_satisfied == 0 => {
                            self.stack.push(stack::Element::Dissatisfied)
                        }
                        Some(_) => {
                            self.stack.push(stack::Element::Satisfied);
                        }
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::OrC(ref _left, ref right) if node_state.n_evaluated == 1 => {
                    match self.stack.pop() {
                        Some(stack::Element::Satisfied) => (),
                        Some(stack::Element::Dissatisfied) => {
                            self.push_evaluation_state(right, 0, 0)
                        }
                        Some(stack::Element::Push(_v)) => {
                            return Some(Err(Error::UnexpectedStackElementPush))
                        }
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::OrD(ref _left, ref right) if node_state.n_evaluated == 1 => {
                    match self.stack.pop() {
                        Some(stack::Element::Satisfied) => {
                            self.stack.push(stack::Element::Satisfied)
                        }
                        Some(stack::Element::Dissatisfied) => {
                            self.push_evaluation_state(right, 0, 0)
                        }
                        Some(stack::Element::Push(_v)) => {
                            return Some(Err(Error::UnexpectedStackElementPush))
                        }
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::AndOr(_, ref left, ref right) | Terminal::OrI(ref left, ref right) => {
                    match self.stack.pop() {
                        Some(stack::Element::Satisfied) => self.push_evaluation_state(left, 0, 0),
                        Some(stack::Element::Dissatisfied) => {
                            self.push_evaluation_state(right, 0, 0)
                        }
                        Some(stack::Element::Push(_v)) => {
                            return Some(Err(Error::UnexpectedStackElementPush))
                        }
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::Thresh(ref _k, ref subs) if node_state.n_evaluated == 0 => {
                    self.push_evaluation_state(node_state.node, 1, 0);
                    self.push_evaluation_state(&subs[0], 0, 0);
                }
                Terminal::Thresh(k, ref subs) if node_state.n_evaluated == subs.len() => {
                    match self.stack.pop() {
                        Some(stack::Element::Dissatisfied) if node_state.n_satisfied == k => {
                            self.stack.push(stack::Element::Satisfied)
                        }
                        Some(stack::Element::Satisfied) if node_state.n_satisfied == k - 1 => {
                            self.stack.push(stack::Element::Satisfied)
                        }
                        Some(stack::Element::Satisfied) | Some(stack::Element::Dissatisfied) => {
                            self.stack.push(stack::Element::Dissatisfied)
                        }
                        Some(stack::Element::Push(_v)) => {
                            return Some(Err(Error::UnexpectedStackElementPush))
                        }
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::Thresh(ref _k, ref subs) if node_state.n_evaluated != 0 => {
                    match self.stack.pop() {
                        Some(stack::Element::Dissatisfied) => {
                            self.push_evaluation_state(
                                node_state.node,
                                node_state.n_evaluated + 1,
                                node_state.n_satisfied,
                            );
                            self.push_evaluation_state(&subs[node_state.n_evaluated], 0, 0);
                        }
                        Some(stack::Element::Satisfied) => {
                            self.push_evaluation_state(
                                node_state.node,
                                node_state.n_evaluated + 1,
                                node_state.n_satisfied + 1,
                            );
                            self.push_evaluation_state(&subs[node_state.n_evaluated], 0, 0);
                        }
                        Some(stack::Element::Push(_v)) => {
                            return Some(Err(Error::UnexpectedStackElementPush))
                        }
                        None => return Some(Err(Error::UnexpectedStackEnd)),
                    }
                }
                Terminal::Multi(ref k, ref subs) if node_state.n_evaluated == 0 => {
                    let len = self.stack.len();
                    if len < k + 1 {
                        return Some(Err(Error::InsufficientSignaturesMultiSig));
                    } else {
                        //Non-sat case. If the first sig is empty, others k elements must
                        //be empty.
                        match self.stack.last() {
                            Some(&stack::Element::Dissatisfied) => {
                                //Remove the extra zero from multi-sig check
                                let sigs = self.stack.split_off(len - (k + 1));
                                let nonsat = sigs
                                    .iter()
                                    .map(|sig| *sig == stack::Element::Dissatisfied)
                                    .filter(|empty| *empty)
                                    .count();
                                if nonsat == *k + 1 {
                                    self.stack.push(stack::Element::Dissatisfied);
                                } else {
                                    return Some(Err(Error::MissingExtraZeroMultiSig));
                                }
                            }
                            None => return Some(Err(Error::UnexpectedStackEnd)),
                            _ => {
                                match self
                                    .stack
                                    .evaluate_multi(&mut self.verify_sig, &subs[subs.len() - 1])
                                {
                                    Some(Ok(x)) => {
                                        self.push_evaluation_state(
                                            node_state.node,
                                            node_state.n_evaluated + 1,
                                            node_state.n_satisfied + 1,
                                        );
                                        return Some(Ok(x));
                                    }
                                    None => self.push_evaluation_state(
                                        node_state.node,
                                        node_state.n_evaluated + 1,
                                        node_state.n_satisfied,
                                    ),
                                    x => return x, //forward errors as is
                                }
                            }
                        }
                    }
                }
                Terminal::Multi(k, ref subs) => {
                    if node_state.n_satisfied == k {
                        //multi-sig bug: Pop extra 0
                        if let Some(stack::Element::Dissatisfied) = self.stack.pop() {
                            self.stack.push(stack::Element::Satisfied);
                        } else {
                            return Some(Err(Error::MissingExtraZeroMultiSig));
                        }
                    } else if node_state.n_evaluated == subs.len() {
                        return Some(Err(Error::MultiSigEvaluationError));
                    } else {
                        match self.stack.evaluate_multi(
                            &mut self.verify_sig,
                            &subs[subs.len() - node_state.n_evaluated - 1],
                        ) {
                            Some(Ok(x)) => {
                                self.push_evaluation_state(
                                    node_state.node,
                                    node_state.n_evaluated + 1,
                                    node_state.n_satisfied + 1,
                                );
                                return Some(Ok(x));
                            }
                            None => self.push_evaluation_state(
                                node_state.node,
                                node_state.n_evaluated + 1,
                                node_state.n_satisfied,
                            ),
                            x => return x, //forward errors as is
                        }
                    }
                }
                //All other match patterns should not be reached in any valid
                //type checked Miniscript
                _ => return Some(Err(Error::CouldNotEvaluate)),
            };
        }

        //state empty implies that either the execution has terminated or we have a
        //Pk based descriptor
        if let Some(pk) = self.public_key {
            if let Some(stack::Element::Push(sig)) = self.stack.pop() {
                if let Ok(sig) = verify_sersig(&mut self.verify_sig, &pk, &sig) {
                    //Signature check successful, set public_key to None to
                    //terminate the next() function in the subsequent call
                    self.public_key = None;
                    self.stack.push(stack::Element::Satisfied);
                    return Some(Ok(SatisfiedConstraint::PublicKey { key: pk, sig }));
                } else {
                    return Some(Err(Error::PkEvaluationError(pk.clone().to_public_key())));
                }
            } else {
                return Some(Err(Error::UnexpectedStackEnd));
            }
        } else {
            //All the script has been executed.
            //Check that the stack must contain exactly 1 satisfied element
            if self.stack.pop() == Some(stack::Element::Satisfied) && self.stack.is_empty() {
                return None;
            } else {
                return Some(Err(Error::ScriptSatisfactionError));
            }
        }
    }
}

/// Helper function to verify serialized signature
fn verify_sersig<'txin, F>(
    verify_sig: F,
    pk: &bitcoin::PublicKey,
    sigser: &[u8],
) -> Result<secp256k1::ecdsa::Signature, Error>
where
    F: FnOnce(&bitcoin::PublicKey, bitcoin::EcdsaSig) -> bool,
{
    if let Some((sighash_byte, sig)) = sigser.split_last() {
        let hash_ty = bitcoin::EcdsaSigHashType::from_u32_standard(*sighash_byte as u32)
            .map_err(|_| Error::NonStandardSigHash([sig, &[*sighash_byte]].concat().to_vec()))?;
        let sig = secp256k1::ecdsa::Signature::from_der(sig)?;
        let ecdsa_sig = bitcoin::EcdsaSig { sig, hash_ty };
        if verify_sig(pk, ecdsa_sig) {
            Ok(ecdsa_sig.sig)
        } else {
            Err(Error::InvalidSignature(*pk))
        }
    } else {
        Err(Error::PkEvaluationError(*pk))
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use bitcoin;
    use bitcoin::hashes::{hash160, ripemd160, sha256, sha256d, Hash};
    use bitcoin::secp256k1::{self, Secp256k1, VerifyOnly};
    use miniscript::context::NoChecksEcdsa;
    use Miniscript;
    use MiniscriptKey;
    use ToPublicKey;

    fn setup_keys_sigs(
        n: usize,
    ) -> (
        Vec<bitcoin::PublicKey>,
        Vec<Vec<u8>>,
        Vec<secp256k1::ecdsa::Signature>,
        secp256k1::Message,
        Secp256k1<VerifyOnly>,
    ) {
        let secp_sign = secp256k1::Secp256k1::signing_only();
        let secp_verify = secp256k1::Secp256k1::verification_only();
        let msg = secp256k1::Message::from_slice(&b"Yoda: btc, I trust. HODL I must!"[..])
            .expect("32 bytes");
        let mut pks = vec![];
        let mut secp_sigs = vec![];
        let mut der_sigs = vec![];
        let mut sk = [0; 32];
        for i in 1..n + 1 {
            sk[0] = i as u8;
            sk[1] = (i >> 8) as u8;
            sk[2] = (i >> 16) as u8;

            let sk = secp256k1::SecretKey::from_slice(&sk[..]).expect("secret key");
            let pk = bitcoin::PublicKey {
                inner: secp256k1::PublicKey::from_secret_key(&secp_sign, &sk),
                compressed: true,
            };
            let sig = secp_sign.sign_ecdsa(&msg, &sk);
            secp_sigs.push(sig);
            let mut sigser = sig.serialize_der().to_vec();
            sigser.push(0x01); // sighash_all
            pks.push(pk);
            der_sigs.push(sigser);
        }
        (pks, der_sigs, secp_sigs, msg, secp_verify)
    }

    #[test]
    fn sat_constraints() {
        let (pks, der_sigs, secp_sigs, sighash, secp) = setup_keys_sigs(10);
        let vfyfn_ = |pk: &bitcoin::PublicKey, ecdsa_sig: bitcoin::EcdsaSig| {
            secp.verify_ecdsa(&sighash, &ecdsa_sig.sig, &pk.inner)
                .is_ok()
        };

        fn from_stack<'txin, 'elem, F>(
            verify_fn: F,
            stack: &'elem mut Stack<'txin>,
            ms: &'elem Miniscript<bitcoin::PublicKey, NoChecksEcdsa>,
        ) -> Iter<'elem, 'txin, F>
        where
            F: FnMut(&bitcoin::PublicKey, bitcoin::EcdsaSig) -> bool,
        {
            Iter {
                verify_sig: verify_fn,
                stack: stack,
                public_key: None,
                state: vec![NodeEvaluationState {
                    node: ms,
                    n_evaluated: 0,
                    n_satisfied: 0,
                }],
                age: 1002,
                height: 1002,
                has_errored: false,
            }
        }

        let pk = ms_str!("c:pk_k({})", pks[0]);
        let pkh = ms_str!("c:pk_h({})", pks[1].to_pubkeyhash());
        //Time
        let after = ms_str!("after({})", 1000);
        let older = ms_str!("older({})", 1000);
        //Hashes
        let preimage = vec![0xab as u8; 32];
        let sha256_hash = sha256::Hash::hash(&preimage);
        let sha256 = ms_str!("sha256({})", sha256_hash);
        let sha256d_hash_rev = sha256d::Hash::hash(&preimage);
        let mut sha256d_hash_bytes = sha256d_hash_rev.clone().into_inner();
        sha256d_hash_bytes.reverse();
        let sha256d_hash = sha256d::Hash::from_inner(sha256d_hash_bytes);
        let hash256 = ms_str!("hash256({})", sha256d_hash);
        let hash160_hash = hash160::Hash::hash(&preimage);
        let hash160 = ms_str!("hash160({})", hash160_hash);
        let ripemd160_hash = ripemd160::Hash::hash(&preimage);
        let ripemd160 = ms_str!("ripemd160({})", ripemd160_hash);

        let mut stack = Stack::from(vec![stack::Element::Push(&der_sigs[0])]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &pk);
        let pk_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            pk_satisfied.unwrap(),
            vec![SatisfiedConstraint::PublicKey {
                key: &pks[0],
                sig: secp_sigs[0].clone(),
            }]
        );

        //Check Pk failure with wrong signature
        let mut stack = Stack::from(vec![stack::Element::Dissatisfied]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &pk);
        let pk_err: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert!(pk_err.is_err());

        //Check Pkh
        let pk_bytes = pks[1].to_public_key().to_bytes();
        let mut stack = Stack::from(vec![
            stack::Element::Push(&der_sigs[1]),
            stack::Element::Push(&pk_bytes),
        ]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &pkh);
        let pkh_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            pkh_satisfied.unwrap(),
            vec![SatisfiedConstraint::PublicKeyHash {
                keyhash: &pks[1].to_pubkeyhash(),
                key: pks[1].clone(),
                sig: secp_sigs[1].clone(),
            }]
        );

        //Check After
        let mut stack = Stack::from(vec![]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &after);
        let after_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            after_satisfied.unwrap(),
            vec![SatisfiedConstraint::AbsoluteTimeLock { time: &1000 }]
        );

        //Check Older
        let mut stack = Stack::from(vec![]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &older);
        let older_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            older_satisfied.unwrap(),
            vec![SatisfiedConstraint::RelativeTimeLock { time: &1000 }]
        );

        //Check Sha256
        let mut stack = Stack::from(vec![stack::Element::Push(&preimage)]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &sha256);
        let sah256_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            sah256_satisfied.unwrap(),
            vec![SatisfiedConstraint::HashLock {
                hash: HashLockType::Sha256(&sha256_hash),
                preimage: &preimage,
            }]
        );

        //Check Shad256
        let mut stack = Stack::from(vec![stack::Element::Push(&preimage)]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &hash256);
        let sha256d_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            sha256d_satisfied.unwrap(),
            vec![SatisfiedConstraint::HashLock {
                hash: HashLockType::Hash256(&sha256d_hash_rev),
                preimage: &preimage,
            }]
        );

        //Check hash160
        let mut stack = Stack::from(vec![stack::Element::Push(&preimage)]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &hash160);
        let hash160_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            hash160_satisfied.unwrap(),
            vec![SatisfiedConstraint::HashLock {
                hash: HashLockType::Hash160(&hash160_hash),
                preimage: &preimage,
            }]
        );

        //Check ripemd160
        let mut stack = Stack::from(vec![stack::Element::Push(&preimage)]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &ripemd160);
        let ripemd160_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            ripemd160_satisfied.unwrap(),
            vec![SatisfiedConstraint::HashLock {
                hash: HashLockType::Ripemd160(&ripemd160_hash),
                preimage: &preimage
            }]
        );

        //Check AndV
        let pk_bytes = pks[1].to_public_key().to_bytes();
        let mut stack = Stack::from(vec![
            stack::Element::Push(&der_sigs[1]),
            stack::Element::Push(&pk_bytes),
            stack::Element::Push(&der_sigs[0]),
        ]);
        let elem = ms_str!(
            "and_v(vc:pk_k({}),c:pk_h({}))",
            pks[0],
            pks[1].to_pubkeyhash()
        );
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let and_v_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            and_v_satisfied.unwrap(),
            vec![
                SatisfiedConstraint::PublicKey {
                    key: &pks[0],
                    sig: secp_sigs[0].clone(),
                },
                SatisfiedConstraint::PublicKeyHash {
                    keyhash: &pks[1].to_pubkeyhash(),
                    key: pks[1].clone(),
                    sig: secp_sigs[1].clone(),
                }
            ]
        );

        //Check AndB
        let mut stack = Stack::from(vec![
            stack::Element::Push(&preimage),
            stack::Element::Push(&der_sigs[0]),
        ]);
        let elem = ms_str!("and_b(c:pk_k({}),sjtv:sha256({}))", pks[0], sha256_hash);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let and_b_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            and_b_satisfied.unwrap(),
            vec![
                SatisfiedConstraint::PublicKey {
                    key: &pks[0],
                    sig: secp_sigs[0].clone(),
                },
                SatisfiedConstraint::HashLock {
                    hash: HashLockType::Sha256(&sha256_hash),
                    preimage: &preimage,
                }
            ]
        );

        //Check AndOr
        let mut stack = Stack::from(vec![
            stack::Element::Push(&preimage),
            stack::Element::Push(&der_sigs[0]),
        ]);
        let elem = ms_str!(
            "andor(c:pk_k({}),jtv:sha256({}),c:pk_h({}))",
            pks[0],
            sha256_hash,
            pks[1].to_pubkeyhash(),
        );
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let and_or_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            and_or_satisfied.unwrap(),
            vec![
                SatisfiedConstraint::PublicKey {
                    key: &pks[0],
                    sig: secp_sigs[0].clone(),
                },
                SatisfiedConstraint::HashLock {
                    hash: HashLockType::Sha256(&sha256_hash),
                    preimage: &preimage,
                }
            ]
        );

        //AndOr second satisfaction path
        let pk_bytes = pks[1].to_public_key().to_bytes();
        let mut stack = Stack::from(vec![
            stack::Element::Push(&der_sigs[1]),
            stack::Element::Push(&pk_bytes),
            stack::Element::Dissatisfied,
        ]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let and_or_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            and_or_satisfied.unwrap(),
            vec![SatisfiedConstraint::PublicKeyHash {
                keyhash: &pks[1].to_pubkeyhash(),
                key: pks[1].clone(),
                sig: secp_sigs[1].clone(),
            }]
        );

        //Check OrB
        let mut stack = Stack::from(vec![
            stack::Element::Push(&preimage),
            stack::Element::Dissatisfied,
        ]);
        let elem = ms_str!("or_b(c:pk_k({}),sjtv:sha256({}))", pks[0], sha256_hash);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let or_b_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            or_b_satisfied.unwrap(),
            vec![SatisfiedConstraint::HashLock {
                hash: HashLockType::Sha256(&sha256_hash),
                preimage: &preimage,
            }]
        );

        //Check OrD
        let mut stack = Stack::from(vec![stack::Element::Push(&der_sigs[0])]);
        let elem = ms_str!("or_d(c:pk_k({}),jtv:sha256({}))", pks[0], sha256_hash);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let or_d_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            or_d_satisfied.unwrap(),
            vec![SatisfiedConstraint::PublicKey {
                key: &pks[0],
                sig: secp_sigs[0].clone(),
            }]
        );

        //Check OrC
        let mut stack = Stack::from(vec![
            stack::Element::Push(&der_sigs[0]),
            stack::Element::Dissatisfied,
        ]);
        let elem = ms_str!("t:or_c(jtv:sha256({}),vc:pk_k({}))", sha256_hash, pks[0]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let or_c_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            or_c_satisfied.unwrap(),
            vec![SatisfiedConstraint::PublicKey {
                key: &pks[0],
                sig: secp_sigs[0].clone(),
            }]
        );

        //Check OrI
        let mut stack = Stack::from(vec![
            stack::Element::Push(&der_sigs[0]),
            stack::Element::Dissatisfied,
        ]);
        let elem = ms_str!("or_i(jtv:sha256({}),c:pk_k({}))", sha256_hash, pks[0]);
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let or_i_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            or_i_satisfied.unwrap(),
            vec![SatisfiedConstraint::PublicKey {
                key: &pks[0],
                sig: secp_sigs[0].clone(),
            }]
        );

        //Check Thres
        let mut stack = Stack::from(vec![
            stack::Element::Push(&der_sigs[0]),
            stack::Element::Push(&der_sigs[1]),
            stack::Element::Push(&der_sigs[2]),
            stack::Element::Dissatisfied,
            stack::Element::Dissatisfied,
        ]);
        let elem = ms_str!(
            "thresh(3,c:pk_k({}),sc:pk_k({}),sc:pk_k({}),sc:pk_k({}),sc:pk_k({}))",
            pks[4],
            pks[3],
            pks[2],
            pks[1],
            pks[0],
        );
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let thresh_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            thresh_satisfied.unwrap(),
            vec![
                SatisfiedConstraint::PublicKey {
                    key: &pks[2],
                    sig: secp_sigs[2].clone(),
                },
                SatisfiedConstraint::PublicKey {
                    key: &pks[1],
                    sig: secp_sigs[1].clone(),
                },
                SatisfiedConstraint::PublicKey {
                    key: &pks[0],
                    sig: secp_sigs[0].clone(),
                }
            ]
        );

        // Check multi
        let mut stack = Stack::from(vec![
            stack::Element::Dissatisfied,
            stack::Element::Push(&der_sigs[2]),
            stack::Element::Push(&der_sigs[1]),
            stack::Element::Push(&der_sigs[0]),
        ]);
        let elem = ms_str!(
            "multi(3,{},{},{},{},{})",
            pks[4],
            pks[3],
            pks[2],
            pks[1],
            pks[0],
        );
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let multi_satisfied: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert_eq!(
            multi_satisfied.unwrap(),
            vec![
                SatisfiedConstraint::PublicKey {
                    key: &pks[0],
                    sig: secp_sigs[0].clone(),
                },
                SatisfiedConstraint::PublicKey {
                    key: &pks[1],
                    sig: secp_sigs[1].clone(),
                },
                SatisfiedConstraint::PublicKey {
                    key: &pks[2],
                    sig: secp_sigs[2].clone(),
                },
            ]
        );

        // Error multi: Invalid order of sigs
        let mut stack = Stack::from(vec![
            stack::Element::Dissatisfied,
            stack::Element::Push(&der_sigs[0]),
            stack::Element::Push(&der_sigs[2]),
            stack::Element::Push(&der_sigs[1]),
        ]);
        let elem = ms_str!(
            "multi(3,{},{},{},{},{})",
            pks[4],
            pks[3],
            pks[2],
            pks[1],
            pks[0],
        );
        let mut vfyfn = vfyfn_.clone(); // sigh rust 1.29...
        let constraints = from_stack(&mut vfyfn, &mut stack, &elem);

        let multi_error: Result<Vec<SatisfiedConstraint>, Error> = constraints.collect();
        assert!(multi_error.is_err());
    }
}
