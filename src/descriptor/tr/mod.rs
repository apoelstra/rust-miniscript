// SPDX-License-Identifier: CC0-1.0

use core::{cmp, fmt, hash};

use bitcoin::taproot::{TAPROOT_CONTROL_BASE_SIZE, TAPROOT_CONTROL_NODE_SIZE};
use bitcoin::{opcodes, Address, Network, ScriptBuf, Weight};
use sync::Arc;

use super::checksum;
use crate::descriptor::DefiniteDescriptorKey;
use crate::expression::{self, FromTree};
use crate::miniscript::satisfy::{Placeholder, Satisfaction, SchnorrSigType, Witness};
use crate::plan::AssetProvider;
use crate::policy::semantic::Policy;
use crate::policy::Liftable;
use crate::prelude::*;
use crate::util::{varint_len, witness_size};
use crate::{
    Error, ForEachKey, FromStrKey, Miniscript, MiniscriptKey, ParseError, Satisfier,
    ScriptContext as _, Tap, Threshold, ToPublicKey, TranslateErr, Translator, ValidationError,
};

mod spend_info;
mod taptree;

pub use self::spend_info::{TrSpendInfo, TrSpendInfoIter, TrSpendInfoIterItem};
pub use self::taptree::{TapTree, TapTreeDepthError, TapTreeIter, TapTreeIterItem};

/// A taproot descriptor
pub struct Tr<Pk: MiniscriptKey> {
    /// A taproot internal key
    internal_key: Pk,
    /// Optional Taproot Tree with spending conditions
    tree: Option<TapTree<Pk>>,
    /// Optional spending information associated with the descriptor
    /// This will be [`None`] when the descriptor is not derived.
    /// This information will be cached automatically when it is required
    //
    // The inner `Arc` here is because Rust does not allow us to return a reference
    // to the contents of the `Option` from inside a `MutexGuard`. There is no outer
    // `Arc` because when this structure is cloned, we create a whole new mutex.
    spend_info: Mutex<Option<Arc<TrSpendInfo<Pk>>>>,
}

impl<Pk: MiniscriptKey> Clone for Tr<Pk> {
    fn clone(&self) -> Self {
        // When cloning, construct a new Mutex so that distinct clones don't
        // cause blocking between each other. We clone only the internal `Arc`,
        // so the clone is always cheap (in both time and space)
        Self {
            internal_key: self.internal_key.clone(),
            tree: self.tree.clone(),
            spend_info: Mutex::new(
                self.spend_info
                    .lock()
                    .expect("Lock poisoned")
                    .as_ref()
                    .map(Arc::clone),
            ),
        }
    }
}

impl<Pk: MiniscriptKey> PartialEq for Tr<Pk> {
    fn eq(&self, other: &Self) -> bool {
        self.internal_key == other.internal_key && self.tree == other.tree
    }
}

impl<Pk: MiniscriptKey> Eq for Tr<Pk> {}

impl<Pk: MiniscriptKey> PartialOrd for Tr<Pk> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}

impl<Pk: MiniscriptKey> Ord for Tr<Pk> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match self.internal_key.cmp(&other.internal_key) {
            cmp::Ordering::Equal => {}
            ord => return ord,
        }
        self.tree.cmp(&other.tree)
    }
}

impl<Pk: MiniscriptKey> hash::Hash for Tr<Pk> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.internal_key.hash(state);
        self.tree.hash(state);
    }
}

impl<Pk: MiniscriptKey> Tr<Pk> {
    /// Create a new [`Tr`] descriptor from internal key and [`TapTree`]
    pub fn new(internal_key: Pk, tree: Option<TapTree<Pk>>) -> Result<Self, ValidationError> {
        Tap::SANE.validate_pk(&internal_key)?;
        Ok(Self { internal_key, tree, spend_info: Mutex::new(None) })
    }

    /// Obtain the internal key of [`Tr`] descriptor
    pub fn internal_key(&self) -> &Pk { &self.internal_key }

    /// Obtain the [`TapTree`] of the [`Tr`] descriptor
    pub fn tap_tree(&self) -> Option<&TapTree<Pk>> { self.tree.as_ref() }

    /// Iterates over all the leaves of the tree in depth-first preorder.
    ///
    /// The yielded elements include the Miniscript for each leave as well as its depth
    /// in the tree, which is the data required by PSBT (BIP 371).
    pub fn leaves(&self) -> TapTreeIter<'_, Pk> {
        match self.tree {
            Some(ref t) => t.leaves(),
            None => TapTreeIter::empty(),
        }
    }

    /// Obtain the spending information for this [`Tr`].
    ///
    /// The first time this method is called, it computes the full Taproot Merkle tree of
    /// all branches as well as the output key which appears on-chain. This is fairly
    /// expensive since it requires hashing every branch and then doing an elliptic curve
    /// operation. The result is cached and reused on subsequent calls.
    ///
    /// This data is needed to compute the Taproot output, so this method is implicitly
    /// called through [`Self::script_pubkey`], [`Self::address`], etc. It is also needed
    /// to compute the hash needed to sign the output.
    pub fn spend_info(&self) -> Arc<TrSpendInfo<Pk>>
    where
        Pk: ToPublicKey,
    {
        let mut lock = self.spend_info.lock().unwrap();
        match *lock {
            Some(ref res) => Arc::clone(res),
            None => {
                let arc = Arc::new(TrSpendInfo::from_tr(self));
                *lock = Some(Arc::clone(&arc));
                arc
            }
        }
    }

    /// Computes an upper bound on the difference between a non-satisfied
    /// `TxIn`'s `segwit_weight` and a satisfied `TxIn`'s `segwit_weight`
    ///
    /// Assumes all Schnorr signatures are 66 bytes, including push opcode and
    /// sighash suffix.
    ///
    /// # Errors
    /// When the descriptor is impossible to safisfy (ex: sh(OP_FALSE)).
    pub fn max_weight_to_satisfy(&self) -> Result<Weight, Error> {
        let tree = match self.tap_tree() {
            None => {
                // key spend path
                // item: varint(sig+sigHash) + <sig(64)+sigHash(1)>
                let item_sig_size = 1 + 65;
                // 1 stack item
                let stack_varint_diff = varint_len(1) - varint_len(0);

                return Ok(Weight::from_wu((stack_varint_diff + item_sig_size) as u64));
            }
            // script path spend..
            Some(tree) => tree,
        };

        let wu = tree
            .leaves()
            .filter_map(|leaf| {
                let script_size = leaf.miniscript().script_size();
                let max_sat_elems = leaf.miniscript().max_satisfaction_witness_elements().ok()?;
                let max_sat_size = leaf.miniscript().max_satisfaction_size().ok()?;
                let control_block_size = control_block_len(leaf.depth());

                // stack varint difference (+1 for ctrl block, witness script already included)
                let stack_varint_diff = varint_len(max_sat_elems + 1) - varint_len(0);

                Some(
                    stack_varint_diff +
                    // size of elements to satisfy script
                    max_sat_size +
                    // second to last element: script
                    varint_len(script_size) +
                    script_size +
                    // last element: control block
                    varint_len(control_block_size) +
                    control_block_size,
                )
            })
            .max()
            .ok_or(Error::ImpossibleSatisfaction)?;

        Ok(Weight::from_wu(wu as u64))
    }

    /// Computes an upper bound on the weight of a satisfying witness to the
    /// transaction.
    ///
    /// Assumes all ec-signatures are 73 bytes, including push opcode and
    /// sighash suffix. Includes the weight of the VarInts encoding the
    /// scriptSig and witness stack length.
    ///
    /// # Errors
    /// When the descriptor is impossible to safisfy (ex: sh(OP_FALSE)).
    #[deprecated(
        since = "10.0.0",
        note = "Use max_weight_to_satisfy instead. The method to count bytes was redesigned and the results will differ from max_weight_to_satisfy. For more details check rust-bitcoin/rust-miniscript#476."
    )]
    pub fn max_satisfaction_weight(&self) -> Result<usize, Error> {
        let tree = match self.tap_tree() {
            // key spend path:
            // scriptSigLen(4) + stackLen(1) + stack[Sig]Len(1) + stack[Sig](65)
            None => return Ok(4 + 1 + 1 + 65),
            // script path spend..
            Some(tree) => tree,
        };

        tree.leaves()
            .filter_map(|leaf| {
                let script_size = leaf.miniscript().script_size();
                let max_sat_elems = leaf.miniscript().max_satisfaction_witness_elements().ok()?;
                let max_sat_size = leaf.miniscript().max_satisfaction_size().ok()?;
                let control_block_size = control_block_len(leaf.depth());
                Some(
                    // scriptSig len byte
                    4 +
                    // witness field stack len (+2 for control block & script)
                    varint_len(max_sat_elems + 2) +
                    // size of elements to satisfy script
                    max_sat_size +
                    // second to last element: script
                    varint_len(script_size) +
                    script_size +
                    // last element: control block
                    varint_len(control_block_size) +
                    control_block_size,
                )
            })
            .max()
            .ok_or(Error::ImpossibleSatisfaction)
    }

    /// Converts keys from one type of public key to another.
    pub fn translate_pk<T>(
        &self,
        translate: &mut T,
    ) -> Result<Tr<T::TargetPk>, TranslateErr<T::Error>>
    where
        T: Translator<Pk>,
    {
        let tree = match &self.tree {
            Some(tree) => Some(tree.translate_pk(translate)?),
            None => None,
        };
        let translate_desc = Tr::new(translate.pk(&self.internal_key)?, tree)
            .map_err(Error::Validation)
            .map_err(TranslateErr::OuterError)?;
        Ok(translate_desc)
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Tr<Pk> {
    /// Obtains the corresponding script pubkey for this descriptor.
    pub fn script_pubkey(&self) -> ScriptBuf {
        let output_key = self.spend_info().output_key();
        let builder = bitcoin::blockdata::script::Builder::new();
        builder
            .push_opcode(opcodes::all::OP_PUSHNUM_1)
            .push_slice(output_key.serialize())
            .into_script()
    }

    /// Obtains the corresponding address for this descriptor.
    pub fn address(&self, network: Network) -> Address {
        let spend_info = self.spend_info();
        Address::p2tr_tweaked(spend_info.output_key(), network)
    }

    /// Returns satisfying non-malleable witness and scriptSig with minimum
    /// weight to spend an output controlled by the given descriptor if it is
    /// possible to construct one using the `satisfier`.
    pub fn get_satisfaction<S>(&self, satisfier: &S) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        let satisfaction = best_tap_spend(self, satisfier, false /* allow_mall */)
            .try_completing(satisfier)
            .expect("the same satisfier should manage to complete the template");
        if let Witness::Stack(stack) = satisfaction.stack {
            Ok((stack, ScriptBuf::new()))
        } else {
            Err(Error::CouldNotSatisfy)
        }
    }

    /// Returns satisfying, possibly malleable, witness and scriptSig with
    /// minimum weight to spend an output controlled by the given descriptor if
    /// it is possible to construct one using the `satisfier`.
    pub fn get_satisfaction_mall<S>(
        &self,
        satisfier: &S,
    ) -> Result<(Vec<Vec<u8>>, ScriptBuf), Error>
    where
        S: Satisfier<Pk>,
    {
        let satisfaction = best_tap_spend(self, satisfier, true /* allow_mall */)
            .try_completing(satisfier)
            .expect("the same satisfier should manage to complete the template");
        if let Witness::Stack(stack) = satisfaction.stack {
            Ok((stack, ScriptBuf::new()))
        } else {
            Err(Error::CouldNotSatisfy)
        }
    }
}

impl Tr<DefiniteDescriptorKey> {
    /// Returns a plan if the provided assets are sufficient to produce a non-malleable satisfaction
    pub fn plan_satisfaction<P>(
        &self,
        provider: &P,
    ) -> Satisfaction<Placeholder<DefiniteDescriptorKey>>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        best_tap_spend(self, provider, false /* allow_mall */)
    }

    /// Returns a plan if the provided assets are sufficient to produce a malleable satisfaction
    pub fn plan_satisfaction_mall<P>(
        &self,
        provider: &P,
    ) -> Satisfaction<Placeholder<DefiniteDescriptorKey>>
    where
        P: AssetProvider<DefiniteDescriptorKey>,
    {
        best_tap_spend(self, provider, true /* allow_mall */)
    }
}

impl<Pk: FromStrKey> core::str::FromStr for Tr<Pk> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let expr_tree = expression::Tree::from_str(s)?;
        Self::from_tree(expr_tree.root())
    }
}

impl<Pk: FromStrKey> crate::expression::FromTree for Tr<Pk> {
    fn from_tree(root: expression::TreeIterItem) -> Result<Self, Error> {
        use crate::expression::{Parens, ParseTreeError};

        root.verify_toplevel("tr", 1..=2)
            .map_err(From::from)
            .map_err(Error::Parse)?;

        let mut root_children = root.children();
        let internal_key: Pk = root_children
            .next()
            .unwrap() // `verify_toplevel` above checked that first child existed
            .verify_terminal("internal key")
            .map_err(Error::Parse)?;

        let tap_tree = match root_children.next() {
            None => return Tr::new(internal_key, None).map_err(Error::Validation),
            Some(tree) => tree,
        };

        let mut tree_builder = taptree::TapTreeBuilder::new();
        let mut tap_tree_iter = tap_tree.pre_order_iter();
        // while let construction needed because we modify the iterator inside the loop
        // (by calling skip_descendants to skip over the contents of the tapscripts).
        while let Some(node) = tap_tree_iter.next() {
            if node.parens() == Parens::Curly {
                if !node.name().is_empty() {
                    return Err(Error::Parse(ParseError::Tree(ParseTreeError::IncorrectName {
                        actual: node.name().to_owned(),
                        expected: "",
                    })));
                }
                node.verify_n_children("taptree branch", 2..=2)
                    .map_err(From::from)
                    .map_err(Error::Parse)?;
                tree_builder.push_inner_node()?;
            } else {
                let script = Miniscript::from_tree(node)?;
                // FIXME hack for https://github.com/rust-bitcoin/rust-miniscript/issues/734
                script
                    .validate(&Tap::CONSENSUS)
                    .map_err(Error::Validation)?;

                tree_builder.push_leaf(script);
                tap_tree_iter.skip_descendants();
            }
        }
        Tr::new(internal_key, Some(tree_builder.finalize())).map_err(Error::Validation)
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Tr<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.tree {
            Some(ref s) => write!(f, "tr({:?},{:?})", self.internal_key, s),
            None => write!(f, "tr({:?})", self.internal_key),
        }
    }
}

impl<Pk: MiniscriptKey> fmt::Display for Tr<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use fmt::Write;
        let mut wrapped_f = checksum::Formatter::new(f);
        let key = &self.internal_key;
        match self.tree {
            Some(ref s) => write!(wrapped_f, "tr({},{})", key, s)?,
            None => write!(wrapped_f, "tr({})", key)?,
        }
        wrapped_f.write_checksum_if_not_alt()
    }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Tr<Pk> {
    fn lift(&self) -> Result<Policy<Pk>, ValidationError> {
        match &self.tree {
            Some(root) => Ok(Policy::Thresh(Threshold::or(
                Arc::new(Policy::Key(self.internal_key.clone())),
                Arc::new(root.lift()?),
            ))),
            None => Ok(Policy::Key(self.internal_key.clone())),
        }
    }
}

impl<Pk: MiniscriptKey> ForEachKey<Pk> for Tr<Pk> {
    fn for_each_key<'a, F: FnMut(&'a Pk) -> bool>(&'a self, mut pred: F) -> bool {
        let script_keys_res = self
            .leaves()
            .all(|leaf| leaf.miniscript().for_each_key(&mut pred));
        script_keys_res && pred(&self.internal_key)
    }
}

// Helper function to compute the len of control block at a given depth
fn control_block_len(depth: u8) -> usize {
    TAPROOT_CONTROL_BASE_SIZE + (depth as usize) * TAPROOT_CONTROL_NODE_SIZE
}

// Helper function to get a script spend satisfaction
// try script spend
fn best_tap_spend<Pk, P>(
    desc: &Tr<Pk>,
    provider: &P,
    allow_mall: bool,
) -> Satisfaction<Placeholder<Pk>>
where
    Pk: ToPublicKey,
    P: AssetProvider<Pk>,
{
    let spend_info = desc.spend_info();
    // First try the key spend path
    if let Some(size) = provider.provider_lookup_tap_key_spend_sig(&desc.internal_key) {
        Satisfaction {
            stack: Witness::Stack(vec![Placeholder::SchnorrSigPk(
                desc.internal_key.clone(),
                SchnorrSigType::KeySpend { merkle_root: spend_info.merkle_root() },
                size,
            )]),
            has_sig: true,
            absolute_timelock: None,
            relative_timelock: None,
        }
    } else {
        // Since we have the complete descriptor we can ignore the satisfier. We don't use the control block
        // map (lookup_control_block) from the satisfier here.
        let mut min_satisfaction = Satisfaction {
            stack: Witness::Unavailable,
            has_sig: false,
            relative_timelock: None,
            absolute_timelock: None,
        };
        let mut min_wit_len = None;
        for leaf in spend_info.leaves() {
            let mut satisfaction = if allow_mall {
                match leaf.miniscript().build_template_mall(provider) {
                    s @ Satisfaction { stack: Witness::Stack(_), .. } => s,
                    _ => continue, // No witness for this script in tr descriptor, look for next one
                }
            } else {
                match leaf.miniscript().build_template(provider) {
                    s @ Satisfaction { stack: Witness::Stack(_), .. } => s,
                    _ => continue, // No witness for this script in tr descriptor, look for next one
                }
            };
            let wit = match satisfaction {
                Satisfaction { stack: Witness::Stack(ref mut wit), .. } => wit,
                _ => unreachable!(),
            };

            let script = ScriptBuf::from(leaf.script());
            let control_block = leaf.control_block().clone();

            wit.push(Placeholder::TapScript(script));
            wit.push(Placeholder::TapControlBlock(control_block));

            let wit_size = witness_size(wit);
            if min_wit_len.is_some() && Some(wit_size) > min_wit_len {
                continue;
            } else {
                min_satisfaction = satisfaction;
                min_wit_len = Some(wit_size);
            }
        }

        min_satisfaction
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::*;

    fn descriptor() -> String {
        let desc = "tr(acc0, {
            multi_a(3, acc10, acc11, acc12), {
              and_v(
                v:multi_a(2, acc10, acc11, acc12),
                after(10)
              ),
              and_v(
                v:multi_a(1, acc10, acc11, ac12),
                after(100)
              )
            }
         })";
        desc.replace(&[' ', '\n'][..], "")
    }

    #[test]
    fn for_each() {
        let desc = descriptor();
        let tr = Tr::<String>::from_str(&desc).unwrap();
        // Note the last ac12 only has ac and fails the predicate
        assert!(!tr.for_each_key(|k| k.starts_with("acc")));
    }

    #[test]
    fn tr_maximum_depth() {
        // Copied from integration tests
        let descriptor128 = "tr(X!,{pk(X1!),{pk(X2!),{pk(X3!),{pk(X4!),{pk(X5!),{pk(X6!),{pk(X7!),{pk(X8!),{pk(X9!),{pk(X10!),{pk(X11!),{pk(X12!),{pk(X13!),{pk(X14!),{pk(X15!),{pk(X16!),{pk(X17!),{pk(X18!),{pk(X19!),{pk(X20!),{pk(X21!),{pk(X22!),{pk(X23!),{pk(X24!),{pk(X25!),{pk(X26!),{pk(X27!),{pk(X28!),{pk(X29!),{pk(X30!),{pk(X31!),{pk(X32!),{pk(X33!),{pk(X34!),{pk(X35!),{pk(X36!),{pk(X37!),{pk(X38!),{pk(X39!),{pk(X40!),{pk(X41!),{pk(X42!),{pk(X43!),{pk(X44!),{pk(X45!),{pk(X46!),{pk(X47!),{pk(X48!),{pk(X49!),{pk(X50!),{pk(X51!),{pk(X52!),{pk(X53!),{pk(X54!),{pk(X55!),{pk(X56!),{pk(X57!),{pk(X58!),{pk(X59!),{pk(X60!),{pk(X61!),{pk(X62!),{pk(X63!),{pk(X64!),{pk(X65!),{pk(X66!),{pk(X67!),{pk(X68!),{pk(X69!),{pk(X70!),{pk(X71!),{pk(X72!),{pk(X73!),{pk(X74!),{pk(X75!),{pk(X76!),{pk(X77!),{pk(X78!),{pk(X79!),{pk(X80!),{pk(X81!),{pk(X82!),{pk(X83!),{pk(X84!),{pk(X85!),{pk(X86!),{pk(X87!),{pk(X88!),{pk(X89!),{pk(X90!),{pk(X91!),{pk(X92!),{pk(X93!),{pk(X94!),{pk(X95!),{pk(X96!),{pk(X97!),{pk(X98!),{pk(X99!),{pk(X100!),{pk(X101!),{pk(X102!),{pk(X103!),{pk(X104!),{pk(X105!),{pk(X106!),{pk(X107!),{pk(X108!),{pk(X109!),{pk(X110!),{pk(X111!),{pk(X112!),{pk(X113!),{pk(X114!),{pk(X115!),{pk(X116!),{pk(X117!),{pk(X118!),{pk(X119!),{pk(X120!),{pk(X121!),{pk(X122!),{pk(X123!),{pk(X124!),{pk(X125!),{pk(X126!),{pk(X127!),{pk(X128!),pk(X129)}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})";
        descriptor128.parse::<crate::Descriptor<String>>().unwrap();

        // Copied from integration tests
        let descriptor129 = "tr(X!,{pk(X1!),{pk(X2!),{pk(X3!),{pk(X4!),{pk(X5!),{pk(X6!),{pk(X7!),{pk(X8!),{pk(X9!),{pk(X10!),{pk(X11!),{pk(X12!),{pk(X13!),{pk(X14!),{pk(X15!),{pk(X16!),{pk(X17!),{pk(X18!),{pk(X19!),{pk(X20!),{pk(X21!),{pk(X22!),{pk(X23!),{pk(X24!),{pk(X25!),{pk(X26!),{pk(X27!),{pk(X28!),{pk(X29!),{pk(X30!),{pk(X31!),{pk(X32!),{pk(X33!),{pk(X34!),{pk(X35!),{pk(X36!),{pk(X37!),{pk(X38!),{pk(X39!),{pk(X40!),{pk(X41!),{pk(X42!),{pk(X43!),{pk(X44!),{pk(X45!),{pk(X46!),{pk(X47!),{pk(X48!),{pk(X49!),{pk(X50!),{pk(X51!),{pk(X52!),{pk(X53!),{pk(X54!),{pk(X55!),{pk(X56!),{pk(X57!),{pk(X58!),{pk(X59!),{pk(X60!),{pk(X61!),{pk(X62!),{pk(X63!),{pk(X64!),{pk(X65!),{pk(X66!),{pk(X67!),{pk(X68!),{pk(X69!),{pk(X70!),{pk(X71!),{pk(X72!),{pk(X73!),{pk(X74!),{pk(X75!),{pk(X76!),{pk(X77!),{pk(X78!),{pk(X79!),{pk(X80!),{pk(X81!),{pk(X82!),{pk(X83!),{pk(X84!),{pk(X85!),{pk(X86!),{pk(X87!),{pk(X88!),{pk(X89!),{pk(X90!),{pk(X91!),{pk(X92!),{pk(X93!),{pk(X94!),{pk(X95!),{pk(X96!),{pk(X97!),{pk(X98!),{pk(X99!),{pk(X100!),{pk(X101!),{pk(X102!),{pk(X103!),{pk(X104!),{pk(X105!),{pk(X106!),{pk(X107!),{pk(X108!),{pk(X109!),{pk(X110!),{pk(X111!),{pk(X112!),{pk(X113!),{pk(X114!),{pk(X115!),{pk(X116!),{pk(X117!),{pk(X118!),{pk(X119!),{pk(X120!),{pk(X121!),{pk(X122!),{pk(X123!),{pk(X124!),{pk(X125!),{pk(X126!),{pk(X127!),{pk(X128!),{pk(X129),pk(X130)}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})";
        assert!(matches!(
            descriptor129
                .parse::<crate::Descriptor::<String>>()
                .unwrap_err(),
            crate::Error::TapTreeDepthError(TapTreeDepthError),
        ));
    }
}
