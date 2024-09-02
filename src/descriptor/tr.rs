// SPDX-License-Identifier: CC0-1.0

use core::{cmp, fmt, hash};

#[cfg(not(test))] // https://github.com/rust-lang/rust/issues/121684
use bitcoin::secp256k1;
use bitcoin::taproot::{
    LeafVersion, TaprootBuilder, TaprootSpendInfo, TAPROOT_CONTROL_BASE_SIZE,
    TAPROOT_CONTROL_MAX_NODE_COUNT, TAPROOT_CONTROL_NODE_SIZE,
};
use bitcoin::{opcodes, Address, Network, ScriptBuf, Weight};
use sync::Arc;

use super::checksum;
use crate::descriptor::DefiniteDescriptorKey;
use crate::expression::{self, FromTree};
use crate::miniscript::satisfy::{Placeholder, Satisfaction, SchnorrSigType, Witness};
use crate::miniscript::Miniscript;
use crate::plan::AssetProvider;
use crate::policy::semantic::Policy;
use crate::policy::Liftable;
use crate::prelude::*;
use crate::util::{varint_len, witness_size};
use crate::{
    Error, ForEachKey, FromStrKey, MiniscriptKey, ParseError, Satisfier, ScriptContext, Tap,
    Threshold, ToPublicKey, TranslateErr, Translator,
};

/// A Taproot Tree representation.
// Hidden leaves are not yet supported in descriptor spec. Conceptually, it should
// be simple to integrate those here, but it is best to wait on core for the exact syntax.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum TapTree<Pk: MiniscriptKey> {
    /// A taproot tree structure
    Tree {
        /// Left tree branch.
        left: Arc<TapTree<Pk>>,
        /// Right tree branch.
        right: Arc<TapTree<Pk>>,
        /// Tree height, defined as `1 + max(left_height, right_height)`.
        height: usize,
    },
    /// A taproot leaf denoting a spending condition
    // A new leaf version would require a new Context, therefore there is no point
    // in adding a LeafVersion with Leaf type here. All Miniscripts right now
    // are of Leafversion::default
    Leaf(Arc<Miniscript<Pk, Tap>>),
}

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
    spend_info: Mutex<Option<Arc<TaprootSpendInfo>>>,
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

impl<Pk: MiniscriptKey> TapTree<Pk> {
    /// Creates a `TapTree` by combining `left` and `right` tree nodes.
    pub fn combine(left: TapTree<Pk>, right: TapTree<Pk>) -> Self {
        let height = 1 + cmp::max(left.height(), right.height());
        TapTree::Tree { left: Arc::new(left), right: Arc::new(right), height }
    }

    /// Returns the height of this tree.
    pub fn height(&self) -> usize {
        match *self {
            TapTree::Tree { left: _, right: _, height } => height,
            TapTree::Leaf(..) => 0,
        }
    }

    /// Iterates over all miniscripts in DFS walk order compatible with the
    /// PSBT requirements (BIP 371).
    pub fn iter(&self) -> TapTreeIter<Pk> { TapTreeIter { stack: vec![(0, self)] } }

    // Helper function to translate keys
    fn translate_helper<T>(&self, t: &mut T) -> Result<TapTree<T::TargetPk>, TranslateErr<T::Error>>
    where
        T: Translator<Pk>,
    {
        let frag = match *self {
            TapTree::Tree { ref left, ref right, ref height } => TapTree::Tree {
                left: Arc::new(left.translate_helper(t)?),
                right: Arc::new(right.translate_helper(t)?),
                height: *height,
            },
            TapTree::Leaf(ref ms) => TapTree::Leaf(Arc::new(ms.translate_pk(t)?)),
        };
        Ok(frag)
    }
}

impl<Pk: MiniscriptKey> fmt::Display for TapTree<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TapTree::Tree { ref left, ref right, height: _ } => {
                write!(f, "{{{},{}}}", *left, *right)
            }
            TapTree::Leaf(ref script) => write!(f, "{}", *script),
        }
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for TapTree<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TapTree::Tree { ref left, ref right, height: _ } => {
                write!(f, "{{{:?},{:?}}}", *left, *right)
            }
            TapTree::Leaf(ref script) => write!(f, "{:?}", *script),
        }
    }
}

impl<Pk: MiniscriptKey> Tr<Pk> {
    /// Create a new [`Tr`] descriptor from internal key and [`TapTree`]
    pub fn new(internal_key: Pk, tree: Option<TapTree<Pk>>) -> Result<Self, Error> {
        Tap::check_pk(&internal_key)?;
        let nodes = tree.as_ref().map(|t| t.height()).unwrap_or(0);

        if nodes <= TAPROOT_CONTROL_MAX_NODE_COUNT {
            Ok(Self { internal_key, tree, spend_info: Mutex::new(None) })
        } else {
            Err(Error::MaxRecursiveDepthExceeded)
        }
    }

    /// Obtain the internal key of [`Tr`] descriptor
    pub fn internal_key(&self) -> &Pk { &self.internal_key }

    /// Obtain the [`TapTree`] of the [`Tr`] descriptor
    pub fn tap_tree(&self) -> &Option<TapTree<Pk>> { &self.tree }

    /// Obtain the [`TapTree`] of the [`Tr`] descriptor
    #[deprecated(since = "11.0.0", note = "use tap_tree instead")]
    pub fn taptree(&self) -> &Option<TapTree<Pk>> { self.tap_tree() }

    /// Iterate over all scripts in merkle tree. If there is no script path, the iterator
    /// yields [`None`]
    pub fn iter_scripts(&self) -> TapTreeIter<Pk> {
        match self.tree {
            Some(ref t) => t.iter(),
            None => TapTreeIter { stack: vec![] },
        }
    }

    /// Compute the [`TaprootSpendInfo`] associated with this descriptor if spend data is `None`.
    ///
    /// If spend data is already computed (i.e it is not `None`), this does not recompute it.
    ///
    /// [`TaprootSpendInfo`] is only required for spending via the script paths.
    pub fn spend_info(&self) -> Arc<TaprootSpendInfo>
    where
        Pk: ToPublicKey,
    {
        // If the value is already cache, read it
        // read only panics if the lock is poisoned (meaning other thread having a lock panicked)
        let read_lock = self.spend_info.lock().expect("Lock poisoned");
        if let Some(ref spend_info) = *read_lock {
            return Arc::clone(spend_info);
        }
        drop(read_lock);

        // Get a new secp context
        // This would be cheap operation after static context support from upstream
        let secp = secp256k1::Secp256k1::verification_only();
        // Key spend path with no merkle root
        let data = if self.tree.is_none() {
            TaprootSpendInfo::new_key_spend(&secp, self.internal_key.to_x_only_pubkey(), None)
        } else {
            let mut builder = TaprootBuilder::new();
            for (depth, ms) in self.iter_scripts() {
                let script = ms.encode();
                builder = builder
                    .add_leaf(depth, script)
                    .expect("Computing spend data on a valid Tree should always succeed");
            }
            // Assert builder cannot error here because we have a well formed descriptor
            match builder.finalize(&secp, self.internal_key.to_x_only_pubkey()) {
                Ok(data) => data,
                Err(_) => unreachable!("We know the builder can be finalized"),
            }
        };
        let spend_info = Arc::new(data);
        *self.spend_info.lock().expect("Lock poisoned") = Some(Arc::clone(&spend_info));
        spend_info
    }

    /// Checks whether the descriptor is safe.
    pub fn sanity_check(&self) -> Result<(), Error> {
        for (_depth, ms) in self.iter_scripts() {
            ms.sanity_check()?;
        }
        Ok(())
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
            .iter()
            .filter_map(|(depth, ms)| {
                let script_size = ms.script_size();
                let max_sat_elems = ms.max_satisfaction_witness_elements().ok()?;
                let max_sat_size = ms.max_satisfaction_size().ok()?;
                let control_block_size = control_block_len(depth);

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

        tree.iter()
            .filter_map(|(depth, ms)| {
                let script_size = ms.script_size();
                let max_sat_elems = ms.max_satisfaction_witness_elements().ok()?;
                let max_sat_size = ms.max_satisfaction_size().ok()?;
                let control_block_size = control_block_len(depth);
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
            Some(tree) => Some(tree.translate_helper(translate)?),
            None => None,
        };
        let translate_desc =
            Tr::new(translate.pk(&self.internal_key)?, tree).map_err(TranslateErr::OuterError)?;
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

/// Iterator for Taproot structures
/// Yields a pair of (depth, miniscript) in a depth first walk
/// For example, this tree:
///                                     - N0 -
///                                    /     \\
///                                   N1      N2
///                                  /  \    /  \\
///                                 A    B  C   N3
///                                            /  \\
///                                           D    E
/// would yield (2, A), (2, B), (2,C), (3, D), (3, E).
///
#[derive(Debug, Clone)]
pub struct TapTreeIter<'a, Pk: MiniscriptKey> {
    stack: Vec<(u8, &'a TapTree<Pk>)>,
}

impl<Pk: MiniscriptKey> TapTreeIter<'_, Pk> {
    /// Helper function to return an empty iterator from Descriptor::tap_tree_iter.
    pub(super) fn empty() -> Self { Self { stack: vec![] } }
}

impl<'a, Pk> Iterator for TapTreeIter<'a, Pk>
where
    Pk: MiniscriptKey + 'a,
{
    type Item = (u8, &'a Miniscript<Pk, Tap>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((depth, last)) = self.stack.pop() {
            match *last {
                TapTree::Tree { ref left, ref right, height: _ } => {
                    self.stack.push((depth + 1, right));
                    self.stack.push((depth + 1, left));
                }
                TapTree::Leaf(ref ms) => return Some((depth, ms)),
            }
        }
        None
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

        struct TreeStack<'s, Pk: MiniscriptKey> {
            inner: Vec<(expression::TreeIterItem<'s>, TapTree<Pk>)>,
        }

        impl<'s, Pk: MiniscriptKey> TreeStack<'s, Pk> {
            fn new() -> Self { Self { inner: Vec::with_capacity(128) } }

            fn push(&mut self, parent: expression::TreeIterItem<'s>, tree: TapTree<Pk>) {
                let mut next_push = (parent, tree);
                while let Some(top) = self.inner.pop() {
                    if next_push.0.index() == top.0.index() {
                        next_push.0 = top.0.parent().unwrap();
                        next_push.1 = TapTree::combine(top.1, next_push.1);
                    } else {
                        self.inner.push(top);
                        break;
                    }
                }
                self.inner.push(next_push);
            }

            fn pop_final(&mut self) -> Option<TapTree<Pk>> {
                assert_eq!(self.inner.len(), 1);
                self.inner.pop().map(|x| x.1)
            }
        }

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
            None => return Tr::new(internal_key, None),
            Some(tree) => tree,
        };

        let mut tree_stack = TreeStack::new();
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
            } else {
                let script = Miniscript::from_tree(node)?;
                // FIXME hack for https://github.com/rust-bitcoin/rust-miniscript/issues/734
                if script.ty.corr.base != crate::miniscript::types::Base::B {
                    return Err(Error::NonTopLevel(format!("{:?}", script)));
                };

                tree_stack.push(node.parent().unwrap(), TapTree::Leaf(Arc::new(script)));
                tap_tree_iter.skip_descendants();
            }
        }
        Tr::new(internal_key, tree_stack.pop_final())
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

impl<Pk: MiniscriptKey> Liftable<Pk> for TapTree<Pk> {
    fn lift(&self) -> Result<Policy<Pk>, Error> {
        fn lift_helper<Pk: MiniscriptKey>(s: &TapTree<Pk>) -> Result<Policy<Pk>, Error> {
            match *s {
                TapTree::Tree { ref left, ref right, height: _ } => Ok(Policy::Thresh(
                    Threshold::or(Arc::new(lift_helper(left)?), Arc::new(lift_helper(right)?)),
                )),
                TapTree::Leaf(ref leaf) => leaf.lift(),
            }
        }

        let pol = lift_helper(self)?;
        Ok(pol.normalized())
    }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Tr<Pk> {
    fn lift(&self) -> Result<Policy<Pk>, Error> {
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
            .iter_scripts()
            .all(|(_d, ms)| ms.for_each_key(&mut pred));
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
        for (_depth, ms) in desc.iter_scripts() {
            let mut satisfaction = if allow_mall {
                match ms.build_template(provider) {
                    s @ Satisfaction { stack: Witness::Stack(_), .. } => s,
                    _ => continue, // No witness for this script in tr descriptor, look for next one
                }
            } else {
                match ms.build_template_mall(provider) {
                    s @ Satisfaction { stack: Witness::Stack(_), .. } => s,
                    _ => continue, // No witness for this script in tr descriptor, look for next one
                }
            };
            let wit = match satisfaction {
                Satisfaction { stack: Witness::Stack(ref mut wit), .. } => wit,
                _ => unreachable!(),
            };

            let leaf_script = (ms.encode(), LeafVersion::TapScript);
            let control_block = spend_info
                .control_block(&leaf_script)
                .expect("Control block must exist in script map for every known leaf");

            wit.push(Placeholder::TapScript(leaf_script.0));
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
    fn height() {
        let desc = descriptor();
        let tr = Tr::<String>::from_str(&desc).unwrap();
        assert_eq!(tr.tap_tree().as_ref().unwrap().height(), 2);
    }
}
