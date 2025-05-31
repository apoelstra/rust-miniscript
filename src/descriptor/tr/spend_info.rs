// SPDX-License-Identifier: CC0-1.0

//! Taproot Spending Information
//!
//! Provides a structure which can be used to obtain control blocks and other information
//! needed for Taproot spends.
//!

use bitcoin::key::{Parity, TapTweak as _, TweakedPublicKey, UntweakedPublicKey};
use bitcoin::secp256k1::Secp256k1;
use bitcoin::taproot::{ControlBlock, LeafVersion, TapLeafHash, TapNodeHash, TaprootMerkleBranch};
use bitcoin::{Script, ScriptBuf};

use crate::miniscript::context::Tap;
use crate::prelude::Vec;
use crate::sync::Arc;
use crate::{Miniscript, MiniscriptKey, ToPublicKey};

/// Utility structure which maintains a stack of bits (at most 128) using a u128.
///
/// Will panic if the user attempts to push more than 128 bits; we assume in this
/// module that we are starting with a validated [`super::TapTree`] and therefore
/// that this can't happen.
#[derive(Default)]
struct BitStack128 {
    inner: u128,
    height: u8,
}

impl BitStack128 {
    fn push(&mut self, bit: bool) {
        if bit {
            self.inner |= 1u128 << self.height;
        } else {
            self.inner &= !(1u128 << self.height);
        }
        self.height += 1;
    }

    fn pop(&mut self) -> Option<bool> {
        if self.height > 0 {
            self.height -= 1;
            Some(self.inner & (1u128 << self.height) != 0)
        } else {
            None
        }
    }
}

/// A structure which can be used to obtain control blocks and other information
/// needed for Taproot spends.
///
/// Conceptually, this object is a copy of the Taproot tree with each leave annotated
/// with extra information that can be used to compute its control block.
pub struct TrSpendInfo<Pk: MiniscriptKey> {
    internal_key: UntweakedPublicKey,
    output_key: TweakedPublicKey,
    output_key_parity: Parity,
    /// The nodes of the tree, in pre-order, i.e. left-to-right depth-first order.
    nodes: Vec<TrSpendInfoNode<Pk>>,
}

impl<Pk: ToPublicKey> TrSpendInfo<Pk> {
    fn nodes_from_tap_tree(tree: &super::TapTree<Pk>) -> Vec<TrSpendInfoNode<Pk>> {
        let mut nodes = vec![];
        let mut parent_stack = Vec::with_capacity(128); // FIXME use ArrayVec here
        for leaf in tree.leaves() {
            let depth = usize::from(leaf.depth());
            let script = leaf.miniscript().encode();

            let leaf_hash = TapLeafHash::from_script(&script, leaf.leaf_version());
            let mut current_hash = TapNodeHash::from(leaf_hash);

            // 1. If this node increases our depth, add parents.
            while parent_stack.len() < depth {
                // When we encounter a leaf we put all of its parent nodes into the
                // result. We set the "sibling hash" to a dummy value (specifically,
                // `current_hash`, because it's convenient and the right type).
                parent_stack.push((false, nodes.len()));
                nodes.push(TrSpendInfoNode { sibling_hash: current_hash, leaf_data: None });
            }
            // If parent_stack.len() < depth then we pushed things onto the stack in
            // the previous step so that we now have equality. Meanwhile, it is
            // impossible for parent_stack.len() > depth because we pop things off
            // the stack in step 3 below.
            assert_eq!(depth, parent_stack.len());

            // 2. Add the node.
            //
            // Again, we don't know the sibling hash yet so we use the current hash.
            // But this time the current hash isn't an arbitrary dummy value -- in the
            // next step we will have an invariant that incomplete nodes' "sibling hashes"
            // are set to the nodes' own hashes.
            //
            // We will use this hash to compute the parent's hash then replace it with
            // the actual sibling hash. We do this for every node EXCEPT the root node,
            // whose "sibling hash" will then wind up being equal to the Merkle root
            // of the whole tree.
            nodes.push(TrSpendInfoNode {
                sibling_hash: current_hash,
                leaf_data: Some(LeafData {
                    script,
                    miniscript: Arc::clone(leaf.miniscript()),
                    leaf_hash,
                }),
            });

            // 3. Recursively complete nodes as long as we are on a right branch.
            //
            // As described above, for each parent node, we compute its hash and store it
            // in `sibling_hash`. At that point we're done with the childrens' hashes so
            // we finally replace those with their sibling hashes.
            let mut cur_index = nodes.len() - 1;
            while let Some((done_left_child, parent_idx)) = parent_stack.pop() {
                if done_left_child {
                    let lchild_hash = nodes[parent_idx + 1].sibling_hash;
                    // Set current node's "sibling hash" to its own hash.
                    let new_merkle_root = TapNodeHash::from_node_hashes(lchild_hash, current_hash);
                    nodes[parent_idx].sibling_hash = new_merkle_root;
                    // Set the children's sibling hashes to each others' hashes.
                    nodes[parent_idx + 1].sibling_hash = current_hash;
                    nodes[cur_index].sibling_hash = lchild_hash;
                    // Recurse.
                    current_hash = new_merkle_root;
                    cur_index = parent_idx;
                } else {
                    // Once we hit a left branch we can't do anything until we see the next leaf.
                    parent_stack.push((true, parent_idx));
                    break;
                }
            }
        }
        debug_assert_eq!(parent_stack.len(), 0);
        debug_assert_ne!(nodes.len(), 0);

        nodes
    }

    /// Constructs a [`TrSpendInfo`] for a [`super::Tr`].
    pub fn from_tr(tr: &super::Tr<Pk>) -> Self {
        let internal_key = tr.internal_key().to_x_only_pubkey();

        let nodes = match tr.tap_tree() {
            Some(tree) => Self::nodes_from_tap_tree(tree),
            None => vec![],
        };

        let secp = Secp256k1::verification_only();
        let (output_key, output_key_parity) =
            internal_key.tap_tweak(&secp, nodes.first().map(|node| node.sibling_hash));

        TrSpendInfo { internal_key, output_key, output_key_parity, nodes }
    }

    /// If this [`TrSpendInfo`] has an associated Taproot tree, return its Merkle root.
    pub fn merkle_root(&self) -> Option<TapNodeHash> {
        // As described in `nodes_from_tap_tree`, the "sibling hash" of the root node
        // is actually the Merkle root of the whole tree.
        self.nodes.first().map(|node| node.sibling_hash)
    }

    /// The internal key of the Taproot output.
    ///
    /// This returns the x-only public key which appears on-chain. For the abstroct
    /// public key, use the `internal_key` method on the original [`super::Tr`] used to
    /// create this object.
    pub fn internal_key(&self) -> UntweakedPublicKey { self.internal_key }

    // I don't really like these names, but they're used in rust-bitcoin so we'll stick
    // with them and just doc-alias them to better names so they show up in search results.
    /// The external key of the Taproot output.
    #[doc(alias = "external_key")]
    pub fn output_key(&self) -> TweakedPublicKey { self.output_key }

    /// The parity of the external key of the Taproot output.
    #[doc(alias = "external_key_parity")]
    pub fn output_key_parity(&self) -> Parity { self.output_key_parity }

    /// An iterator over the leaves of the Taptree.
    ///
    /// This yields the same leaves in the same order as [`super::Tr::leaves`] on the original
    /// [`super::Tr`]. However, in addition to yielding the leaves and their depths, it also
    /// yields their scripts, leafhashes, and control blocks.
    pub fn leaves(&self) -> TrSpendInfoIter<'_, Pk> {
        TrSpendInfoIter {
            spend_info: self,
            index: 0,
            merkle_stack: Vec::with_capacity(128),
            done_left_stack: BitStack128::default(),
        }
    }

    /// If the Taproot tree is not keyspend-only, converts it to a [`bitcoin::taproot::TapTree`] structure.
    ///
    /// This conversion is not particularly efficient but the resulting data structure is
    /// useful for interacting with PSBTs.
    pub fn to_tap_tree(&self) -> Option<bitcoin::taproot::TapTree> {
        if self.nodes.is_empty() {
            return None;
        }

        let mut builder = bitcoin::taproot::TaprootBuilder::new();
        for leaf in self.leaves() {
            builder = builder
                .add_leaf_with_ver(
                    leaf.depth(),
                    ScriptBuf::from(leaf.script()),
                    leaf.leaf_version(),
                )
                .expect("iterating through tree in correct DFS order")
        }
        Some(bitcoin::taproot::TapTree::try_from(builder).expect("tree is complete"))
    }
}

/// An internal node of the spend
#[derive(Debug)]
struct TrSpendInfoNode<Pk: MiniscriptKey> {
    sibling_hash: TapNodeHash,
    leaf_data: Option<LeafData<Pk>>,
}

#[derive(Debug)]
struct LeafData<Pk: MiniscriptKey> {
    script: ScriptBuf,
    miniscript: Arc<Miniscript<Pk, Tap>>,
    leaf_hash: TapLeafHash,
}

/// An iterator over the leaves of a Taproot tree. Produced by [`TrSpendInfo::leaves`].
///
/// This is conceptually similar to [`super::TapTreeIter`], which can be obtained by
/// calling [`super::TapTree::leaves`]. That iterator goes over the leaves of the tree,
/// yielding the Miniscripts of the leaves and their depth.
///
/// This iterator goes over the leaves in the same order, yielding the data that actually
/// goes on chain: their scripts, control blocks, etc.
pub struct TrSpendInfoIter<'sp, Pk: MiniscriptKey> {
    spend_info: &'sp TrSpendInfo<Pk>,
    index: usize,
    merkle_stack: Vec<TapNodeHash>,
    done_left_stack: BitStack128,
}

impl<'sp, Pk: MiniscriptKey> Iterator for TrSpendInfoIter<'sp, Pk> {
    type Item = TrSpendInfoIterItem<'sp, Pk>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.index < self.spend_info.nodes.len() {
            let current_node = &self.spend_info.nodes[self.index];
            if self.index > 0 {
                self.merkle_stack.push(current_node.sibling_hash);
            }
            self.index += 1;

            if let Some(ref leaf) = current_node.leaf_data {
                // leaf
                let mut merkle_stack = self.merkle_stack.clone();
                merkle_stack.reverse();
                self.merkle_stack.pop();

                loop {
                    match self.done_left_stack.pop() {
                        None => break, // this leaf is the root node
                        Some(false) => {
                            self.done_left_stack.push(true);
                            break;
                        }
                        Some(true) => {
                            self.merkle_stack.pop();
                        }
                    }
                }

                return Some(TrSpendInfoIterItem {
                    script: &leaf.script,
                    miniscript: &leaf.miniscript,
                    leaf_hash: leaf.leaf_hash,
                    control_block: ControlBlock {
                        leaf_version: LeafVersion::TapScript,
                        output_key_parity: self.spend_info.output_key_parity,
                        internal_key: self.spend_info.internal_key,
                        merkle_branch: TaprootMerkleBranch::try_from(merkle_stack)
                            .expect("merkle stack guaranteed to be within allowable length"),
                    },
                });
            } else {
                // internal node
                self.done_left_stack.push(false);
            }
        }
        None
    }
}

/// Item yielded from a [`TrSpendInfoIter`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TrSpendInfoIterItem<'tr, Pk: MiniscriptKey> {
    script: &'tr Script,
    miniscript: &'tr Arc<Miniscript<Pk, Tap>>,
    leaf_hash: TapLeafHash,
    control_block: ControlBlock,
}

impl<'sp, Pk: MiniscriptKey> TrSpendInfoIterItem<'sp, Pk> {
    /// The Tapscript of this leaf.
    #[inline]
    pub fn script(&self) -> &'sp Script { self.script }

    /// The Tapscript of this leaf, in Miniscript form.
    #[inline]
    pub fn miniscript(&self) -> &'sp Arc<Miniscript<Pk, Tap>> { self.miniscript }

    /// The depth of the leaf in the tree.
    ///
    /// This value is returned as `u8` since it is guaranteed to be <= 128 by the Taproot
    /// consensus rules.
    #[inline]
    pub fn depth(&self) -> u8 {
        self.control_block.merkle_branch.len() as u8 // cast ok, length limited to 128
    }

    /// The Tapleaf version of this leaf.
    ///
    /// This function returns a constant value, since there is only one version in use
    /// on the Bitcoin network; however, it may be useful to use this method in case
    /// you wish to be forward-compatible with future versions supported by this
    /// library.
    #[inline]
    pub fn leaf_version(&self) -> LeafVersion { self.control_block.leaf_version }

    /// The hash of this leaf.
    ///
    /// This hash, prefixed with the leaf's [`Self::leaf_version`], is what is directly
    /// committed in the Taproot tree.
    #[inline]
    pub fn leaf_hash(&self) -> TapLeafHash { self.leaf_hash }

    /// The control block of this leaf.
    ///
    /// Unlike the other data obtainable from [`TrSpendInfoIterItem`], this one is computed
    /// dynamically during iteration and therefore will not outlive the iterator item. See
    /// [`Self::into_control_block`], which consumes the iterator item but will give you an
    /// owned copy of the control block.
    ///
    /// If you need access to multiple control blocks at once, you may need to `clone` the
    /// return value of this method, or call [`Self::into_control_block`], and store the
    /// result in a separate container.
    #[inline]
    pub fn control_block(&self) -> &ControlBlock { &self.control_block }

    /// Extract the control block of this leaf, consuming `self`.
    #[inline]
    pub fn into_control_block(self) -> ControlBlock { self.control_block }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor::Tr;
    use crate::ScriptContext;

    #[derive(PartialEq, Eq, Debug)]
    struct ExpectedTree {
        internal_key: UntweakedPublicKey,
        output_key: TweakedPublicKey,
        output_key_parity: Parity,
        merkle_root: Option<TapNodeHash>,
    }

    #[derive(PartialEq, Eq, Debug)]
    struct ExpectedLeaf {
        leaf_hash: TapLeafHash,
        branch: TaprootMerkleBranch,
    }

    fn test_cases() -> Vec<(String, ExpectedTree, Vec<ExpectedLeaf>)> {
        let secp = Secp256k1::verification_only();
        let pk = "03cc8a4bc64d897bddc5fbc2f670f7a8ba0b386779106cf1223c6fc5d7cd6fc115"
            .parse::<bitcoin::PublicKey>()
            .unwrap();

        // Hash of the FALSE script
        let zero_hash = "e7e4d593fcb72926eedbe0d1e311f41acd6f6ef161dcba081a75168ec4dcd379"
            .parse::<TapLeafHash>()
            .unwrap();
        // Hash of the TRUE script
        let one_hash = "a85b2107f791b26a84e7586c28cec7cb61202ed3d01944d832500f363782d675"
            .parse::<TapLeafHash>()
            .unwrap();

        let mut ret = vec![];

        // Empty tree
        let merkle_root = None;
        let internal_key = pk.to_x_only_pubkey();
        let (output_key, output_key_parity) = internal_key.tap_tweak(&secp, merkle_root);
        ret.push((
            format!("tr({pk})"),
            ExpectedTree { internal_key, output_key, output_key_parity, merkle_root },
            vec![],
        ));

        // Single-leaf tree
        let merkle_root = Some(TapNodeHash::from(zero_hash));
        let internal_key = pk.to_x_only_pubkey();
        let (output_key, output_key_parity) = internal_key.tap_tweak(&secp, merkle_root);
        ret.push((
            format!("tr({pk},0)"),
            ExpectedTree { internal_key, output_key, output_key_parity, merkle_root },
            vec![ExpectedLeaf {
                leaf_hash: zero_hash,
                branch: TaprootMerkleBranch::try_from(vec![]).unwrap(),
            }],
        ));

        // Two-leaf tree, repeated leaf
        let merkle_root = Some(
            "e3208df58f4fae78044357451c8830698300cd7da47cf41957d82ac4ce1dd170"
                .parse()
                .unwrap(),
        );
        let internal_key = pk.to_x_only_pubkey();
        let (output_key, output_key_parity) = internal_key.tap_tweak(&secp, merkle_root);
        ret.push((
            format!("tr({pk},{{0,0}})"),
            ExpectedTree { internal_key, output_key, output_key_parity, merkle_root },
            vec![
                ExpectedLeaf {
                    leaf_hash: zero_hash,
                    branch: TaprootMerkleBranch::try_from(vec![TapNodeHash::from(zero_hash)])
                        .unwrap(),
                },
                ExpectedLeaf {
                    leaf_hash: zero_hash,
                    branch: TaprootMerkleBranch::try_from(vec![TapNodeHash::from(zero_hash)])
                        .unwrap(),
                },
            ],
        ));

        // Two-leaf tree, non-repeated leaf
        let merkle_root = Some(
            "15526cd6108b4765640abe555e75f4bd11d9b1453b9db4cd36cf4189577a6f63"
                .parse()
                .unwrap(),
        );
        let internal_key = pk.to_x_only_pubkey();
        let (output_key, output_key_parity) = internal_key.tap_tweak(&secp, merkle_root);
        ret.push((
            format!("tr({pk},{{0,1}})"),
            ExpectedTree { internal_key, output_key, output_key_parity, merkle_root },
            vec![
                ExpectedLeaf {
                    leaf_hash: zero_hash,
                    branch: TaprootMerkleBranch::try_from(vec![TapNodeHash::from(one_hash)])
                        .unwrap(),
                },
                ExpectedLeaf {
                    leaf_hash: one_hash,
                    branch: TaprootMerkleBranch::try_from(vec![TapNodeHash::from(zero_hash)])
                        .unwrap(),
                },
            ],
        ));

        // Fuzz test vector 1
        let merkle_root = Some(
            "d281962c67932b82e19b0da5ea437af316213e24509be0ef1bd7c5ee2b460d79"
                .parse()
                .unwrap(),
        );
        let internal_key = pk.to_x_only_pubkey();
        let (output_key, output_key_parity) = internal_key.tap_tweak(&secp, merkle_root);

        ret.push((
            format!("tr({pk},{{0,{{0,tv:0}}}})"),
            ExpectedTree { internal_key, output_key, output_key_parity, merkle_root },
            vec![
                ExpectedLeaf {
                    leaf_hash: zero_hash,
                    branch: TaprootMerkleBranch::try_from(vec![
                        "573d619569d58a36b52187e56f168650ac17f66a9a3afaf054900a04001019b3"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                    ])
                    .unwrap(),
                },
                ExpectedLeaf {
                    leaf_hash: zero_hash,
                    branch: TaprootMerkleBranch::try_from(vec![
                        "64ac241466a5e7032586718ff7465716f77a88d89946ce472daa4c3d0b81148f"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                        TapNodeHash::from(zero_hash),
                    ])
                    .unwrap(),
                },
                ExpectedLeaf {
                    leaf_hash: "64ac241466a5e7032586718ff7465716f77a88d89946ce472daa4c3d0b81148f"
                        .parse()
                        .unwrap(),
                    branch: TaprootMerkleBranch::try_from(vec![
                        TapNodeHash::from(zero_hash),
                        TapNodeHash::from(zero_hash),
                    ])
                    .unwrap(),
                },
            ],
        ));

        // Fuzz test vector 2
        let merkle_root = Some(
            "2534e94c6ad06281b61fff86bad38a3911fb13436fb27fed6f5c057e4a71a911"
                .parse()
                .unwrap(),
        );
        let internal_key = pk.to_x_only_pubkey();
        let (output_key, output_key_parity) = internal_key.tap_tweak(&secp, merkle_root);

        ret.push((
            format!("tr({pk},{{uuu:0,{{0,uu:0}}}})"),
            ExpectedTree { internal_key, output_key, output_key_parity, merkle_root },
            vec![
                ExpectedLeaf {
                    leaf_hash: "6498e1d56640a272493d1d87549f3347dc448ca674556a2110cdfe100e3c238b"
                        .parse()
                        .unwrap(),
                    branch: TaprootMerkleBranch::try_from(vec![
                        "7e3e98bab404812c8eebd21c5d825527676b8e9f261f7ad479f3a08a83a43fb4"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                    ])
                    .unwrap(),
                },
                ExpectedLeaf {
                    leaf_hash: zero_hash,
                    branch: TaprootMerkleBranch::try_from(vec![
                        "19417c32bc6ca7e0f6e65b006ac305107c6add73c8bef31181037e6faaa55e7f"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                        "6498e1d56640a272493d1d87549f3347dc448ca674556a2110cdfe100e3c238b"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                    ])
                    .unwrap(),
                },
                ExpectedLeaf {
                    leaf_hash: "19417c32bc6ca7e0f6e65b006ac305107c6add73c8bef31181037e6faaa55e7f"
                        .parse()
                        .unwrap(),
                    branch: TaprootMerkleBranch::try_from(vec![
                        TapNodeHash::from(zero_hash),
                        "6498e1d56640a272493d1d87549f3347dc448ca674556a2110cdfe100e3c238b"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                    ])
                    .unwrap(),
                },
            ],
        ));

        // Fuzz test vector 3
        let merkle_root = Some(
            "9f4bc03c65a88ffbbb3a8d4fe5e01be608109d9f875f35685d8865e181def26e"
                .parse()
                .unwrap(),
        );
        let internal_key = pk.to_x_only_pubkey();
        let (output_key, output_key_parity) = internal_key.tap_tweak(&secp, merkle_root);

        ret.push((
            format!("tr({pk},{{{{0,{{uuu:0,0}}}},{{0,uu:0}}}})"),
            ExpectedTree { internal_key, output_key, output_key_parity, merkle_root },
            vec![
                ExpectedLeaf {
                    leaf_hash: zero_hash,
                    branch: TaprootMerkleBranch::try_from(vec![
                        "57e3b7d414075ff4864deec9efa99db4462c038706306e02c58e02e957c8a51e"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                        "7e3e98bab404812c8eebd21c5d825527676b8e9f261f7ad479f3a08a83a43fb4"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                    ])
                    .unwrap(),
                },
                ExpectedLeaf {
                    leaf_hash: "6498e1d56640a272493d1d87549f3347dc448ca674556a2110cdfe100e3c238b"
                        .parse()
                        .unwrap(),
                    branch: TaprootMerkleBranch::try_from(vec![
                        TapNodeHash::from(zero_hash),
                        TapNodeHash::from(zero_hash),
                        "7e3e98bab404812c8eebd21c5d825527676b8e9f261f7ad479f3a08a83a43fb4"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                    ])
                    .unwrap(),
                },
                ExpectedLeaf {
                    leaf_hash: zero_hash,
                    branch: TaprootMerkleBranch::try_from(vec![
                        "6498e1d56640a272493d1d87549f3347dc448ca674556a2110cdfe100e3c238b"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                        TapNodeHash::from(zero_hash),
                        "7e3e98bab404812c8eebd21c5d825527676b8e9f261f7ad479f3a08a83a43fb4"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                    ])
                    .unwrap(),
                },
                ExpectedLeaf {
                    leaf_hash: zero_hash,
                    branch: TaprootMerkleBranch::try_from(vec![
                        "19417c32bc6ca7e0f6e65b006ac305107c6add73c8bef31181037e6faaa55e7f"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                        "e034d7d8b221034861bf3893c63cb0ff60d28a7a00090d0dc57c26fec91983cb"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                    ])
                    .unwrap(),
                },
                ExpectedLeaf {
                    leaf_hash: "19417c32bc6ca7e0f6e65b006ac305107c6add73c8bef31181037e6faaa55e7f"
                        .parse()
                        .unwrap(),
                    branch: TaprootMerkleBranch::try_from(vec![
                        TapNodeHash::from(zero_hash),
                        "e034d7d8b221034861bf3893c63cb0ff60d28a7a00090d0dc57c26fec91983cb"
                            .parse::<TapNodeHash>()
                            .unwrap(),
                    ])
                    .unwrap(),
                },
            ],
        ));

        ret
    }

    #[test]
    fn spend_info_fixed_vectors() {
        for (s, tree, leaves) in test_cases() {
            let tr = Tr::<bitcoin::PublicKey>::from_str_with_params(&s, &Tap::CONSENSUS).unwrap();
            let spend_info = tr.spend_info();

            assert_eq!(
                spend_info.internal_key(),
                tree.internal_key,
                "internal key mismatch (left: computed, right: expected)",
            );
            assert_eq!(
                spend_info.merkle_root(),
                tree.merkle_root,
                "merkle root mismatch (left: computed, right: expected)",
            );
            assert_eq!(
                spend_info.output_key(),
                tree.output_key,
                "output key mismatch (left: computed, right: expected)",
            );

            let got_leaves: Vec<_> = spend_info
                .leaves()
                .map(|leaf| ExpectedLeaf {
                    leaf_hash: leaf.leaf_hash(),
                    branch: leaf.control_block().merkle_branch.clone(),
                })
                .collect();
            assert_eq!(got_leaves, leaves, "leaves mismatch (left: computed, right: expected)",);
        }
    }
}
