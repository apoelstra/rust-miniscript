// SPDX-License-Identifier: CC0-1.0

use core::fmt;

use bitcoin::taproot::{LeafVersion, TapLeafHash, TAPROOT_CONTROL_MAX_NODE_COUNT};

use crate::miniscript::context::Tap;
use crate::policy::{Liftable, Semantic};
use crate::prelude::Vec;
use crate::sync::Arc;
use crate::{Miniscript, MiniscriptKey, Threshold, ToPublicKey, ValidationError};

/// Tried to construct Taproot tree which was too deep.
#[derive(PartialEq, Eq, Debug)]
#[non_exhaustive]
pub struct TapTreeDepthError;

impl fmt::Display for TapTreeDepthError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("maximum Taproot tree depth (128) exceeded")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TapTreeDepthError {}

/// A Taproot Tree representation.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TapTree<Pk: MiniscriptKey> {
    depths_leaves: Vec<(u8, Arc<Miniscript<Pk, Tap>>)>,
}

impl<Pk: MiniscriptKey> TapTree<Pk> {
    /// Creates a `TapTree` leaf from a Miniscript.
    pub fn leaf<A: Into<Arc<Miniscript<Pk, Tap>>>>(ms: A) -> Self {
        TapTree { depths_leaves: vec![(0, ms.into())] }
    }

    /// Creates a `TapTree` by combining `left` and `right` tree nodes.
    pub fn combine(left: TapTree<Pk>, right: TapTree<Pk>) -> Result<Self, TapTreeDepthError> {
        let mut depths_leaves =
            Vec::with_capacity(left.depths_leaves.len() + right.depths_leaves.len());
        for (depth, leaf) in left.depths_leaves.iter().chain(right.depths_leaves.iter()) {
            if usize::from(*depth) > TAPROOT_CONTROL_MAX_NODE_COUNT - 1 {
                return Err(TapTreeDepthError);
            }
            depths_leaves.push((*depth + 1, Arc::clone(leaf)));
        }
        Ok(Self { depths_leaves })
    }

    /// Iterates over all the leaves of the tree in depth-first preorder.
    ///
    /// The yielded elements include the Miniscript for each leave as well as its depth
    /// in the tree, which is the data required by PSBT (BIP 371).
    pub fn leaves(&self) -> TapTreeIter<'_, Pk> { TapTreeIter::from_tree(self) }

    /// Converts keys from one type of public key to another.
    pub fn translate_pk<T>(
        &self,
        translate: &mut T,
    ) -> Result<TapTree<T::TargetPk>, crate::TranslateErr<T::Error>>
    where
        T: crate::Translator<Pk>,
    {
        let mut ret = TapTree { depths_leaves: Vec::with_capacity(self.depths_leaves.len()) };
        for (depth, leaf) in &self.depths_leaves {
            ret.depths_leaves
                .push((*depth, Arc::new(leaf.translate_pk(translate)?)));
        }

        Ok(ret)
    }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for TapTree<Pk> {
    fn lift(&self) -> Result<Semantic<Pk>, ValidationError> {
        let thresh_vec = self
            .leaves()
            .map(|item| item.miniscript().lift().map(Arc::new))
            .collect::<Result<Vec<_>, _>>()?;
        let thresh = Threshold::new(1, thresh_vec).expect("no size limit on Semantic threshold");
        Ok(Semantic::Thresh(thresh).normalized())
    }
}

fn fmt_helper<Pk: MiniscriptKey>(
    view: &TapTree<Pk>,
    f: &mut fmt::Formatter,
    mut fmt_ms: impl FnMut(&mut fmt::Formatter, &Miniscript<Pk, Tap>) -> fmt::Result,
) -> fmt::Result {
    let mut last_depth = 0;
    for item in view.leaves() {
        if last_depth > 0 {
            f.write_str(",")?;
        }

        while last_depth < item.depth() {
            f.write_str("{")?;
            last_depth += 1;
        }
        fmt_ms(f, item.miniscript())?;
        while last_depth > item.depth() {
            f.write_str("}")?;
            last_depth -= 1;
        }
    }

    while last_depth > 0 {
        f.write_str("}")?;
        last_depth -= 1;
    }
    Ok(())
}

impl<Pk: MiniscriptKey> fmt::Display for TapTree<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_helper(self, f, |f, ms| write!(f, "{}", ms))
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for TapTree<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_helper(self, f, |f, ms| write!(f, "{:?}", ms))
    }
}

/// Iterator over the leaves of a Taptree.
///
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
pub struct TapTreeIter<'tr, Pk: MiniscriptKey> {
    inner: core::slice::Iter<'tr, (u8, Arc<Miniscript<Pk, Tap>>)>,
}

impl<'tr, Pk: MiniscriptKey> TapTreeIter<'tr, Pk> {
    /// An empty iterator.
    pub fn empty() -> Self { Self { inner: [].iter() } }

    /// An iterator over a given tree.
    fn from_tree(tree: &'tr TapTree<Pk>) -> Self { Self { inner: tree.depths_leaves.iter() } }
}

impl<'tr, Pk: MiniscriptKey> Iterator for TapTreeIter<'tr, Pk> {
    type Item = TapTreeIterItem<'tr, Pk>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|&(depth, ref node)| TapTreeIterItem { depth, node })
    }
}

impl<'tr, Pk: MiniscriptKey> DoubleEndedIterator for TapTreeIter<'tr, Pk> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_back()
            .map(|&(depth, ref node)| TapTreeIterItem { depth, node })
    }
}

impl<'tr, Pk: MiniscriptKey> ExactSizeIterator for TapTreeIter<'tr, Pk> {
    fn len(&self) -> usize { self.inner.len() }
}

impl<'tr, Pk: MiniscriptKey> core::iter::FusedIterator for TapTreeIter<'tr, Pk> {}

/// Iterator over all of the leaves of a Taproot tree.
///
/// If there is no tree (i.e. this is a keyspend-only Taproot descriptor)
/// then the iterator will yield nothing.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TapTreeIterItem<'tr, Pk: MiniscriptKey> {
    node: &'tr Arc<Miniscript<Pk, Tap>>,
    depth: u8,
}

impl<'tr, Pk: MiniscriptKey> TapTreeIterItem<'tr, Pk> {
    /// The Tapscript in the leaf.
    ///
    /// To obtain a [`bitcoin::Script`] from this node, call [`Miniscript::encode`]
    /// on the returned value.
    #[inline]
    pub fn miniscript(&self) -> &'tr Arc<Miniscript<Pk, Tap>> { self.node }

    /// The depth of this leaf.
    ///
    /// This is useful for reconstructing the shape of the tree.
    #[inline]
    pub fn depth(&self) -> u8 { self.depth }

    /// The Tapleaf version of this leaf.
    ///
    /// This function returns a constant value, since there is only one version in use
    /// on the Bitcoin network; however, it may be useful to use this method in case
    /// you wish to be forward-compatible with future versions supported by this
    /// library.
    #[inline]
    pub fn leaf_version(&self) -> LeafVersion { LeafVersion::TapScript }
}

impl<Pk: ToPublicKey> TapTreeIterItem<'_, Pk> {
    /// Computes the Bitcoin Script of the leaf.
    ///
    /// This function is potentially expensive. If you are calling this method on
    /// all (or many) of the leaves of the tree, you may instead want to call
    /// [`super::Tr::spend_info`] and use the [`super::TrSpendInfo::leaves`] iterator instead.
    #[inline]
    pub fn compute_script(&self) -> bitcoin::ScriptBuf { self.node.encode() }

    /// Computes the [`TapLeafHash`] of the leaf.
    ///
    /// This function is potentially expensive, since it serializes the full Bitcoin
    /// Script of the leaf and hashes this data. If you are calling this method on
    /// all (or many) of the leaves of the tree, you may instead want to call
    /// [`super::Tr::spend_info`] and use the [`super::TrSpendInfo::leaves`] iterator instead.
    #[inline]
    pub fn compute_tap_leaf_hash(&self) -> TapLeafHash {
        TapLeafHash::from_script(&self.compute_script(), self.leaf_version())
    }
}

pub(super) struct TapTreeBuilder<Pk: MiniscriptKey> {
    depths_leaves: Vec<(u8, Arc<Miniscript<Pk, Tap>>)>,
    complete_heights: u128, // ArrayVec<bool, 129> represented as a bitmap...and a bool.
    complete_128: bool,     // BIP341 says depths are in [0,128] *inclusive* so 129 possibilities.
    current_height: u8,
}

impl<Pk: MiniscriptKey> TapTreeBuilder<Pk> {
    pub(super) fn new() -> Self {
        Self {
            depths_leaves: vec![],
            complete_heights: 0,
            complete_128: false,
            current_height: 0,
        }
    }

    #[inline]
    pub(super) fn push_inner_node(&mut self) -> Result<(), TapTreeDepthError> {
        self.current_height += 1;
        if usize::from(self.current_height) > TAPROOT_CONTROL_MAX_NODE_COUNT {
            return Err(TapTreeDepthError);
        }
        Ok(())
    }

    #[inline]
    pub(super) fn push_leaf<A: Into<Arc<Miniscript<Pk, Tap>>>>(&mut self, ms: A) {
        self.depths_leaves.push((self.current_height, ms.into()));

        // Special-case 128 which doesn't fit into the `complete_heights` bitmap
        if usize::from(self.current_height) == TAPROOT_CONTROL_MAX_NODE_COUNT {
            if self.complete_128 {
                self.complete_128 = false;
                self.current_height -= 1;
            } else {
                self.complete_128 = true;
                return;
            }
        }
        // Then deal with all other nonzero heights
        while self.current_height > 0 {
            if self.complete_heights & (1 << self.current_height) == 0 {
                self.complete_heights |= 1 << self.current_height;
                break;
            }
            self.complete_heights &= !(1 << self.current_height);
            self.current_height -= 1;
        }
    }

    #[inline]
    pub(super) fn finalize(self) -> TapTree<Pk> { TapTree { depths_leaves: self.depths_leaves } }
}
