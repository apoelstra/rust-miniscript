// SPDX-License-Identifier: CC0-1.0

//! Thresholds
//!
//! Miniscript

#[cfg(all(not(feature = "std"), not(test)))]
use alloc::{vec, vec::Vec};
use core::{cmp, fmt, iter};
#[cfg(any(feature = "std", test))]
use std::vec;

/// Error parsing an absolute locktime.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ThresholdError {
    k: usize,
    n: usize,
    max: Option<usize>,
}

impl fmt::Display for ThresholdError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.n == 0 {
            f.write_str("thresholds in Miniscript must be nonempty")
        } else if self.k == 0 {
            f.write_str("thresholds in Miniscript must have k > 0")
        } else if self.k > self.n {
            write!(f, "invalid threshold {}-of-{}; cannot have k > n", self.k, self.n)
        } else {
            debug_assert!(self.max.is_some());
            let max = self.max.unwrap();
            debug_assert!(self.n > max);
            write!(f, "invalid threshold {}-of-{}; maximum size is {}", self.k, self.n, max)
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ThresholdError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> { None }
}

/// Check whether `k` and `n` are valid for an instance of [`Self`].
pub fn validate_k_n<const MAX: usize>(k: usize, n: usize) -> Result<(), ThresholdError> {
    if k == 0 || k > n || (MAX > 0 && n > MAX) {
        Err(ThresholdError { k, n, max: (MAX > 0).then_some(MAX) })
    } else {
        Ok(())
    }
}

/// Structure representing a k-of-n threshold collection of some arbitrary
/// object `T`.
///
/// If the constant parameter `MAX` is nonzero, it represents a cap on the
/// `n` value; if `n` exceeds `MAX` then an error is returned on construction.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Threshold<T, const MAX: usize> {
    k: usize,
    inner: Vec<T>,
}

impl<T, const MAX: usize> Threshold<T, MAX> {
    /// Constructs a threshold directly from a threshold value and collection.
    pub fn new(k: usize, inner: Vec<T>) -> Result<Self, ThresholdError> {
        validate_k_n::<MAX>(k, inner.len())?;
        Ok(Self { k, inner })
    }

    /// Constructs a threshold from a threshold value and an iterator that yields collection
    /// elements.
    pub fn from_iter<I: Iterator<Item = T>>(k: usize, iter: I) -> Result<Self, ThresholdError> {
        let min_size = cmp::max(k, iter.size_hint().0);
        // Do an early return if our minimum size exceeds the max.
        if MAX > 0 && min_size > MAX {
            let n = iter.count();
            return Err(ThresholdError { k, n, max: (MAX > 0).then_some(MAX) });
        }

        let mut inner = Vec::with_capacity(min_size);
        iter.for_each(|x| inner.push(x));
        Self::new(k, inner)
    }

    /// Constructor for an "or" represented as a 1-of-2 threshold.
    pub fn or(left: T, right: T) -> Self {
        debug_assert!(MAX == 0 || MAX > 1);
        Self { k: 1, inner: vec![left, right] }
    }

    /// Constructor for an "and" represented as a 2-of-2 threshold.
    pub fn and(left: T, right: T) -> Self {
        debug_assert!(MAX == 0 || MAX > 1);
        Self { k: 2, inner: vec![left, right] }
    }

    /// Whether this threshold is a 1-of-n.
    pub fn is_or(&self) -> bool { self.k == 1 }

    /// Whether this threshold is a n-of-n.
    pub fn is_and(&self) -> bool { self.k == self.inner.len() }

    /// Changes the type-system-enforced maximum value of the threshold.
    pub fn set_maximum<const NEWMAX: usize>(self) -> Result<Threshold<T, NEWMAX>, ThresholdError> {
        Threshold::new(self.k, self.inner)
    }

    /// Forgets the type-system-enforced maximum value of the threshold.
    pub fn forget_maximum(self) -> Threshold<T, 0> { Threshold { k: self.k, inner: self.inner } }

    /// Constructs a threshold from an existing threshold by applying a mapping function to
    /// each individual item.
    pub fn map<U, F: FnMut(T) -> U>(self, mapfn: F) -> Threshold<U, MAX> {
        Threshold { k: self.k, inner: self.inner.into_iter().map(mapfn).collect() }
    }

    /// Like [`Self::map`] but takes a reference to the threshold rather than taking ownership.
    pub fn map_ref<U, F: FnMut(&T) -> U>(&self, mapfn: F) -> Threshold<U, MAX> {
        Threshold { k: self.k, inner: self.inner.iter().map(mapfn).collect() }
    }

    /// Like [`Self::map`] except that the mapping function may return an error.
    pub fn translate<U, F, FuncError>(self, translatefn: F) -> Result<Threshold<U, MAX>, FuncError>
    where
        F: FnMut(T) -> Result<U, FuncError>,
    {
        let k = self.k;
        self.inner
            .into_iter()
            .map(translatefn)
            .collect::<Result<Vec<_>, _>>()
            .map(|inner| Threshold { k, inner })
    }

    /// Like [`Self::translate`] but takes a reference to the threshold rather than taking ownership.
    pub fn translate_ref<U, F, FuncError>(
        &self,
        translatefn: F,
    ) -> Result<Threshold<U, MAX>, FuncError>
    where
        F: FnMut(&T) -> Result<U, FuncError>,
    {
        let k = self.k;
        self.inner
            .iter()
            .map(translatefn)
            .collect::<Result<Vec<_>, _>>()
            .map(|inner| Threshold { k, inner })
    }

    /// Like [`Self::translate_ref`] but passes indices to the closure rather than internal data.
    ///
    /// This is useful in situations where the data to be translated exists outside of the
    /// threshold itself, and the threshold data is irrelevant. In particular it is used
    /// within the `verify_threshold` method for expression trees.
    ///
    /// If the data to be translated comes from a post-order iterator, you may instead want
    /// [`Self::map_from_post_order_iter`].
    pub fn translate_by_index<U, F, FuncError>(
        &self,
        translatefn: F,
    ) -> Result<Threshold<U, MAX>, FuncError>
    where
        F: FnMut(usize) -> Result<U, FuncError>,
    {
        let k = self.k;
        (0..self.inner.len())
            .map(translatefn)
            .collect::<Result<Vec<_>, _>>()
            .map(|inner| Threshold { k, inner })
    }

    /// Construct a threshold from an existing threshold which has been processed in some way.
    ///
    /// It is a common pattern in this library to transform data structures by
    /// running a post-order iterator over them, putting processed elements into
    /// a vector to be later referenced by their parents.
    ///
    /// This function encapsulates that pattern by taking the child-index vector of
    /// the`PostOrderIterItem`, under consideration, and the vector of processed
    /// elements.
    pub fn map_from_post_order_iter<U: Clone>(
        &self,
        child_indices: &[usize],
        processed: &[U],
    ) -> Threshold<U, MAX> {
        debug_assert_eq!(
            self.inner.len(),
            child_indices.len(),
            "internal consistency error translating threshold by post-order iterator"
        );
        let mut processed_inner = Vec::with_capacity(self.inner.len());
        processed_inner.extend(child_indices.iter().copied().map(|n| processed[n].clone()));
        Threshold { k: self.k, inner: processed_inner }
    }

    /// Accessor for the number of elements in the threshold.
    // non-const because Vec::len is not const
    pub fn n(&self) -> usize { self.inner.len() }

    /// Accessor for the threshold value.
    pub const fn k(&self) -> usize { self.k }

    /// Accessor for the underlying data.
    pub fn data(&self) -> &[T] { &self.inner }

    /// Mutable accessor for the underlying data.
    ///
    /// This returns access to the underlying data as a mutable slice, which allows you
    /// to modify individual elements. To change the number of elements, you must
    /// destructure the threshold with [`Self::k`] and [`Self::into_data`] and
    /// reconstruct it (and on reconstruction, deal with any errors caused by your
    /// tinkering with the threshold values).
    pub fn data_mut(&mut self) -> &mut [T] { &mut self.inner }

    /// Accessor for the underlying data.
    pub fn into_data(self) -> Vec<T> { self.inner }

    /// Passthrough to an iterator on the underlying vector.
    pub fn iter(&self) -> core::slice::Iter<'_, T> { self.inner.iter() }
}

impl<T> Threshold<T, 0> {
    /// Constructor for an "or" represented as a 1-of-n threshold.
    ///
    /// # Panics
    ///
    /// Panics if the passed vector is empty.
    pub fn or_n(inner: Vec<T>) -> Self {
        assert_ne!(inner.len(), 0);
        Self { k: 1, inner }
    }

    /// Constructor for an "and" represented as a n-of-n threshold.
    ///
    /// # Panics
    ///
    /// Panics if the passed vector is empty.
    pub fn and_n(inner: Vec<T>) -> Self {
        assert_ne!(inner.len(), 0);
        Self { k: inner.len(), inner }
    }
}

impl<T, const MAX: usize> iter::IntoIterator for Threshold<T, MAX> {
    type Item = T;
    type IntoIter = vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter { self.inner.into_iter() }
}

impl<T: fmt::Display, const MAX: usize> Threshold<T, MAX> {
    /// Produces an object which can [`fmt::Display`] the threshold.
    pub fn display<'s>(&'s self, name: &'s str, show_k: bool) -> impl fmt::Display + 's {
        ThreshDisplay { name, thresh: self, show_k }
    }
}

impl<T: fmt::Debug, const MAX: usize> Threshold<T, MAX> {
    /// Produces an object which can [`fmt::Debug`] the threshold.
    pub fn debug<'s>(&'s self, name: &'s str, show_k: bool) -> impl fmt::Debug + 's {
        ThreshDisplay { name, thresh: self, show_k }
    }
}

struct ThreshDisplay<'t, 's, T, const MAX: usize> {
    name: &'s str,
    thresh: &'t Threshold<T, MAX>,
    show_k: bool,
}

impl<T, const MAX: usize> fmt::Display for ThreshDisplay<'_, '_, T, MAX>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use core::fmt::Write;

        f.write_str(self.name)?;
        f.write_char('(')?;
        let inners = if self.show_k {
            write!(f, "{}", self.thresh.k)?;
            &self.thresh.inner[0..]
        } else {
            write!(f, "{}", self.thresh.inner[0])?;
            &self.thresh.inner[1..]
        };
        for inner in inners {
            write!(f, ",{}", inner)?;
        }
        f.write_char(')')
    }
}

impl<T, const MAX: usize> fmt::Debug for ThreshDisplay<'_, '_, T, MAX>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use core::fmt::Write;

        f.write_str(self.name)?;
        f.write_char('(')?;
        let inners = if self.show_k {
            write!(f, "{}", self.thresh.k)?;
            &self.thresh.inner[0..]
        } else {
            write!(f, "{:?}", self.thresh.inner[0])?;
            &self.thresh.inner[1..]
        };
        for inner in inners {
            write!(f, ",{:?}", inner)?;
        }
        f.write_char(')')
    }
}
