// SPDX-License-Identifier: CC0-1.0

//! Errors
//!
//! Provides the [`WithSpan`] error-wrapping structure, which attaches
//! a span and backing string context to an error. Here "backing string"
//! refers to an owned or unowned string (in the case of a descriptor
//! parsed from string), an owned or unowned script (in the case of
//! Miniscript parsed from Bitcoin Script), or one of the two special
//! marker types [`SpanOnly`] and [`NoString`].
//!
//! [`SpanOnly`] indicates that the error carries meaningful span
//! information but not a backing string. It is expected that a higher
//! level of code will attach the backing string by calling
//! [`WithSpan::with_string`].
//!
//! [`NoString`] indicates that the span information in the error is
//! meaningless, because the objects being manipulated do not originate
//! in any type of string.
//!
//! Most internal functions in this library will return an error type
//! of the form `Result<T, WithSpan<SpanOnly, E>>`. Then user-facing
//! top-level functions will convert this into a more specific type
//! by attaching the appropriate backing string, if any.
//!

use core::{fmt, ops};

use crate::prelude::*;

/// Extension trait to allow attaching span information to an error.
pub trait ResultExt: Sized {
    /// For `Result<T, E>`, this is `Result<T, WithSpan<E, SpanOnly>>`.
    type IncompleteSpanResult;

    /// Attaches a span to an error, without attaching any backing string.
    fn with_span(self, span: ops::Range<usize>) -> Self::IncompleteSpanResult;

    /// Attaches a single-character span at the given index to an error,
    /// without attaching any backing string.
    fn with_index(self, index: usize) -> Self::IncompleteSpanResult {
        self.with_span(index..index + 1)
    }
}

impl<T, E> ResultExt for Result<T, E> {
    type IncompleteSpanResult = Result<T, WithSpan<E>>;

    fn with_span(self, span: ops::Range<usize>) -> Self::IncompleteSpanResult {
        self.map_err(|inner| WithSpan { string: SpanOnly, span, inner })
    }
}

/// Marker indicating that an error has span information but does not
/// carry the slice that this span indexes into.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SpanOnly;

// This impl is needed for the type to work as a dummy "backing string".
impl ops::Index<ops::Range<usize>> for SpanOnly {
    type Output = Self;
    fn index(&self, _: ops::Range<usize>) -> &Self { self }
}

// This impl is needed for the type to work as a dummy "backing string".
impl fmt::Display for SpanOnly {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { f.write_str("[span only]") }
}

/// Marker indicating that an error may have span information, but this
/// is not meaningful because no backing string exists.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NoString;

// This impl is needed for the type to work as a dummy "backing string".
impl ops::Index<ops::Range<usize>> for NoString {
    type Output = Self;
    fn index(&self, _: ops::Range<usize>) -> &Self { self }
}

// This impl is needed for the type to work as a dummy "backing string".
impl fmt::Display for NoString {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result { Err(fmt::Error) }
}

/// A wrapped version of a string-parsing error which includes extra context.
///
/// This is the only error type in this module which should be constructed
/// from outside of this module.
///
/// This error has a generic parameter for the underlying string-parsing error.
/// Whenever possible, we recommend developers instantiate this with a concrete type
/// rather than propagating the parameter to higher-level error types. This
/// reduces complie times and complexity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WithSpan<E, S = SpanOnly> {
    string: S,
    span: ops::Range<usize>,
    inner: E,
}

impl<E, S> WithSpan<E, S> {
    /// Accessor for the underlying string.
    pub const fn string(&self) -> &S { &self.string }

    /// Accessor for the underlying string.
    pub const fn span(&self) -> ops::Range<usize> {
        // Range does not impl Copy, and Clone is non-const, so we must do
        // a manual clone.
        ops::Range { start: self.span.start, end: self.span.end }
    }

    /// Accessor for the wrapped error.
    pub const fn error(&self) -> &E { &self.inner }

    /// Accessor for the wrapped error.
    pub fn into_error(self) -> E { self.inner }

    /// Maps one kind of error to another, preserving the span information.
    pub fn map<E2, F: FnOnce(E) -> E2>(self, mapfn: F) -> WithSpan<E2, S> {
        WithSpan { string: self.string, span: self.span, inner: mapfn(self.inner) }
    }
}

impl<E, S: fmt::Display> WithSpan<E, S> {
    /// Hack to emulate run-time specification on `WithSpan<E, NoString>`.
    ///
    /// Because Rust does not have specification, we need to do run-time detection
    /// of whether we have a "no string" `WithSpan`, since this affects the output
    /// of `fmt::Display`.
    ///
    /// The "natural" way to implement this is in terms of `Any::type_id()`, but
    /// it turns out that `Any` is only implemented when `S: 'static`, which excludes
    /// many things, most importantly `&str`. (There are some other hacks, e.g. "autoref
    /// specification" developed by dtolnay, but this does not work with generic
    /// parameters, and I think that nothing does.)
    ///
    /// Instead we use `type_name`, which the docs say is for "diagnostic use only"
    /// and has a pile of caveats, BUT for this use case (comparing to a specific
    /// concrete type with no parameters or other weird aspects, which is defined
    /// in the same module as this check) it should reliably work.
    ///
    /// This strategy has some limitations -- in particular if you parameterize
    /// the the type with a `Box<dyn fmt::Format>` which is actually a `NoString`,
    /// this method will return false instead of true -- but these limitations
    /// don't matter for this usecase.
    fn has_no_string(&self) -> bool {
        core::any::type_name::<S>() == core::any::type_name::<NoString>()
    }
}

impl<E> WithSpan<E, SpanOnly> {
    /// Attaches a backing string to a span carrying error.
    ///
    /// # Panics
    ///
    /// Panics if the span lies outside of the provided string.
    pub fn with_string<S: ops::Index<ops::Range<usize>>>(self, string: S) -> WithSpan<E, S> {
        let _ = &string[self.span()]; // trigger a panic if the span is OOB for the string
        WithSpan { string, span: self.span, inner: self.inner }
    }

    /// Indicates that a span-carrying error has no backing string.
    pub fn without_string(self) -> WithSpan<E, NoString> { self.with_string(NoString) }
}

impl<E, S: ToOwned> WithSpan<E, S> {
    /// For a span whose backing string is borrowed, return the owned variant.
    ///
    /// This is useful for dropping lifetimes from `Result`s and errors.
    pub fn to_owned(self) -> WithSpan<E, S::Owned> {
        WithSpan { string: self.string.to_owned(), span: self.span, inner: self.inner }
    }
}

impl<E: fmt::Display, S: fmt::Display> fmt::Display for WithSpan<E, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.has_no_string() {
            if self.span.len() == 1 {
                write!(f, "at span {}:{} of {}:", self.span.start, self.span.end, self.string)?;
            } else {
                write!(f, "at position {} of {}:", self.span.start, self.string)?;
            }
        }
        fmt::Display::fmt(&self.inner, f)
    }
}

#[cfg(feature = "std")]
impl<E: std::error::Error, S: fmt::Debug + fmt::Display + 'static> std::error::Error
    for WithSpan<E, S>
{
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> { self.inner.source() }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_string_hack() {
        let non_static = "hmm".to_owned();
        assert!(WithSpan { string: NoString, span: 0..0, inner: () }.has_no_string());
        assert!(!WithSpan { string: "hmm", span: 0..0, inner: () }.has_no_string());
        assert!(!WithSpan { string: &non_static, span: 0..0, inner: () }.has_no_string());
    }
}
