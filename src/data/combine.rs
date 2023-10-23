//! This module contains the definition of the [`Combine`] trait (a monoid) as
//! well as some default implementations of that trait for useful types in the
//! context of the extractor.

use std::{
    collections::HashSet,
    hash::{BuildHasher, Hash},
};

/// A trait that represents types that can be combined in a way equivalent to a
/// monoid.
pub trait Combine
where
    Self: Clone,
{
    /// The function that combines two values of the implementing type.
    ///
    /// The function must be:
    ///
    /// - **Symmetric** (such that `a.combine(b) == b.combine(a)`)
    /// - **Associative** (such that `a.combine(b.combine(c) ==
    ///   (a.combine(b)).combine(c)`).
    #[must_use]
    fn combine(self, other: Self) -> Self;

    /// An element `a` that, when combined (`a.combine(b)`) with another element
    /// `b` produces `b`.
    #[must_use]
    fn identity() -> Self;
}

impl<A: Combine> Combine for Option<A> {
    fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Some(a), Some(b)) => Some(a.combine(b)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        }
    }

    fn identity() -> Self {
        None
    }
}

impl<A, S> Combine for HashSet<A, S>
where
    A: Clone + Eq + Hash + PartialEq,
    S: BuildHasher + Clone + Default,
{
    fn combine(self, other: Self) -> Self {
        self.union(&other).cloned().collect()
    }

    fn identity() -> Self {
        HashSet::default()
    }
}
