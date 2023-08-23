//! This module contains data structures used in the implementation of the
//! unifier.

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::{BuildHasher, Hash},
};

/// An specialised implementation of the
/// [Disjoint Set](https://en.wikipedia.org/wiki/Disjoint-set_data_structure)
/// data structure that is capable of carrying arbitrary auxiliary data along
/// with the values in the tree.
///
/// # Performance
///
/// The implementation of [`Self::find`] could be improved in efficiency. This
/// is left as future work, but can be done by allowing `find` to optimise the
/// forest as it does its work.
///
/// Similarly, this implementation currently makes liberal use of cloning.
/// Ideally it would instead rely on interior mutability as much as possible,
/// but this is an optimisation for the future.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DisjointSet<Value, Data>
where
    Value: Clone + Debug + Eq + Hash + PartialEq,
    Data: Combine + Debug + Eq + PartialEq,
{
    reps: HashMap<Value, Value>,
    data: HashMap<Value, Data>,
}

impl<Value, Data> DisjointSet<Value, Data>
where
    Value: Clone + Debug + Eq + Hash + PartialEq,
    Data: Combine + Debug + Eq + PartialEq,
{
    /// Constructs a new union-find forest structure
    #[must_use]
    pub fn new() -> Self {
        let reps = HashMap::new();
        let data = HashMap::new();
        Self { reps, data }
    }

    /// Inserts the `value` into the data structure.
    pub fn insert(&mut self, value: Value) {
        self.reps.insert(value.clone(), value);
    }

    /// Finds the root element corresponding to the query `value`.
    pub fn find(&mut self, value: &Value) -> Value {
        if let Some(rep) = self.reps.get(value).cloned() {
            if rep == *value {
                value.clone()
            } else {
                let f = self.find(&rep);
                self.reps.insert(value.clone(), f.clone());
                f
            }
        } else {
            self.reps.insert(value.clone(), value.clone());
            self.find(value)
        }
    }

    /// Merges the set containing `v1` with the set containing `v2`, using
    /// [`Self::find`] to first find the roots.
    pub fn union(&mut self, v1: &Value, v2: &Value) {
        let v1 = self.find(v1);
        let v2 = self.find(v2);
        let v1_val = self.data.get(&v1).cloned().unwrap_or(Data::identity());
        let v2_val = self.data.remove(&v2).unwrap_or(Data::identity());
        self.data.insert(v1.clone(), v1_val.combine(v2_val));
        self.reps.insert(v2, v1);
    }

    /// Associates the provided auxiliary `data` with `value`,
    /// [`Combine::combine`]ing it with any previous data.
    pub fn add_data(&mut self, value: &Value, data: Data) {
        let root = self.find(value);
        let previous_data = self.data.remove(&root).unwrap_or(Data::identity());
        self.data.insert(root.clone(), previous_data.combine(data));
    }

    /// Gets the auxiliary data corresponding to the passed `value`, if it
    /// exists, or [`None`] otherwise.
    pub fn get_data(&mut self, value: &Value) -> Option<&Data> {
        let root = self.find(value);
        self.data.get(&root)
    }

    /// Sets the provided auxiliary `data` for `value`, replacing any existing
    /// data for that value.
    pub fn set_data(&mut self, value: &Value, data: Data) {
        let root = self.find(value);
        self.data.insert(root, data);
    }
}

impl<Value, Data> DisjointSet<Value, Data>
where
    Value: Clone + Debug + Eq + Hash + PartialEq,
    Data: Combine + Debug + Default + Eq + PartialEq,
{
    /// Gets all of the individual sets in the forest.
    pub fn sets(&mut self) -> Vec<(Value, Data)> {
        self.reps
            .iter()
            .filter(|(k, v)| k == v)
            .map(|(k, _)| (k.clone(), self.data.entry(k.clone()).or_default().clone()))
            .collect()
    }
}

impl<Value, Data> Default for DisjointSet<Value, Data>
where
    Value: Clone + Debug + Eq + Hash + PartialEq,
    Data: Combine + Debug + Eq + PartialEq,
{
    fn default() -> Self {
        Self::new()
    }
}

/// A trait that represents types that can be combined in some way.
///
/// This is equivalent to a monoid.
pub trait Combine
where
    Self: Clone,
{
    /// The combination function itself.
    ///
    /// The function should be:
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
