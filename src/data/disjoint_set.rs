//! This module contains the definition of a specialised
//! [Disjoint Set](https://en.wikipedia.org/wiki/Disjoint-set_data_structure)
//! implementation that is capable of carrying data along with the values in the
//! tree.

use std::{fmt::Debug, hash::Hash};

use crate::data::{
    combine::Combine,
    vector_map::{FromUniqueIndex, ToUniqueIndex, VectorMap},
};

/// A specialised Disjoint Set implementation that is capable of carrying
/// arbitrary auxiliary data along with the values in the tree.
///
/// # Internal Mutability
///
/// It may seem counter-intuitive that an operation like [`Self::find`] requires
/// the structure to be mutable. This is because it internally optimises the set
/// representation as it is run.
///
/// Some work has been done in making this structure present a better interface
/// using a [`std::cell::RefCell`] for interior mutability. Unfortunately, this
/// results in around a 2-5% performance hit to unification (over the
/// non-`RefCell` version) which makes this suboptimal to do for the sake of a
/// nicer interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DisjointSet<Value, Data>
where
    Value: Clone + Debug + Eq + Hash + PartialEq + ToUniqueIndex,
    Data: Combine + Debug + Eq + PartialEq,
{
    reps: VectorMap<Value, Value>,
    data: VectorMap<Value, Data>,
}

impl<Value, Data> DisjointSet<Value, Data>
where
    Value: Clone + Debug + Eq + Hash + PartialEq + ToUniqueIndex,
    Data: Combine + Debug + Eq + PartialEq,
{
    /// Constructs a new union-find forest structure.
    #[must_use]
    pub fn new() -> Self {
        let reps = VectorMap::new();
        let data = VectorMap::new();
        Self { reps, data }
    }

    /// Constructs a new union-find forest structure guaranteed to have the
    /// ability to store at least `capacity` elements without reallocating.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        let reps = VectorMap::with_capacity(capacity);
        let data = VectorMap::with_capacity(capacity);
        Self { reps, data }
    }

    /// Inserts the `value` into the data structure.
    pub fn insert(&mut self, value: Value) {
        self.reps.insert(&value.clone(), value);
    }

    /// Finds the root element corresponding to the query `value`.
    ///
    /// # Mutability
    ///
    /// This function is mutable as it optimises the underlying representation
    /// under the hood. See the structure's top-level comment as for why it is
    /// not hidden using interior mutability.
    pub fn find(&mut self, value: &Value) -> Value {
        if let Some(rep) = self.reps.get(value).cloned() {
            if rep == *value {
                value.clone()
            } else {
                let f = self.find(&rep);
                self.reps.insert(value, f.clone());
                f
            }
        } else {
            self.reps.insert(value, value.clone());
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
        self.data.insert(&v1, v1_val.combine(v2_val));
        self.reps.insert(&v2, v1);
    }

    /// Associates the provided auxiliary `data` with `value`,
    /// [`Combine::combine`]ing it with any previous data.
    pub fn add_data(&mut self, value: &Value, data: Data) {
        let root = self.find(value);
        let previous_data = self.data.remove(&root).unwrap_or(Data::identity());
        self.data.insert(&root, previous_data.combine(data));
    }

    /// Gets the auxiliary data corresponding to the passed `value`, if it
    /// exists, or [`None`] otherwise.
    ///
    /// # Mutability
    ///
    /// This function is mutable as it optimises the underlying representation
    /// under the hood. See the structure's top-level comment as for why it is
    /// not hidden using interior mutability.
    pub fn get_data(&mut self, value: &Value) -> Option<&Data> {
        let root = self.find(value);
        self.data.get(&root)
    }

    /// Sets the provided auxiliary `data` for `value`, replacing any existing
    /// data for that value.
    pub fn set_data(&mut self, value: &Value, data: Data) {
        let root = self.find(value);
        self.data.insert(&root, data);
    }
}

impl<Value, Data> DisjointSet<Value, Data>
where
    Value: Clone + Debug + Eq + Hash + PartialEq + ToUniqueIndex + FromUniqueIndex,
    Data: Combine + Debug + Default + Eq + PartialEq,
{
    /// Gets all of the individual sets in the forest, along with their
    /// representant value.
    ///
    /// # Mutability
    ///
    /// This function is mutable as it optimises the underlying representation
    /// under the hood. See the structure's top-level comment as for why it is
    /// not hidden using interior mutability.
    pub fn sets(&mut self) -> Vec<(Value, Data)> {
        self.reps
            .iter()
            .filter(|(k, v)| *k == v.index())
            .map(|(k, _)| {
                let k = Value::from_index(k);
                let data = if let Some(v) = self.data.get(&k) {
                    v.clone()
                } else {
                    self.data.insert(&k, Data::default());
                    Data::default()
                };
                (k.clone(), data)
            })
            .collect()
    }

    /// Gets each individual value in the forest.
    #[must_use]
    pub fn values(&self) -> Vec<Value> {
        self.reps.indices().map(Value::from_index).collect()
    }
}

impl<Value, Data> Default for DisjointSet<Value, Data>
where
    Value: Clone + Debug + Eq + Hash + PartialEq + ToUniqueIndex,
    Data: Combine + Debug + Eq + PartialEq,
{
    fn default() -> Self {
        Self::new()
    }
}
