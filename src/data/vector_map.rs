//! This module contains the definition of a map-like structure that is based on
//! a contiguous vector. It uses the fact that its keys must implement
//! [`ToUniqueIndex`] to store them in contiguous memory.

use std::marker::PhantomData;

use derivative::Derivative;

/// A map-like structure based on a vector that works over key types that
/// implement [`ToUniqueIndex`].
///
/// # Memory Usage
///
/// The `VectorMap` will take up _at least_ `mem::size_of::<Option<V>>() * n`
/// bytes where `n` is the largest unique index stored in it. Think very
/// carefully about the size of your data before using this type.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "V: std::clone::Clone"),
    Debug(bound = "V: std::fmt::Debug"),
    Eq(bound = "V: std::cmp::Eq"),
    PartialEq(bound = "V: std::cmp::PartialEq")
)]
pub struct VectorMap<K, V>
where
    K: ToUniqueIndex,
{
    /// A retainer for the key type `K` such that it remains part of the map's
    /// type.
    #[derivative(Debug = "ignore")]
    phantom: PhantomData<K>,

    /// The actual data stored in the container.
    data: Vec<Option<V>>,

    /// The number of items currently inserted into the map.
    size: usize,
}

impl<K, V> VectorMap<K, V>
where
    K: ToUniqueIndex,
{
    /// Creates a new, empty, `VectorMap`.
    #[must_use]
    pub fn new() -> Self {
        let data = Vec::new();
        Self::new_with_vec(data)
    }

    /// Creates a new, empty, `VectorMap` that is guaranteed to have a
    /// large-enough underlying allocation to store _at least_ `capacity`
    /// items before needing to reallocate.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        let data = Vec::with_capacity(capacity);
        Self::new_with_vec(data)
    }

    /// Constructs a new `VectorMap` with the provided `data` as its backing
    /// buffer.
    fn new_with_vec(data: Vec<Option<V>>) -> Self {
        let phantom = PhantomData;
        let size = 0;
        Self {
            phantom,
            data,
            size,
        }
    }

    /// Inserts the provided `value` into the map at the `key`s
    /// [`ToUniqueIndex::index`].
    ///
    /// # Complexity
    ///
    /// Complexity of an insertion at `key.index` is `O(1)` when `key.index <
    /// max_key_index` or `O(n)` where `n = key.index - max_key_index`.
    pub fn insert(&mut self, key: &K, value: V) {
        let index = key.index();
        while index >= self.data.len() {
            self.data.push(None);
        }

        // Actually write the data into the vector.
        self.data[index] = Some(value);

        // Increment the size so it stays accurate
        self.size += 1;
    }

    /// Gets the value in the map for the provided `key` or [`None`] if there is
    /// no entry for `key` in the map.
    ///
    /// # Complexity
    ///
    /// Complexity of getting a value at `key` is `O(1)`.
    pub fn get(&self, key: &K) -> Option<&V> {
        let index = key.index();
        match self.data.get(index) {
            Some(v) => v.as_ref(),
            _ => None,
        }
    }

    /// Gets the value in the map for the provided `key` or [`None`] if there is
    /// no entry for `key` in the map.
    ///
    /// # Complexity
    ///
    /// Complexity of getting a value at `key` is `O(1)`.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let index = key.index();
        match self.data.get_mut(index) {
            Some(v) => match v.as_mut() {
                a @ Some(_) => a,
                None => None,
            },
            None => None,
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Complexity
    ///
    /// Complexity of removing the value at `key` is `O(1)`.
    #[must_use]
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let index = key.index();

        if index < self.data.len() {
            let value = self.data[index].take();
            self.size -= 1;

            value
        } else {
            None
        }
    }

    /// Returns the number of elements the map can hold without reallocating.
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    /// Gets the number of items currently inserted into the map.
    #[must_use]
    pub fn len(&self) -> usize {
        self.size
    }

    /// Checks whether the map is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Gets the largest currently-stored key index in the map if the map is
    /// non-empty, or [`None`] otherwise.
    #[must_use]
    pub fn max_key_index(&self) -> Option<usize> {
        if self.is_empty() {
            None
        } else {
            Some(self.data.len() - 1)
        }
    }

    /// An iterator visiting all index-value pairs in arbitrary order. The
    /// iterator element type is `(usize, &'a V)`.
    #[allow(clippy::missing_panics_doc)] // Cannot actually panic
    pub fn iter(&self) -> impl Iterator<Item = (usize, &V)> {
        self.data
            .iter()
            .enumerate()
            .filter(|(_, v)| v.is_some())
            .map(|(i, v)| (i, v.as_ref().expect("Known Some was not Some")))
    }

    /// An iterator visiting all index-value pairs in arbitrary order. The
    /// iterator element type is `(usize, &'a V)`.
    #[allow(clippy::missing_panics_doc)] // Cannot actually panic
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (usize, &mut V)> {
        self.data
            .iter_mut()
            .enumerate()
            .filter(|(_, v)| v.is_some())
            .map(|(i, v)| (i, v.as_mut().expect("Known Some was not Some")))
    }

    /// An iterator visiting all indices in an arbitrary order. The iterator
    /// element type is `usize`.
    pub fn indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.data
            .iter()
            .enumerate()
            .filter_map(|(i, v)| v.as_ref().map(|_| i))
    }

    /// Creates a consuming iterator visiting all the indices in arbitrary
    /// order. The map cannot be used after calling this. The iterator
    /// element type is `usize`.
    pub fn into_indices(self) -> impl Iterator<Item = usize> {
        self.data
            .into_iter()
            .enumerate()
            .filter_map(|(i, v)| v.as_ref().map(|_| i))
    }

    /// An iterator visiting all indices in an arbitrary order. The iterator
    /// element type is `&'a V`.
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.data.iter().filter_map(Option::as_ref)
    }

    /// Creates a consuming iterator visiting all the indices in arbitrary
    /// order. The map cannot be used after calling this. The iterator
    /// element type is `V`.
    pub fn into_values(self) -> impl Iterator<Item = V> {
        self.data.into_iter().flatten()
    }
}

impl<K, V> Default for VectorMap<K, V>
where
    K: ToUniqueIndex,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> From<&[(K, V)]> for VectorMap<K, V>
where
    K: ToUniqueIndex,
    V: Clone,
{
    fn from(value: &[(K, V)]) -> Self {
        let mut map: VectorMap<K, V> = VectorMap::new();

        for (key, val) in value {
            map.insert(key, val.clone());
        }

        map
    }
}

impl<K, V> From<Vec<(K, V)>> for VectorMap<K, V>
where
    K: ToUniqueIndex + Sized,
    V: Sized,
{
    fn from(value: Vec<(K, V)>) -> Self {
        let mut map: VectorMap<K, V> = VectorMap::new();

        for (key, val) in value {
            map.insert(&key, val);
        }

        map
    }
}

/// A trait representing objects that can be mapped to unique indices.
pub trait ToUniqueIndex {
    /// Gets the unique index for `self`.
    fn index(&self) -> usize;
}

impl ToUniqueIndex for usize {
    fn index(&self) -> usize {
        *self
    }
}

/// A trait representing objects that can be constructed from their unique
/// indices.
pub trait FromUniqueIndex {
    fn from_index(index: usize) -> Self;
}

impl FromUniqueIndex for usize {
    fn from_index(index: usize) -> Self {
        index
    }
}

#[cfg(test)]
mod test {
    use itertools::Itertools;

    use crate::data::vector_map::test::util::VectorMap;

    #[test]
    fn construction() {
        let _ = VectorMap::new();
    }

    #[test]
    fn insert() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        map.insert(&0, 10);
        assert_eq!(map.len(), 1);

        map.insert(&10, 20);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn get() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        map.insert(&0, 10);
        assert_eq!(map.get(&0), Some(&10));

        assert!(map.get(&10).is_none());
    }

    #[test]
    fn get_mut() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        map.insert(&0, 10);
        assert_eq!(map.get_mut(&0), Some(&mut 10));

        assert!(map.get(&10).is_none());
    }

    #[test]
    fn remove() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        map.insert(&0, 10);
        map.insert(&1, 20);
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(&0), Some(&10));
        assert_eq!(map.get(&1), Some(&20));

        assert_eq!(map.remove(&0), Some(10));
        assert_eq!(map.len(), 1);
        assert_eq!(map.get(&1), Some(&20));
    }

    #[test]
    fn capacity() {
        let map = VectorMap::new();
        let _ = map.capacity();
    }

    #[test]
    fn len() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        map.insert(&0, 10);
        map.insert(&1, 20);
        map.insert(&2, 30);
        assert_eq!(map.len(), 3);
    }

    #[test]
    fn is_empty() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        map.insert(&0, 10);
        assert!(!map.is_empty());
    }

    #[test]
    fn max_key_index() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());
        assert_eq!(map.max_key_index(), None);

        map.insert(&10, 10);
        assert!(!map.is_empty());
        assert_eq!(map.max_key_index(), Some(10));
    }

    #[test]
    fn iter() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        let mut expected_result = Vec::new();
        for i in (0..10).step_by(2) {
            map.insert(&i, i * 10);
            expected_result.push((i, i * 10));
        }
        assert_eq!(map.len(), 5);

        let pairs = map.iter().map(|(k, v)| (k, *v)).collect_vec();
        assert_eq!(pairs, expected_result);
    }

    #[test]
    fn iter_mut() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        let mut expected_result = Vec::new();
        for i in (0..10).step_by(2) {
            map.insert(&i, i * 10);
            expected_result.push((i, i * 10));
        }
        assert_eq!(map.len(), 5);

        let pairs = map.iter_mut().map(|(k, v)| (k, *v)).collect_vec();
        assert_eq!(pairs, expected_result);
    }

    #[test]
    fn indices() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        let mut expected_result = Vec::new();
        for i in (0..10).step_by(2) {
            map.insert(&i, i * 10);
            expected_result.push(i);
        }
        assert_eq!(map.len(), 5);

        let pairs = map.indices().collect_vec();
        assert_eq!(pairs, expected_result);
    }

    #[test]
    fn into_indices() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        let mut expected_result = Vec::new();
        for i in (0..10).step_by(2) {
            map.insert(&i, i * 10);
            expected_result.push(i);
        }
        assert_eq!(map.len(), 5);

        let pairs = map.into_indices().collect_vec();
        assert_eq!(pairs, expected_result);
    }

    #[test]
    fn values() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        let mut expected_result = Vec::new();
        for i in (0..10).step_by(2) {
            map.insert(&i, i * 10);
            expected_result.push(i * 10);
        }
        assert_eq!(map.len(), 5);

        let pairs = map.values().copied().collect_vec();
        assert_eq!(pairs, expected_result);
    }

    #[test]
    fn into_values() {
        let mut map = VectorMap::new();
        assert!(map.is_empty());

        let mut expected_result = Vec::new();
        for i in (0..10).step_by(2) {
            map.insert(&i, i * 10);
            expected_result.push(i * 10);
        }
        assert_eq!(map.len(), 5);

        let pairs = map.into_values().collect_vec();
        assert_eq!(pairs, expected_result);
    }

    /// Utilities for testing the vector map.
    mod util {
        use crate::data::vector_map::VectorMap as ActualVectorMap;

        /// A type of the map to make testing easier.
        pub type VectorMap = ActualVectorMap<Key, Value>;

        /// A key type for testing.
        pub type Key = usize;

        /// A value type for testing.
        pub type Value = usize;
    }
}
