//! This module contains the definitions for the layout representation types.
//!
//! It currently only contains placeholder types.

use serde::{Deserialize, Serialize};

use crate::{inference::abi::AbiType, utility::U256Wrapper};

/// The most-concrete layout discovered for the input contract.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StorageLayout {
    slots: Vec<StorageSlot>,
}

impl StorageLayout {
    /// Adds a slot specified by `index` and `typ` to the storage layout.
    pub fn add(&mut self, index: impl Into<U256Wrapper>, offset: usize, typ: AbiType) {
        let slot = StorageSlot::new(index, offset, typ);
        self.slots.push(slot);

        // Keep them sorted by slot index with ties broken by slot offset
        self.slots.sort_by_key(|s| (s.index, s.offset));
    }

    /// Gets the storage slots that make up this layout.
    ///
    /// These are guaranteed to be sorted in ascending order by slot index and
    /// then offset within the slot.
    #[must_use]
    pub fn slots(&self) -> &Vec<StorageSlot> {
        &self.slots
    }
}

/// Additional utility functions to enable cleaner testing with the storage
/// layout.
impl StorageLayout {
    /// Checks if the layout contains the specified slot.
    #[must_use]
    pub fn has_slot(&self, index: impl Into<U256Wrapper>, offset: usize, typ: AbiType) -> bool {
        self.slots.contains(&StorageSlot::new(index, offset, typ))
    }

    /// Checks that there is no slot in the layout at the specified `index`.
    ///
    /// If you need to check that there is no slot specifically at an index and
    /// offset, use the negation of [`Iterator::any`] on the result of calling
    /// [`StorageLayout::slots`].
    #[must_use]
    pub fn has_no_slot_at(&self, index: impl Into<U256Wrapper>) -> bool {
        let index = index.into();
        !self.slots.iter().any(|s| s.index == index)
    }

    /// Gets the number of slots in the storage layout.
    #[must_use]
    pub fn slot_count(&self) -> usize {
        self.slots.len()
    }

    /// Checks if the storage layout is empty (has no slots).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}

impl Default for StorageLayout {
    fn default() -> Self {
        let slots = Vec::new();
        Self { slots }
    }
}

/// A representation of a concrete storage slot, with its best-known type.
#[derive(Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct StorageSlot {
    /// The concrete index of the storage slot in the contract.
    pub index: U256Wrapper,

    /// The offset at which the type starts within the storage slot.
    ///
    /// This will be 0 except in the case of structs and other packed encodings.
    pub offset: usize,

    #[serde(rename = "type")]
    /// The best-known type of the storage slot.
    pub typ: AbiType,
}

impl StorageSlot {
    /// Constructs a new storage slot container for the data at `index` with
    /// type `typ`.
    #[must_use]
    pub fn new(index: impl Into<U256Wrapper>, offset: usize, typ: AbiType) -> Self {
        let index = index.into();
        Self { index, offset, typ }
    }
}
