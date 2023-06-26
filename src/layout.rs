//! This module contains the definitions for the layout representation types.
//!
//! It currently only contains placeholder types.

use crate::unifier::abi::AbiType;

/// The most-concrete layout discovered for the input contract.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StorageLayout {
    slots: Vec<StorageSlot>,
}

impl StorageLayout {
    /// Adds a slot specified by `index` and `typ` to the storage layout.
    pub fn add(&mut self, index: usize, typ: AbiType, defaulted: bool) {
        let slot = StorageSlot::new(index, typ, defaulted);
        self.slots.push(slot);
    }

    /// Gets the storage slots that make up this layout.
    #[must_use]
    pub fn slots(&self) -> &Vec<StorageSlot> {
        &self.slots
    }
}

impl Default for StorageLayout {
    fn default() -> Self {
        let slots = Vec::new();
        Self { slots }
    }
}

/// A representation of a concrete storage slot, with its best-known type.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct StorageSlot {
    /// The concrete index of the storage slot in the contract.
    pub index: usize,

    /// The best-known type of the storage slot.
    pub typ: AbiType,

    /// A flag indicating if any defaulting took place while computing `typ`.
    pub defaulted: bool,
}

impl StorageSlot {
    /// Constructs a new storage slot container for the data at `index` with
    /// type `typ`.
    #[must_use]
    pub fn new(index: usize, typ: AbiType, defaulted: bool) -> Self {
        Self {
            index,
            typ,
            defaulted,
        }
    }
}
