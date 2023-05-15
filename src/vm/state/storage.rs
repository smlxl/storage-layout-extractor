//! This module contains the definition of the virtual machine's storage
//! container.

// TODO [Ara] Some complexity here comes from the fact that offsets into the
//   storage may be symbolic variables, but also frequently _aren't_.

use std::collections::HashMap;

use crate::vm::symbolic_value::{
    known_data::KnownData,
    BoxedVal,
    Provenance,
    SymbolicValue,
    SymbolicValueData,
};

/// A representation of the persistent storage of the symbolic virtual machine.
///
/// Where the storage on a real EVM implementation is effectively a
/// word-addressable word-array where every slot is initialized to 0. This does
/// not work for symbolic values, and so we require a split approach.
///
/// 1. Many writes to storage write to known (non-symbolic) identifiers. These
///    can be stored and retrieved naturally.
/// 2. Other writes to storage write to keys that are computed in the program
///    (e.g. for mappings and dynamic arrays), so we have to be able to work
///    with arbitrary symbolic values as well.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Storage {
    /// Many storage writes are in the form of a known slot index.
    known_slots: HashMap<BoxedVal, BoxedVal>,

    /// Others use symbolic values as offsets.
    symbolic_slots: HashMap<BoxedVal, BoxedVal>,
}

impl Storage {
    /// Creates a new, empty storage.
    pub fn new() -> Self {
        let fixed_slots = HashMap::new();
        let symbolic_slots = HashMap::new();
        Self {
            known_slots: fixed_slots,
            symbolic_slots,
        }
    }

    /// Stores the provided `value` in storage at the provided `key`,
    /// overwriting any existing value at that key.
    ///
    /// The `value` is treated as being 256 bits wide.
    pub fn store(&mut self, key: BoxedVal, value: BoxedVal) {
        let target_map = match key.data {
            SymbolicValueData::KnownData { .. } => &mut self.known_slots,
            _ => &mut self.symbolic_slots,
        };
        target_map.insert(key, value);
    }

    /// Loads any value found at the provided `key`, returning 0 if the slot has
    /// never been written to.
    ///
    /// # Note
    ///
    /// This is a best-effort analysis as we cannot guarantee knowing if there
    /// have been overwrites between adjacent slots.
    pub fn load(&mut self, key: &BoxedVal) -> &BoxedVal {
        // First we need to work out which of the maps to read from.
        let target_map = match key.data {
            SymbolicValueData::KnownData { .. } => &mut self.known_slots,
            _ => &mut self.symbolic_slots,
        };

        // Once we have that we can pull the key out, or default in the map if it
        // doesn't exist
        target_map.entry(key.clone()).or_insert_with(|| {
            // The instruction pointer is 0 here, as the uninitialized value was created
            // when the program started. It is _not_ synthetic.
            SymbolicValue::new_known_value(
                0,
                KnownData::zero(),
                Provenance::UninitializedStorage { key: key.clone() },
            )
        })
    }

    /// Gets the number of entries in the storage.
    pub fn entry_count(&self) -> usize {
        self.known_slots.len() + self.symbolic_slots.len()
    }

    /// Gets the slot keys for this storage that have been written to.
    pub fn keys(&self) -> Vec<&BoxedVal> {
        let mut known_keys: Vec<&BoxedVal> = self.known_slots.keys().collect();
        let symbolic_keys: Vec<&BoxedVal> = self.symbolic_slots.keys().collect();

        known_keys.extend(symbolic_keys.into_iter());

        known_keys
    }
}

impl Default for Storage {
    fn default() -> Self {
        Storage::new()
    }
}

#[cfg(test)]
mod test {
    use std::ops::Deref;

    use crate::vm::{
        state::storage::Storage,
        symbolic_value::{
            known_data::KnownData,
            BoxedVal,
            Provenance,
            SymbolicValue,
            SymbolicValueData,
        },
    };

    /// Creates a new synthetic value for testing purposes.
    fn new_synthetic_value(instruction_pointer: u32) -> BoxedVal {
        SymbolicValue::new_value(instruction_pointer, Provenance::Synthetic)
    }

    #[test]
    fn can_construct_new_storage() {
        let storage = Storage::new();
        assert_eq!(storage.entry_count(), 0);
    }

    #[test]
    fn can_store_word_to_storage() {
        let mut storage = Storage::new();
        let key = new_synthetic_value(0);
        let value = new_synthetic_value(1);
        storage.store(key.clone(), value.clone());

        assert_eq!(storage.entry_count(), 1);
        assert_eq!(storage.load(&key), &value);
    }

    #[test]
    fn can_overwrite_word_in_storage() {
        let mut storage = Storage::new();
        let key = new_synthetic_value(0);
        let value_1 = new_synthetic_value(1);
        let value_2 = new_synthetic_value(2);

        storage.store(key.clone(), value_1.clone());
        assert_eq!(storage.entry_count(), 1);
        assert_eq!(storage.load(&key), &value_1);

        storage.store(key.clone(), value_2.clone());
        assert_eq!(storage.entry_count(), 1);
        assert_eq!(storage.load(&key), &value_2);
    }

    #[test]
    fn can_store_word_under_known_key() {
        let mut storage = Storage::new();
        let key = SymbolicValue::new_known_value(0, KnownData::zero(), Provenance::Synthetic);
        let value = new_synthetic_value(1);

        storage.store(key.clone(), value.clone());
        assert_eq!(storage.entry_count(), 1);
        assert_eq!(storage.load(&key), &value);
    }

    #[test]
    fn can_get_zero_if_slot_never_written() {
        let mut storage = Storage::new();
        let key_1 = SymbolicValue::new_known_value(0, KnownData::zero(), Provenance::Synthetic);
        let key_2 = new_synthetic_value(1);

        match storage.load(&key_1).deref() {
            SymbolicValue {
                data: SymbolicValueData::KnownData { value, .. },
                provenance,
                ..
            } => {
                assert_eq!(value, &KnownData::zero());
                assert_eq!(
                    provenance,
                    &Provenance::UninitializedStorage { key: key_1.clone() }
                )
            }
            _ => panic!("Test failure"),
        }

        match &storage.load(&key_2).deref() {
            SymbolicValue {
                data: SymbolicValueData::KnownData { value, .. },
                provenance,
                ..
            } => {
                assert_eq!(value, &KnownData::zero());
                assert_eq!(
                    provenance,
                    &Provenance::UninitializedStorage { key: key_2.clone() }
                )
            }
            _ => panic!("Test failure"),
        }
    }

    #[test]
    fn can_get_all_keys() {
        let mut storage = Storage::new();
        let key_1 = SymbolicValue::new_known_value(0, KnownData::zero(), Provenance::Synthetic);
        let key_2 = new_synthetic_value(1);
        let value = new_synthetic_value(2);
        storage.store(key_1.clone(), value.clone());
        storage.store(key_2.clone(), value);

        let keys = storage.keys();
        assert_eq!(keys, vec![&key_1, &key_2]);
    }
}
