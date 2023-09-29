//! This module contains the definition of the virtual machine's storage
//! container.

use std::collections::HashMap;

use crate::vm::value::{Provenance, RuntimeBoxedVal, RSV, RSVD};

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
///
/// # Generational Storage
///
/// Each storage location stores the total history of writes made to it during
/// the course of a given thread of execution. You can call the `generations`
/// method to get at these for a given key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Storage {
    /// Many storage writes are in the form of a known slot index.
    known_slots: HashMap<RuntimeBoxedVal, Vec<RuntimeBoxedVal>>,

    /// Others use symbolic values as offsets.
    symbolic_slots: HashMap<RuntimeBoxedVal, Vec<RuntimeBoxedVal>>,
}

impl Storage {
    /// Creates a new, empty storage.
    #[must_use]
    pub fn new() -> Self {
        let fixed_slots = HashMap::new();
        let symbolic_slots = HashMap::new();
        Self {
            known_slots: fixed_slots,
            symbolic_slots,
        }
    }

    /// Stores the provided `value` in storage at the provided `key`,
    /// overwriting any existing value at that key for the purposes of
    /// execution.
    ///
    /// Any previous values are retained in the generations, and the `value` is
    /// treated as being 256 bits wide.
    pub fn store(&mut self, key: RuntimeBoxedVal, value: RuntimeBoxedVal) {
        let target_map = match key.data() {
            RSVD::KnownData { .. } => &mut self.known_slots,
            _ => &mut self.symbolic_slots,
        };
        let entry = target_map.entry(key).or_insert(vec![]);
        entry.push(value);
    }

    /// Loads the value found at the provided `key`.
    ///
    /// This always returns the _most-recently written_ value, and does not
    /// account for the generations.
    ///
    /// If the slot has not been written to during the current execution, it
    /// returns a symbolic value representing the potential value of the slot.
    ///
    /// # Note
    ///
    /// This is a best-effort analysis as we cannot guarantee knowing if there
    /// have been overwrites between adjacent slots.
    #[allow(clippy::missing_panics_doc)] // Panics are guarded
    #[must_use]
    pub fn load(&mut self, key: &RuntimeBoxedVal) -> RuntimeBoxedVal {
        // First we need to work out which of the maps to read from.
        let target_map = match key.data() {
            RSVD::KnownData { .. } => &mut self.known_slots,
            _ => &mut self.symbolic_slots,
        };

        // Once we have that we can pull the key out, or default in the map if it
        // doesn't exist
        let entry = target_map.entry(key.clone()).or_insert_with(|| {
            // The instruction pointer is 0 here, as the uninitialized value was created
            // when the program started. It is _not_ synthetic.

            vec![RSV::new(
                0,
                RSVD::UnwrittenStorageValue { key: key.clone() },
                Provenance::NonWrittenStorage,
                None,
            )]
        });

        let most_recent = entry
            .last()
            .expect("We already know there is at least one item in the vector");

        // We wrap the loaded value in an `SLoad` as long as it is not already wrapped
        // in one, thereby letting us know at which point in the computation of the
        // value tree the value was loaded from storage.
        //
        // Knowing this is very important in the context of deciding which portions of
        // storage slots are not truly used, as they will contain near-direct loads from
        // the same slot.
        RSV::new(
            most_recent.instruction_pointer(),
            if let RSVD::SLoad { .. } = &most_recent.data() {
                most_recent.data().clone()
            } else {
                RSVD::SLoad {
                    key:   key.clone(),
                    value: most_recent.clone(),
                }
            },
            most_recent.provenance(),
            None,
        )
    }

    /// Gets all of the stores that were made at the provided `key` during
    /// the course of execution.
    ///
    /// Returns [`Some`] for keys that have seen at least one write, and
    /// otherwise returns [`None`].
    #[must_use]
    pub fn generations(&self, key: &RuntimeBoxedVal) -> Option<Vec<&RuntimeBoxedVal>> {
        let target_map = match key.data() {
            RSVD::KnownData { .. } => &self.known_slots,
            _ => &self.symbolic_slots,
        };

        target_map.get(key).map(|generations| generations.iter().collect())
    }

    /// Gets the number of entries in the storage.
    #[must_use]
    pub fn entry_count(&self) -> usize {
        self.known_slots.len() + self.symbolic_slots.len()
    }

    /// Gets the slot keys for this storage that have been written to.
    #[must_use]
    pub fn keys(&self) -> Vec<&RuntimeBoxedVal> {
        let mut known_keys: Vec<&RuntimeBoxedVal> = self.known_slots.keys().collect();
        let symbolic_keys: Vec<&RuntimeBoxedVal> = self.symbolic_slots.keys().collect();

        known_keys.extend(symbolic_keys);

        known_keys
    }

    /// Gets all of the values that are registered in the virtual machine stack
    /// at the time of calling.
    #[must_use]
    pub fn all_values(&self) -> Vec<RuntimeBoxedVal> {
        let mut values = Vec::new();
        values.extend(self.known_slots.keys().cloned());
        self.known_slots
            .values()
            .for_each(|more| values.extend(more.iter().cloned()));
        values.extend(self.symbolic_slots.keys().cloned());
        self.symbolic_slots
            .values()
            .for_each(|more| values.extend(more.iter().cloned()));

        values
    }

    /// Consumes the storage and returns all of the values that were contained
    /// within the storage.
    ///
    /// Here, each `key -> value` pair, accounting for generations, is wrapped
    /// into [`RSVD::StorageWrite`] of `(key, value)`, allowing for easier
    /// analysis later.
    #[must_use]
    pub fn stores_as_values(self) -> Vec<RuntimeBoxedVal> {
        let mut all_values: Vec<RuntimeBoxedVal> = Vec::new();

        self.known_slots
            .into_iter()
            .chain(self.symbolic_slots)
            .for_each(|(k, vs)| {
                all_values.extend(vs.into_iter().map(|v| {
                    let provenance = v.provenance();
                    RSV::new(
                        v.instruction_pointer(),
                        RSVD::StorageWrite {
                            key:   k.clone(),
                            value: v,
                        },
                        provenance,
                        None,
                    )
                }));
            });

        all_values
    }
}

impl Default for Storage {
    fn default() -> Self {
        Storage::new()
    }
}

#[cfg(test)]
mod test {
    use crate::vm::{
        state::storage::Storage,
        value::{known::KnownWord, Provenance, RuntimeBoxedVal, RSV, RSVD},
    };

    /// Creates a new synthetic value for testing purposes.
    #[allow(clippy::unnecessary_box_returns)] // We use boxes everywhere during execution
    fn new_synthetic_value(instruction_pointer: u32) -> RuntimeBoxedVal {
        RSV::new_value(instruction_pointer, Provenance::Synthetic)
    }

    #[test]
    fn can_construct_new_storage() {
        let storage = Storage::new();
        assert_eq!(storage.entry_count(), 0);
    }

    #[test]
    fn can_store_word_to_storage() {
        let mut storage = Storage::new();
        let input_key = new_synthetic_value(0);
        let input_value = new_synthetic_value(1);
        storage.store(input_key.clone(), input_value.clone());

        assert_eq!(storage.entry_count(), 1);
        match storage.load(&input_key).data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &input_key);
                assert_eq!(value, &input_value);
            }
            _ => panic!("Incorrect payload"),
        }
    }

    #[test]
    fn can_overwrite_word_in_storage() {
        let mut storage = Storage::new();
        let input_key = new_synthetic_value(0);
        let value_1 = new_synthetic_value(1);
        let value_2 = new_synthetic_value(2);

        storage.store(input_key.clone(), value_1.clone());
        assert_eq!(storage.entry_count(), 1);
        match storage.load(&input_key).data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &input_key);
                assert_eq!(value, &value_1);
            }
            _ => panic!("Incorrect payload"),
        }

        storage.store(input_key.clone(), value_2.clone());
        assert_eq!(storage.entry_count(), 1);
        match storage.load(&input_key).data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &input_key);
                assert_eq!(value, &value_2);
            }
            _ => panic!("Incorrect payload"),
        }
    }

    #[test]
    fn can_store_word_under_known_key() {
        let mut storage = Storage::new();
        let input_key = RSV::new_known_value(0, KnownWord::zero(), Provenance::Synthetic, None);
        let input_value = new_synthetic_value(1);

        storage.store(input_key.clone(), input_value.clone());
        assert_eq!(storage.entry_count(), 1);
        match storage.load(&input_key).data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &input_key);
                assert_eq!(value, &input_value);
            }
            _ => panic!("Incorrect payload"),
        }
    }

    #[test]
    fn can_get_zero_if_slot_never_written() {
        let mut storage = Storage::new();
        let key_1 = RSV::new_known_value(0, KnownWord::zero(), Provenance::Synthetic, None);
        let key_2 = new_synthetic_value(1);

        let load = storage.load(&key_1);
        assert_eq!(load.provenance(), Provenance::NonWrittenStorage);
        match load.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &key_1);
                assert_eq!(
                    value,
                    &RSV::new(
                        0,
                        RSVD::UnwrittenStorageValue { key: key_1 },
                        Provenance::NonWrittenStorage,
                        None,
                    )
                );
            }
            _ => panic!("Invalid payload"),
        }

        let load = storage.load(&key_2);
        assert_eq!(load.provenance(), Provenance::NonWrittenStorage);
        assert_eq!(load.provenance(), Provenance::NonWrittenStorage);
        match load.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &key_2);
                assert_eq!(
                    value,
                    &RSV::new(
                        0,
                        RSVD::UnwrittenStorageValue { key: key_2 },
                        Provenance::NonWrittenStorage,
                        None,
                    )
                );
            }
            _ => panic!("Invalid payload"),
        }
    }

    #[test]
    fn can_get_all_keys() {
        let mut storage = Storage::new();
        let key_1 = RSV::new_known_value(0, KnownWord::zero(), Provenance::Synthetic, None);
        let key_2 = new_synthetic_value(1);
        let value = new_synthetic_value(2);
        storage.store(key_1.clone(), value.clone());
        storage.store(key_2.clone(), value);

        let keys = storage.keys();
        assert_eq!(keys, vec![&key_1, &key_2]);
    }

    #[test]
    fn can_query_generations() {
        let mut storage = Storage::new();
        let key = new_synthetic_value(0);
        let value_1 = new_synthetic_value(1);
        let value_2 = new_synthetic_value(2);

        storage.store(key.clone(), value_1.clone());
        storage.store(key.clone(), value_2.clone());

        let generations = storage.generations(&key).unwrap();
        assert_eq!(generations, vec![&value_1, &value_2]);
    }
}
