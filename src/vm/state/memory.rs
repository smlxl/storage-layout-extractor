//! This module contains the definition of the virtual machine's memory.

use std::collections::HashMap;

use crate::vm::value::{known_data::KnownData, BoxedVal, Provenance, SymbolicValue};

/// A representation of the transient memory of the symbolic virtual machine.
///
/// Where the memory on a real EVM implementation is word-addressed byte-array
/// that grows as needed, here we are working with symbolic values, and hence
/// can only address portions of that memory by the symbols used to index into
/// it.
///
/// To that end, the memory for the symbolic EVM maps from symbolic expressions
/// to other symbolic expressions, relying on the identity or similarity of
/// symbolic expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Memory {
    mem: HashMap<BoxedVal, MemStore>,
}

impl Memory {
    /// Constructs a new memory container that currently stores no data.
    pub fn new() -> Self {
        let mem = HashMap::default();
        Self { mem }
    }

    /// Stores the provided `value` (of size 256-bits) at the provided `offset`
    /// in the memory.
    ///
    /// This will overwrite any existing value at the provided `offset`.
    ///
    /// # Note
    ///
    /// Be careful with overlapping stores, as the storage is not able to track
    /// these. Implementation of the `MLOAD` and `MSTORE*` opcodes may want to
    /// account for sub-word writes by dissecting the arguments to this
    /// function.
    pub fn store(&mut self, offset: BoxedVal, value: BoxedVal) {
        let store_value = MemStore {
            data: value,
            size: MemStoreSize::Word,
        };
        self.mem.insert(offset, store_value);
    }

    /// Stores the provided `value` (of size 8-bits) at the provided `offset`
    /// in the memory.
    ///
    /// This will overwrite any existing value at the provided `offset`.
    ///
    /// # Note
    ///
    /// Be careful with overlapping stores, as the storage is not able to track
    /// these. Implementation of the `MLOAD` and MSTORE*` opcodes may want to
    /// account for sub-word writes by dissecting the arguments to this
    /// function.
    pub fn store_8(&mut self, offset: BoxedVal, value: BoxedVal) {
        let store_value = MemStore {
            data: value,
            size: MemStoreSize::Byte,
        };
        self.mem.insert(offset, store_value);
    }

    /// Loads the 256-bits at the given `offset` in memory, or returns 0 if the
    /// offset has never been written to.
    ///
    /// # Note
    ///
    /// This is a best-effort analysis as we cannot guarantee knowing if there
    /// have been overwrites between adjacent slots.
    pub fn load(&mut self, offset: &BoxedVal) -> &BoxedVal {
        &self
            .mem
            .entry(offset.clone())
            .or_insert_with(|| {
                // The instruction pointer is 0 here, as the uninitialized value was created
                // when the program started.

                let data = SymbolicValue::new_known_value(
                    0,
                    KnownData::zero(),
                    Provenance::UninitializedMemory,
                );
                MemStore {
                    data,
                    size: MemStoreSize::Word,
                }
            })
            .data
    }

    /// Asks the memory about the size of the store that was made at a given
    /// location.
    ///
    /// This functionality exists primarily for introspection.
    pub fn query_store_size(&self, offset: &BoxedVal) -> Option<MemStoreSize> {
        self.mem.get(offset).map(|result| result.size)
    }

    /// Asks the memory for the number of entries it has in it.
    ///
    /// This has no equivalent operation on the EVM and is primarily useful for
    /// introspection.
    pub fn entry_count(&self) -> usize {
        self.mem.len()
    }

    /// Checks if the memory has ever been written to.
    pub fn is_empty(&self) -> bool {
        self.entry_count() == 0
    }
}

impl Default for Memory {
    fn default() -> Self {
        Memory::new()
    }
}

/// The data that actually gets stored into memory.
#[derive(Clone, Debug, Eq, PartialEq)]
struct MemStore {
    data: BoxedVal,
    size: MemStoreSize,
}

/// The type of memory storage operation associated with the data at a given
/// "location".
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum MemStoreSize {
    Byte,
    Word,
}

impl MemStoreSize {
    /// Gets the number of bits that were stored into memory for a given write.
    pub fn bits_count(&self) -> usize {
        match self {
            MemStoreSize::Byte => 8,
            MemStoreSize::Word => 256,
        }
    }
}

#[cfg(test)]
mod test {
    use std::ops::Deref;

    use crate::vm::{
        state::memory::{MemStoreSize, Memory},
        value::{known_data::KnownData, BoxedVal, Provenance, SymbolicValue, SymbolicValueData},
    };

    /// Creates a new synthetic value for testing purposes.
    fn new_synthetic_value(instruction_pointer: u32) -> BoxedVal {
        SymbolicValue::new_value(instruction_pointer, Provenance::Synthetic)
    }

    #[test]
    fn can_construct_new_memory() {
        let memory = Memory::new();
        assert_eq!(memory.entry_count(), 0);
    }

    #[test]
    fn can_store_word_to_memory() {
        let mut memory = Memory::new();
        let offset = new_synthetic_value(0);
        let value = new_synthetic_value(1);
        memory.store(offset.clone(), value.clone());

        assert_eq!(memory.entry_count(), 1);
        assert_eq!(memory.load(&offset), &value);
        assert_eq!(
            memory.query_store_size(&offset).unwrap(),
            MemStoreSize::Word
        )
    }

    #[test]
    fn can_overwrite_word_in_memory() {
        let mut memory = Memory::new();
        let offset = new_synthetic_value(0);
        let value_1 = new_synthetic_value(1);
        let value_2 = new_synthetic_value(2);

        memory.store(offset.clone(), value_1.clone());
        let load = memory.load(&offset);
        assert_eq!(load, &value_1);

        memory.store(offset.clone(), value_2.clone());
        let load = memory.load(&offset);
        assert_eq!(load, &value_2);
    }

    #[test]
    fn can_store_byte_to_memory() {
        let mut memory = Memory::new();
        let offset = new_synthetic_value(0);
        let value = new_synthetic_value(1);
        memory.store_8(offset.clone(), value.clone());

        assert_eq!(memory.entry_count(), 1);
        assert_eq!(memory.load(&offset), &value);
        assert_eq!(
            memory.query_store_size(&offset).unwrap(),
            MemStoreSize::Byte
        )
    }

    #[test]
    fn can_overwrite_byte_in_memory() {
        let mut memory = Memory::new();
        let offset = new_synthetic_value(0);
        let value_1 = new_synthetic_value(1);
        let value_2 = new_synthetic_value(2);

        memory.store_8(offset.clone(), value_1.clone());
        let load = memory.load(&offset);
        assert_eq!(load, &value_1);

        memory.store_8(offset.clone(), value_2.clone());
        let load = memory.load(&offset);
        assert_eq!(load, &value_2);
    }

    #[test]
    fn can_get_written_entry_in_memory() {
        let mut memory = Memory::new();
        let offset = new_synthetic_value(0);
        let value = new_synthetic_value(1);

        memory.store(offset.clone(), value.clone());

        let loaded = memory.load(&offset);
        assert_eq!(loaded, &value);
    }

    #[test]
    fn can_get_zero_if_memory_offset_never_written() {
        let mut memory = Memory::new();
        let offset = new_synthetic_value(0);

        let loaded = memory.load(&offset).deref();
        assert_eq!(loaded.instruction_pointer, 0);

        match loaded {
            SymbolicValue {
                data: SymbolicValueData::KnownData { value, .. },
                provenance,
                ..
            } => {
                assert_eq!(value, &KnownData::zero());
                assert_eq!(provenance, &Provenance::UninitializedMemory,);
            }
            _ => panic!("Test failure"),
        }
    }

    #[test]
    fn can_get_entry_count_of_memory() {
        let mut memory = Memory::new();
        let offset_1 = new_synthetic_value(0);
        let value_1 = new_synthetic_value(1);
        let offset_2 = new_synthetic_value(0);
        let value_2 = new_synthetic_value(2);

        assert!(memory.is_empty());

        memory.store(offset_1, value_1);
        assert_eq!(memory.entry_count(), 1);

        memory.store(offset_2, value_2);
        assert_eq!(memory.entry_count(), 2);
    }

    #[test]
    fn can_store_and_retrieve_more_complex_values() {
        let mut memory = Memory::new();
        let left = new_synthetic_value(0);
        let right = new_synthetic_value(1);
        let sum = SymbolicValue::new_synthetic(
            2,
            SymbolicValueData::Add {
                left:  left.clone(),
                right: right.clone(),
            },
        );
        let prod = SymbolicValue::new_synthetic(
            3,
            SymbolicValueData::Mul {
                left:  left.clone(),
                right: right.clone(),
            },
        );
        let sub = SymbolicValue::new_synthetic(
            4,
            SymbolicValueData::Sub {
                left:  left.clone(),
                right: right.clone(),
            },
        );
        let div = SymbolicValue::new_synthetic(
            5,
            SymbolicValueData::Div {
                dividend: left,
                divisor:  right,
            },
        );

        memory.store(sum.clone(), prod.clone());
        assert_eq!(memory.entry_count(), 1);
        assert_eq!(memory.load(&sum), &prod);

        memory.store(sub.clone(), div.clone());
        assert_eq!(memory.entry_count(), 2);
        assert_eq!(memory.load(&sub), &div);
    }
}
