//! This module contains the definition of the virtual machine's memory.

use std::collections::HashMap;

use crate::vm::symbolic_value::BoxedVal;

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
    /// these. Implementation of the `MLOAD` and MSTORE*` opcodes may want to
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

    /// Loads the 256-bits at the given `offset` in memory.
    ///
    /// If the value at `offset` does not exist, it returns [`None`]. This
    /// leaves it up to the caller to implement a sensible return value in its
    /// place.
    ///
    /// On the EVM, reading from "uninitialized" regions of memory returns all
    /// zeroes.
    pub fn load(&self, offset: &BoxedVal) -> Option<&BoxedVal> {
        self.mem.get(offset).map(|result| &result.data)
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
    pub fn entries(&self) -> usize {
        self.mem.len()
    }

    /// Checks if the memory has ever been written to.
    pub fn is_empty(&self) -> bool {
        self.entries() == 0
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
    use crate::vm::{
        state::memory::{MemStoreSize, Memory},
        symbolic_value::{SymbolicValue, SymbolicValueData},
    };

    #[test]
    fn can_construct_new_memory() {
        let memory = Memory::new();
        assert_eq!(memory.entries(), 0);
    }

    #[test]
    fn can_store_word_to_memory() {
        let mut memory = Memory::new();
        let offset = SymbolicValue::new_value(0);
        let value = SymbolicValue::new_value(1);
        memory.store(offset.clone(), value.clone());

        assert_eq!(memory.entries(), 1);
        assert_eq!(memory.load(&offset), Some(&value));
        assert_eq!(
            memory.query_store_size(&offset).unwrap(),
            MemStoreSize::Word
        )
    }

    #[test]
    fn can_overwrite_word_in_memory() {
        let mut memory = Memory::new();
        let offset = SymbolicValue::new_value(0);
        let value_1 = SymbolicValue::new_value(1);
        let value_2 = SymbolicValue::new_value(2);

        memory.store(offset.clone(), value_1.clone());
        let load = memory.load(&offset);
        assert!(load.is_some());
        assert_eq!(load.unwrap(), &value_1);

        memory.store(offset.clone(), value_2.clone());
        let load = memory.load(&offset);
        assert!(load.is_some());
        assert_eq!(load.unwrap(), &value_2);
    }

    #[test]
    fn can_store_byte_to_memory() {
        let mut memory = Memory::new();
        let offset = SymbolicValue::new_value(0);
        let value = SymbolicValue::new_value(1);
        memory.store_8(offset.clone(), value.clone());

        assert_eq!(memory.entries(), 1);
        assert_eq!(memory.load(&offset), Some(&value));
        assert_eq!(
            memory.query_store_size(&offset).unwrap(),
            MemStoreSize::Byte
        )
    }

    #[test]
    fn can_overwrite_byte_in_memory() {
        let mut memory = Memory::new();
        let offset = SymbolicValue::new_value(0);
        let value_1 = SymbolicValue::new_value(1);
        let value_2 = SymbolicValue::new_value(2);

        memory.store_8(offset.clone(), value_1.clone());
        let load = memory.load(&offset);
        assert!(load.is_some());
        assert_eq!(load.unwrap(), &value_1);

        memory.store_8(offset.clone(), value_2.clone());
        let load = memory.load(&offset);
        assert!(load.is_some());
        assert_eq!(load.unwrap(), &value_2);
    }

    #[test]
    fn can_get_entry_count_of_memory() {
        let mut memory = Memory::new();
        let offset_1 = SymbolicValue::new_value(0);
        let value_1 = SymbolicValue::new_value(1);
        let offset_2 = SymbolicValue::new_value(0);
        let value_2 = SymbolicValue::new_value(2);

        assert!(memory.is_empty());

        memory.store(offset_1, value_1);
        assert_eq!(memory.entries(), 1);

        memory.store(offset_2, value_2);
        assert_eq!(memory.entries(), 2);
    }

    #[test]
    fn can_store_and_retrieve_more_complex_values() {
        let mut memory = Memory::new();
        let left = SymbolicValue::new_value(0);
        let right = SymbolicValue::new_value(1);
        let sum = SymbolicValue::new(
            2,
            SymbolicValueData::Add {
                left:  left.clone(),
                right: right.clone(),
            },
        );
        let prod = SymbolicValue::new(
            3,
            SymbolicValueData::Mul {
                left:  left.clone(),
                right: right.clone(),
            },
        );
        let sub = SymbolicValue::new(
            4,
            SymbolicValueData::Sub {
                left:  left.clone(),
                right: right.clone(),
            },
        );
        let div = SymbolicValue::new(
            5,
            SymbolicValueData::Div {
                dividend: left.clone(),
                divisor:  right.clone(),
            },
        );

        memory.store(sum.clone(), prod.clone());
        assert_eq!(memory.entries(), 1);
        assert_eq!(memory.load(&sum).unwrap(), &prod);

        memory.store(sub.clone(), div.clone());
        assert_eq!(memory.entries(), 2);
        assert_eq!(memory.load(&sub).unwrap(), &div);
    }
}
