//! This module contains the definition of the virtual machine's memory.

use std::{collections::HashMap, hash::Hash};

use crate::{
    constant::WORD_SIZE_BITS,
    vm::value::{known::KnownWord, Provenance, RuntimeBoxedVal, RSV, RSVD},
};

/// A representation of the transient memory of the symbolic virtual machine.
///
/// Where the memory on a real EVM implementation is word-addressed byte-array
/// that grows as needed, here we are working with symbolic values, and hence
/// can only address portions of that memory by the symbols used to index into
/// it.
///
/// However, to enable more efficient transformation of values and data, we
/// utilise the ability to constant fold values to write to "real" memory
/// locations wherever possible.
///
/// # Generational Memory
///
/// Each memory location stores the total history of writes made to it during
/// the course of a given thread of execution. You can call the `generations`
/// method to get at these for a given key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Memory {
    /// Stores at locations that are described by a constant numeric offset from
    /// the start of memory.
    constant_offsets: HashMap<usize, Vec<MemStore>>,

    /// Stores at locations that are described by a symbolic value that cannot
    /// be treated specially.
    symbolic_offsets: HashMap<RuntimeBoxedVal, Vec<MemStore>>,

    /// The maximum number of symbolic "bytes" that the memory can copy in a
    /// single operation.
    ///
    /// This is used to prevent memory blowup for contracts that make
    /// significant numbers of large copies.
    max_single_operation_bytes: usize,
}

impl Memory {
    /// Constructs a new memory container that currently stores no data.
    #[must_use]
    pub fn new(max_single_operation_bytes: usize) -> Self {
        let constant_offsets = HashMap::default();
        let symbolic_offsets = HashMap::default();
        Self {
            constant_offsets,
            symbolic_offsets,
            max_single_operation_bytes,
        }
    }

    /// Stores the provided `value` (of size [`WORD_SIZE_BITS`]) at the provided
    /// `offset` in the memory.
    ///
    /// This will overwrite any existing value at the provided `offset` for the
    /// purposes of program execution, though previous values are retained as
    /// generations.
    ///
    /// # Note
    ///
    /// Be careful with overlapping stores, as the storage is not able to track
    /// these. Implementation of the `MLOAD` and `MSTORE*` opcodes may want to
    /// account for sub-word writes by dissecting the arguments to this
    /// function.
    pub fn store(&mut self, offset: RuntimeBoxedVal, value: RuntimeBoxedVal) {
        self.store_with_size(offset, value, MemStoreSize::Word);
    }

    /// Stores the provided `value` (of size 8-bits) at the provided `offset`
    /// in the memory.
    ///
    /// This will overwrite any existing value at the provided `offset` for the
    /// purposes of program execution, though previous values are retained as
    /// generations.
    ///
    /// # Note
    ///
    /// Be careful with overlapping stores, as the storage is not able to track
    /// these. Implementation of the `MLOAD` and `MSTORE*` opcodes may want to
    /// account for sub-word writes by dissecting the arguments to this
    /// function.
    pub fn store_8(&mut self, offset: RuntimeBoxedVal, value: RuntimeBoxedVal) {
        self.store_with_size(offset, value, MemStoreSize::Byte);
    }

    /// Performs an internal store of `value` at `offset` using the specified
    /// `size`.
    ///
    /// # Note
    ///
    /// Be careful with overlapping stores, as the storage is not always able to
    /// track these. Implementation of the `MLOAD` and `MSTORE*` opcodes may
    /// want to account for sub-word writes by dissecting the arguments to
    /// this function.
    // We use boxes everywhere for API simplicity.
    #[allow(clippy::boxed_local, clippy::needless_pass_by_value)]
    fn store_with_size(
        &mut self,
        offset: RuntimeBoxedVal,
        value: RuntimeBoxedVal,
        size: MemStoreSize,
    ) {
        let offset = offset.constant_fold();
        let store_value = MemStore { data: value, size };
        let entry = match offset.data() {
            RSVD::KnownData { value } => {
                self.constant_offsets.entry(value.into()).or_insert(vec![])
            }
            _ => self.symbolic_offsets.entry(offset).or_insert(vec![]),
        };

        entry.push(store_value);
    }

    /// Loads the 256-bits at the given `offset` in memory, or returns 0 if the
    /// offset has never been written to.
    ///
    /// This always returns the _most-recently written_ value, and does not
    /// account for the generations.
    ///
    /// # Note
    ///
    /// This is a best-effort analysis as we cannot guarantee knowing if there
    /// have been overwrites between adjacent slots.
    #[must_use]
    pub fn load(&mut self, offset: &RuntimeBoxedVal) -> RuntimeBoxedVal {
        let offset = offset.constant_fold();
        match offset.data() {
            RSVD::KnownData { value } => {
                Self::get_or_initialize(&mut self.constant_offsets, &value.into()).clone()
            }
            _ => Self::get_or_initialize(&mut self.symbolic_offsets, &offset).clone(),
        }
    }

    /// Loads from the memory at `offset` for a `size` in bytes.
    ///
    /// The exact behaviour of this function occurs on a best-effort basis, and
    /// is determined by the kinds of input it is given:
    ///
    /// - Where both the `offset` and `size` are immediates, this will load
    ///   adjacent words from memory and provide them to the caller as a
    ///   [`RSVD::Concat`].
    /// - Where `offset` is an immediate, but `size` is not, it will return only
    ///   the word at `offset`.
    /// - Where `offset` is symbolic, it will return only the word at `offset`.
    ///
    /// Note that we hope to improve this behaviour in the future.
    #[must_use]
    pub fn load_slice(
        &mut self,
        offset: &RuntimeBoxedVal,
        size: &RuntimeBoxedVal,
        instruction_pointer: u32,
    ) -> RuntimeBoxedVal {
        let offset = offset.constant_fold();
        match offset.data() {
            RSVD::KnownData { value } => match Self::decompose_size(size) {
                Some(size) => {
                    let offset: usize = value.into();
                    let mut values = vec![];
                    let bounded_size = size.min(self.max_single_operation_bytes);

                    // Step by 32 bytes at once as each "write" happens at 32-byte alignment
                    for word_offset in (offset..offset + bounded_size).step_by(32) {
                        values.push(
                            Self::get_or_initialize(&mut self.constant_offsets, &word_offset)
                                .clone(),
                        );
                    }

                    RSV::new(
                        instruction_pointer,
                        RSVD::Concat { values },
                        Provenance::Synthetic,
                        None,
                    )
                }
                None => {
                    // If there is no concrete size, we do our best and just return the direct value
                    // at `offset`.
                    Self::get_or_initialize(&mut self.constant_offsets, &value.into()).clone()
                }
            },
            _ => {
                // Here we just do our best and return the single value as we don't track
                // adjacency between symbolic values yet.
                Self::get_or_initialize(&mut self.symbolic_offsets, &offset).clone()
            }
        }
    }

    /// Determines whether the size is concrete, returning the concrete read
    /// size if so, and [`None`] otherwise.
    #[must_use]
    fn decompose_size(size: &RuntimeBoxedVal) -> Option<usize> {
        let size = size.constant_fold();
        match size.data() {
            RSVD::KnownData { value } => Some(value.into()),
            _ => None,
        }
    }

    /// Gets the item at the provided `key` from the provided `map`,
    /// initializing the read memory to all zeroes if it has not previously been
    /// written.
    #[must_use]
    fn get_or_initialize<'a, K>(
        map: &'a mut HashMap<K, Vec<MemStore>>,
        key: &'a K,
    ) -> &'a RuntimeBoxedVal
    where
        K: Clone + Eq + Hash + PartialEq,
    {
        let entry = map.entry(key.clone()).or_insert_with(|| {
            // The instruction pointer is 0 here, as the uninitialized value was created
            // when the program started.
            let data =
                RSV::new_known_value(0, KnownWord::zero(), Provenance::UninitializedMemory, None);

            vec![MemStore {
                data,
                size: MemStoreSize::Word,
            }]
        });

        // This is safe as we always guarantee that there at least one item in the
        // generational vector.
        &entry.last().unwrap().data
    }

    /// Gets all of the stores that were made at the provided `offset` during
    /// the course of execution.
    ///
    /// Returns [`Some`] for offsets that have seen at least one write, and
    /// otherwise returns [`None`].
    #[must_use]
    pub fn generations(&self, offset: &RuntimeBoxedVal) -> Option<Vec<&RuntimeBoxedVal>> {
        self.symbolic_offsets
            .get(offset)
            .map(|stores| stores.iter().map(|store| &store.data).collect())
    }

    /// Asks the memory about the size of the store that was made at a given
    /// location.
    ///
    /// This functionality exists primarily for introspection.
    #[must_use]
    pub fn query_store_size(&self, offset: &RuntimeBoxedVal) -> Option<MemStoreSize> {
        self.symbolic_offsets
            .get(offset)
            .and_then(|generations| generations.first())
            .map(|result| result.size)
    }

    /// Asks the memory for the number of entries it has in it.
    ///
    /// This has no equivalent operation on the EVM and is primarily useful for
    /// introspection.
    #[must_use]
    pub fn entry_count(&self) -> usize {
        self.symbolic_offsets.len() + self.constant_offsets.len()
    }

    /// Checks if the memory has ever been written to.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entry_count() == 0
    }

    /// Gets the offsets in memory that have been written to.
    #[must_use]
    pub fn offsets(&self) -> Vec<&RuntimeBoxedVal> {
        self.symbolic_offsets.keys().collect()
    }

    /// Consumes the memory and returns all values that are registered in it.
    #[must_use]
    pub fn all_values(self) -> Vec<RuntimeBoxedVal> {
        let mut values = Vec::new();
        self.constant_offsets
            .into_values()
            .for_each(|more| values.extend(more.into_iter().map(|s| s.data)));
        self.symbolic_offsets.into_iter().for_each(|(key, more)| {
            values.push(key);
            values.extend(more.into_iter().map(|s| s.data));
        });

        values
    }
}

/// The data that actually gets stored into memory.
#[derive(Clone, Debug, Eq, PartialEq)]
struct MemStore {
    data: RuntimeBoxedVal,
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
    #[must_use]
    pub fn bits_count(&self) -> usize {
        match self {
            MemStoreSize::Byte => 8,
            MemStoreSize::Word => WORD_SIZE_BITS,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        constant::DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES,
        vm::{
            state::memory::{MemStoreSize, Memory},
            value::{known::KnownWord, Provenance, RuntimeBoxedVal, RSV, RSVD},
        },
    };

    /// Creates a new synthetic value for testing purposes.
    #[allow(clippy::unnecessary_box_returns)] // We use boxes everywhere during execution
    fn new_synthetic_value(instruction_pointer: u32) -> RuntimeBoxedVal {
        RSV::new_value(instruction_pointer, Provenance::Synthetic)
    }

    #[test]
    fn can_construct_new_memory() {
        let memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        assert_eq!(memory.entry_count(), 0);
    }

    #[test]
    fn can_store_word_to_memory() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        let offset = new_synthetic_value(0);
        let value = new_synthetic_value(1);
        memory.store(offset.clone(), value.clone());

        assert_eq!(memory.entry_count(), 1);
        assert_eq!(memory.load(&offset), value);
        assert_eq!(
            memory.query_store_size(&offset).unwrap(),
            MemStoreSize::Word
        );
    }

    #[test]
    fn can_overwrite_word_in_memory() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        let offset = new_synthetic_value(0);
        let value_1 = new_synthetic_value(1);
        let value_2 = new_synthetic_value(2);

        memory.store(offset.clone(), value_1.clone());
        let load = memory.load(&offset);
        assert_eq!(load, value_1);

        memory.store(offset.clone(), value_2.clone());
        let load = memory.load(&offset);
        assert_eq!(load, value_2);
    }

    #[test]
    fn can_store_byte_to_memory() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        let offset = new_synthetic_value(0);
        let value = new_synthetic_value(1);
        memory.store_8(offset.clone(), value.clone());

        assert_eq!(memory.entry_count(), 1);
        assert_eq!(memory.load(&offset), value);
        assert_eq!(
            memory.query_store_size(&offset).unwrap(),
            MemStoreSize::Byte
        );
    }

    #[test]
    fn can_overwrite_byte_in_memory() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        let offset = new_synthetic_value(0);
        let value_1 = new_synthetic_value(1);
        let value_2 = new_synthetic_value(2);

        memory.store_8(offset.clone(), value_1.clone());
        let load = memory.load(&offset);
        assert_eq!(load, value_1);

        memory.store_8(offset.clone(), value_2.clone());
        let load = memory.load(&offset);
        assert_eq!(load, value_2);
    }

    #[test]
    fn can_get_written_entry_in_memory() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        let offset = new_synthetic_value(0);
        let value = new_synthetic_value(1);

        memory.store(offset.clone(), value.clone());

        let loaded = memory.load(&offset);
        assert_eq!(loaded, value);
    }

    #[test]
    fn can_get_zero_if_memory_offset_never_written() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        let offset = new_synthetic_value(0);

        let loaded = memory.load(&offset);
        assert_eq!(loaded.instruction_pointer(), 0);
        assert_eq!(loaded.provenance(), Provenance::UninitializedMemory);

        match loaded.data() {
            RSVD::KnownData { value } => {
                assert_eq!(value, &KnownWord::zero());
            }
            _ => panic!("Incorrect payload"),
        }
    }

    #[test]
    fn can_load_multiple_words_if_known_size() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        let zero = KnownWord::zero();
        let thirty_two = KnownWord::from(32);
        let offset_1 = RSV::new_known_value(0, zero, Provenance::Synthetic, None);
        let value_1 = new_synthetic_value(1);
        let offset_2 = RSV::new_known_value(1, thirty_two, Provenance::Synthetic, None);
        let value_2 = new_synthetic_value(3);
        let sixty_four = KnownWord::from(64);
        let bytes_64 = RSV::new_known_value(4, sixty_four, Provenance::Synthetic, None);

        // Store under known offsets
        memory.store(offset_1.clone(), value_1.clone());
        memory.store(offset_2, value_2.clone());

        // Read it back
        let result = memory.load_slice(&offset_1, &bytes_64, 5);
        match result.data() {
            RSVD::Concat { values } => {
                assert_eq!(values, &vec![value_1, value_2]);
            }
            _ => panic!("Invalid payload"),
        }
    }

    #[test]
    fn can_load_word_at_known_offset_with_symbolic_size() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        let zero = KnownWord::zero();
        let offset = RSV::new_known_value(0, zero, Provenance::Synthetic, None);
        let value = new_synthetic_value(1);
        let size = new_synthetic_value(2);

        // Store under known offsets
        memory.store(offset.clone(), value.clone());

        // Read it back
        let result = memory.load_slice(&offset, &size, 5);
        assert_eq!(result, value);
    }

    #[test]
    fn can_get_entry_count_of_memory() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
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
    #[allow(clippy::similar_names)] // The names are actually perfectly descriptive
    fn can_store_and_retrieve_more_complex_values() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        let left = new_synthetic_value(0);
        let right = new_synthetic_value(1);
        let sum = RSV::new_synthetic(
            2,
            RSVD::Add {
                left:  left.clone(),
                right: right.clone(),
            },
        );
        let prod = RSV::new_synthetic(
            3,
            RSVD::Multiply {
                left:  left.clone(),
                right: right.clone(),
            },
        );
        let sub = RSV::new_synthetic(
            4,
            RSVD::Subtract {
                left:  left.clone(),
                right: right.clone(),
            },
        );
        let div = RSV::new_synthetic(
            5,
            RSVD::Divide {
                dividend: left,
                divisor:  right,
            },
        );

        memory.store(sum.clone(), prod.clone());
        assert_eq!(memory.entry_count(), 1);
        assert_eq!(memory.load(&sum), prod);

        memory.store(sub.clone(), div.clone());
        assert_eq!(memory.entry_count(), 2);
        assert_eq!(memory.load(&sub), div);
    }

    #[test]
    fn can_access_generations_at_offset() {
        let mut memory = Memory::new(DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES);
        let offset = new_synthetic_value(0);
        let value_1 = new_synthetic_value(1);
        let value_2 = new_synthetic_value(2);

        memory.store(offset.clone(), value_1.clone());
        memory.store(offset.clone(), value_2.clone());

        let generations = memory.generations(&offset).unwrap();
        assert_eq!(generations, vec![&value_1, &value_2]);
    }
}
