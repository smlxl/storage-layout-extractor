//! The state representation for the symbolic virtual machine, and utilities for
//! dealing with said representation.

pub mod memory;
pub mod stack;
pub mod storage;

use crate::vm::{
    state::{memory::Memory, stack::Stack, storage::Storage},
    value::BoxedVal,
};

/// The state representation for the [`super::VM`].
///
/// This state is responsible for maintaining the symbolic memory locations for
/// each of the virtual machine's stack, storage, and memory. Having this will
/// allow the virtual machine to symbolically execute the bytecode and trace the
/// flow of data (locations) and operations through the program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VMState {
    fork_point:      u32,
    stack:           Stack,
    memory:          Memory,
    storage:         Storage,
    recorded_values: Vec<BoxedVal>,
}

impl VMState {
    /// Constructs a new virtual machine state originating at the provided
    /// `fork_point`, with all memory locations set to their default values
    pub fn new(fork_point: u32) -> Self {
        let stack = Stack::new();
        let memory = Memory::new();
        let storage = Storage::new();
        let recorded_values = Vec::default();

        Self {
            fork_point,
            stack,
            memory,
            storage,
            recorded_values,
        }
    }

    /// Gets the stack associated with this virtual machine state.
    pub fn stack(&mut self) -> &mut Stack {
        &mut self.stack
    }

    /// Gets the memory associated with this virtual machine state.
    pub fn memory(&mut self) -> &mut Memory {
        &mut self.memory
    }

    /// Gets the storage associated with this virtual machine state.
    pub fn storage(&mut self) -> &mut Storage {
        &mut self.storage
    }

    /// Records the provided `value` so that it is available for later analysis
    /// even if it is no longer accounted for in one of the VM's working
    /// memories.
    pub fn record_value(&mut self, value: BoxedVal) {
        self.recorded_values.push(value);
    }

    /// Gets the values that have been recorded to be available for analysis
    /// though not stored in the VM's working memories.
    pub fn recorded_values(&self) -> &[BoxedVal] {
        self.recorded_values.as_slice()
    }

    /// Gets the point in the instruction stream, specifically the value of the
    /// instruction pointer, at which this VM state was forked.
    pub fn fork_point(&self) -> u32 {
        self.fork_point
    }

    /// Forks the virtual machine state, returning a new state that at the point
    /// of the fork (given by `instruction_pointer`) is identical to the state
    /// it was forked from.
    ///
    /// This is used for exploring all branches of the bytecode.
    pub fn fork(&self, fork_point: u32) -> Self {
        let mut fork = self.clone();
        fork.fork_point = fork_point;

        fork
    }
}

impl Default for VMState {
    /// Creates a new virtual machine state with the fork point set to the
    /// initial program counter value of zero.
    fn default() -> Self {
        VMState::new(0)
    }
}

#[cfg(test)]
mod test {
    use crate::vm::{
        state::VMState,
        value::{SymbolicValue, SymbolicValueData},
    };

    #[test]
    fn can_construct_vm_state() {
        let state = VMState::new(10);
        assert_eq!(state.fork_point(), 10);
    }

    #[test]
    fn can_construct_default_vm_state() {
        let state = VMState::default();
        assert_eq!(state.fork_point(), 0);
    }

    #[test]
    fn can_record_symbolic_value() {
        let mut state = VMState::default();
        let value = SymbolicValue::new_synthetic(0, SymbolicValueData::default());
        state.record_value(value.clone());

        let values = state.recorded_values();
        assert_eq!(values.len(), 1);
        assert_eq!(values[0], value);
    }

    #[test]
    fn can_fork_state() -> anyhow::Result<()> {
        let value = SymbolicValue::new_synthetic(0, SymbolicValueData::default());
        let state = VMState::default();
        let mut forked_state = state.fork(78);

        // The fork points should differ.
        assert_eq!(state.fork_point(), 0);
        assert_eq!(forked_state.fork_point(), 78);

        // We can modify one.
        forked_state.stack.push(value.clone())?;
        forked_state.memory.store(value.clone(), value.clone());
        forked_state.storage.store(value.clone(), value);
        assert_eq!(forked_state.stack.size(), 1);
        assert_eq!(forked_state.memory.entry_count(), 1);
        assert_eq!(forked_state.storage.entry_count(), 1);

        // Without modifying the other.
        assert_eq!(state.stack.size(), 0);
        assert_eq!(state.memory.entry_count(), 0);
        assert_eq!(state.storage.entry_count(), 0);

        Ok(())
    }
}
