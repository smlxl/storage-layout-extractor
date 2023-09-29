//! The state representation for the symbolic virtual machine, and utilities for
//! dealing with said representation.

pub mod memory;
pub mod stack;
pub mod storage;

use crate::vm::{
    data::VisitedOpcodes,
    state::{memory::Memory, stack::Stack, storage::Storage},
    value::RuntimeBoxedVal,
    Config,
};

/// The state representation for the [`super::VM`].
///
/// This state is responsible for maintaining the symbolic memory locations for
/// each of the virtual machine's stack, storage, and memory. Having this will
/// allow the virtual machine to symbolically execute the bytecode and trace the
/// flow of data and operations through the program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VMState {
    /// The point during execution at which this state was forked.
    fork_point: u32,

    /// The virtual machine stack for this thread of execution.
    stack: Stack,

    /// The symbolic EVM memory for this thread of execution.
    memory: Memory,

    /// The symbolic EVM storage for this thread of execution.
    storage: Storage,

    /// A container for values that would otherwise be dropped but that might
    /// still be useful when it comes to later analysis.
    recorded_values: Vec<RuntimeBoxedVal>,

    /// Values that were logged to the EVM's logging subsystem.
    logged_values: Vec<RuntimeBoxedVal>,

    /// The virtual machine's configuration.
    config: Config,

    /// The set of opcodes (by their index in `instructions`) that have been
    /// executed by the virtual machine on this thread.
    ///
    /// This ensures that no opcode is symbolically executed more than once per
    /// thread while also ensuring that we explore all potential code paths
    /// during execution. This is fine as executing a given code path more
    /// than once per thread provides no additional information as to the type
    /// of a value.
    visited_instructions: VisitedOpcodes,
}

impl VMState {
    /// Constructs a new virtual machine state originating at the provided
    /// `fork_point`, with all memory locations set to their default values.
    ///
    /// To create the initial VM state, use [`Self::new_at_start`].
    #[must_use]
    pub fn new(fork_point: u32, instructions_len: u32, config: Config) -> Self {
        let stack = Stack::new();
        let memory = Memory::new(config.single_memory_operation_size_limit);
        let storage = Storage::new();
        let recorded_values = Vec::default();
        let logged_values = Vec::default();
        let visited_instructions =
            VisitedOpcodes::new(instructions_len, config.maximum_iterations_per_opcode);

        Self {
            fork_point,
            stack,
            memory,
            storage,
            recorded_values,
            logged_values,
            config,
            visited_instructions,
        }
    }

    /// Creates a new virtual machine state originating at the start of
    /// execution, with all memory locations set to their default values.
    #[must_use]
    pub fn new_at_start(instructions_len: u32, config: Config) -> Self {
        Self::new(0, instructions_len, config)
    }

    /// Gets the stack associated with this virtual machine state.
    #[must_use]
    pub fn stack(&self) -> &Stack {
        &self.stack
    }

    /// Gets the stack associated with this virtual machine state.
    #[must_use]
    pub fn stack_mut(&mut self) -> &mut Stack {
        &mut self.stack
    }

    /// Gets the memory associated with this virtual machine state.
    #[must_use]
    pub fn memory(&self) -> &Memory {
        &self.memory
    }

    /// Gets the memory associated with this virtual machine state.
    #[must_use]
    pub fn memory_mut(&mut self) -> &mut Memory {
        &mut self.memory
    }

    /// Gets the storage associated with this virtual machine state.
    #[must_use]
    pub fn storage(&self) -> &Storage {
        &self.storage
    }

    /// Gets the storage associated with this virtual machine state.
    #[must_use]
    pub fn storage_mut(&mut self) -> &mut Storage {
        &mut self.storage
    }

    /// Gets the structure that tracks whether a given opcode has been visited
    /// by the current thread of execution.
    #[must_use]
    pub fn visited_instructions(&self) -> &VisitedOpcodes {
        &self.visited_instructions
    }

    /// Gets the structure that tracks whether a given opcode has been visited
    /// by the current thread of execution.
    #[must_use]
    pub fn visited_instructions_mut(&mut self) -> &mut VisitedOpcodes {
        &mut self.visited_instructions
    }

    /// Records the provided `value` so that it is available for later analysis
    /// even if it is no longer accounted for in one of the VM's working
    /// memories.
    pub fn record_value(&mut self, value: RuntimeBoxedVal) {
        self.recorded_values.push(value);
    }

    /// Gets the values that have been recorded to be available for analysis
    /// though not stored in the VM's working memories.
    #[must_use]
    pub fn recorded_values(&self) -> &[RuntimeBoxedVal] {
        self.recorded_values.as_slice()
    }

    /// Records the provided `value` so that it is available for later analysis
    /// even if it is no longer accounted for in one of the VM's working
    /// memories.
    pub fn log_value(&mut self, value: RuntimeBoxedVal) {
        self.logged_values.push(value);
    }

    /// Gets the values that have been recorded to be available for analysis
    /// though not stored in the VM's working memories.
    #[must_use]
    pub fn logged_values(&self) -> &[RuntimeBoxedVal] {
        self.logged_values.as_slice()
    }

    /// Gets the point in the instruction stream, specifically the value of the
    /// instruction pointer, at which this VM state was forked.
    #[must_use]
    pub fn fork_point(&self) -> u32 {
        self.fork_point
    }

    /// Forks the virtual machine state, returning a new state that at the point
    /// of the fork (given by `instruction_pointer`) is identical to the state
    /// it was forked from.
    ///
    /// This is used for exploring all branches of the bytecode.
    #[must_use]
    pub fn fork(&self, fork_point: u32) -> Self {
        let mut fork = self.clone();
        fork.fork_point = fork_point;

        fork
    }

    /// Consumes the state and produces all of the values that are registered in
    /// the virtual machine state.
    #[must_use]
    pub fn all_values(self) -> Vec<RuntimeBoxedVal> {
        let mut values = Vec::new();
        values.extend(self.stack.all_values());
        values.extend(self.memory.all_values());
        values.extend(self.storage.stores_as_values());
        values.extend(self.recorded_values);
        values.extend(self.logged_values);

        values
    }
}

#[cfg(test)]
mod test {
    use crate::vm::{
        state::VMState,
        value::{RSV, RSVD},
        Config,
    };

    #[test]
    fn can_construct_vm_state() {
        let state = VMState::new(10, 20, Config::default());
        assert_eq!(state.fork_point(), 10);
    }

    #[test]
    fn can_record_symbolic_value() {
        let mut state = VMState::new_at_start(20, Config::default());
        let value = RSV::new_synthetic(0, RSVD::new_value());
        state.record_value(value.clone());

        let values = state.recorded_values();
        assert_eq!(values.len(), 1);
        assert_eq!(values[0], value);
    }

    #[test]
    fn can_fork_state() -> anyhow::Result<()> {
        let value = RSV::new_synthetic(0, RSVD::new_value());
        let state = VMState::new_at_start(200, Config::default());
        let mut forked_state = state.fork(78);

        // The fork points should differ.
        assert_eq!(state.fork_point(), 0);
        assert_eq!(forked_state.fork_point(), 78);

        // We can modify one.
        forked_state.stack.push(value.clone())?;
        forked_state.memory.store(value.clone(), value.clone());
        forked_state.storage.store(value.clone(), value);
        assert_eq!(forked_state.stack.depth(), 1);
        assert_eq!(forked_state.memory.entry_count(), 1);
        assert_eq!(forked_state.storage.entry_count(), 1);

        // Without modifying the other.
        assert_eq!(state.stack.depth(), 0);
        assert_eq!(state.memory.entry_count(), 0);
        assert_eq!(state.storage.entry_count(), 0);

        Ok(())
    }
}
