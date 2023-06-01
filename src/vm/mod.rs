//! This module deals with the implementation of the symbolic virtual machine.

pub mod data;
pub mod instructions;
pub mod state;
pub mod thread;
pub mod value;

use std::collections::VecDeque;

use crate::{
    constant::BLOCK_GAS_LIMIT,
    error::VMError,
    opcode::DynOpcode,
    vm::{
        data::VisitedOpcodes,
        instructions::{ExecutionThread, InstructionStream},
        state::{stack::Stack, VMState},
        thread::VMThread,
    },
};

// TODO [Ara] Precomputed keccaks for the early storage slots to help with
//   recognition of constants. With arrays.

/// The virtual machine used to perform symbolic execution of the contract
/// bytecode.
#[derive(Debug)]
pub struct VM {
    /// The instructions that are being executed by this virtual machine.
    instructions: InstructionStream,

    /// The queue of execution threads that will be taken when executing the
    /// provided `instructions`.
    thread_queue: VecDeque<VMThread>,

    /// The set of opcodes (by their index in `instructions`) that have been
    /// executed by the virtual machine.
    ///
    /// This ensures that no opcode is symbolically executed more than once
    /// while also ensuring that we explore all potential code paths during
    /// execution. This is fine as executing a given code path more than once
    /// provides no additional information as to the type of a value.
    visited_opcodes: VisitedOpcodes,

    /// The stored states that are no longer associated with a thread of
    /// execution.
    stored_states: Vec<VMState>,

    /// The configuration of the virtual machine.
    config: Config,

    /// Whether the currently executing thread needs to die.
    current_thread_killed: bool,
}

impl VM {
    /// Constructs a new virtual machine that executes over the provided
    /// `instructions`.
    ///
    /// It is created with an initial thread of execution that begins at the
    /// first instruction.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the virtual machine could not be constructed.
    pub fn new(instructions: InstructionStream, config: Config) -> anyhow::Result<Self> {
        // Create the initial thread internally as we can't use the function for this
        // while `self` doesn't exist.
        let initial_instruction_thread = instructions.new_thread(0)?;
        let initial_state = VMState::new(0);
        let initial_thread = VMThread::new(initial_state, initial_instruction_thread);

        // Set up the data for the VM.
        let mut thread_queue = VecDeque::new();
        thread_queue.push_back(initial_thread);
        let visited_opcodes = VisitedOpcodes::new(instructions.len() as u32);
        let stored_states = Vec::new();
        let current_thread_killed = false;

        Ok(Self {
            instructions,
            thread_queue,
            visited_opcodes,
            stored_states,
            config,
            current_thread_killed,
        })
    }

    /// Performs symbolic execution of the entire bytecode.
    ///
    /// It explores all branches of the code exactly once, thereby collecting
    /// the maximum information about the code and the types within it.
    ///
    /// Running out of gas just stops execution of that thread, thereby allowing
    /// exploration of the full scope of what could potentially execute on
    /// chain.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if execution fails, or if there is no thread to execute.
    pub fn execute(&mut self) -> anyhow::Result<()> {
        while let Ok(instruction) = self.current_instruction() {
            instruction.execute(self)?;
            self.thread_queue
                .front_mut()
                .unwrap()
                .consume_gas(instruction.min_gas_cost());
            self.advance()?
        }

        Ok(())
    }

    /// Gets the instruction indicated by the current instruction pointer.
    pub fn current_instruction(&mut self) -> anyhow::Result<DynOpcode> {
        self.current_thread().map(|thread| thread.instructions().current())
    }

    /// Advances the virtual machine to the next instruction.
    ///
    /// # Errors
    ///
    /// If the virtual machine cannot be advanced, or if advancing would result
    /// in the virtual machine pointing to an invalid instruction.
    pub fn advance(&mut self) -> anyhow::Result<()> {
        if self.thread_queue.is_empty() {
            return Err(VMError::InvalidStep.into());
        }

        let i_ptr = self
            .thread_queue
            .front_mut()
            .unwrap()
            .instructions()
            .instruction_pointer();
        let instructions_len = self.thread_queue.front_mut().unwrap().instructions().len() as u32;
        let is_visited = self.visited_opcodes.visited(i_ptr)?;
        let gas_usage = self.thread_queue.front_mut().unwrap().gas_usage();
        let is_out_of_gas = gas_usage > self.config.gas_limit;
        let should_die = self.current_thread_killed;

        if i_ptr + 1 >= instructions_len || is_visited || is_out_of_gas || should_die {
            // In this case we are at the end of this thread, so we need to collect it and
            // move on by removing it from the queue.
            let thread = self.thread_queue.pop_front().unwrap();
            self.stored_states.push(thread.into_state());
            self.current_thread_killed = false;
        } else {
            // Here we need to mark the current opcode as visited.
            self.visited_opcodes.mark_visited(i_ptr)?;

            // And then continue execution on the current thread.
            self.current_thread().unwrap().instructions().step();
        }

        Ok(())
    }

    /// Gets the virtual machine stack for the thread that is currently being
    /// executed.
    pub fn stack(&mut self) -> anyhow::Result<&mut Stack> {
        self.current_thread().map(|thread| thread.state().stack())
    }

    /// Gets the virtual machine state that is currently being executed.
    pub fn state(&mut self) -> anyhow::Result<&mut VMState> {
        self.current_thread().map(|thread| thread.state())
    }

    /// Gets the current execution thread (instruction sequence) that is being
    /// executed.
    pub fn execution_thread(&mut self) -> anyhow::Result<&mut ExecutionThread> {
        self.current_thread().map(|thread| thread.instructions())
    }

    /// Gets the current value of the instruction pointer for the thread that is
    /// being executed.
    pub fn instruction_pointer(&mut self) -> anyhow::Result<u32> {
        self.current_thread()
            .map(|thread| thread.instructions().instruction_pointer())
    }

    /// Gets the currently executing virtual machine thread if there is one, or
    /// [`None`] if there is no such thread.
    pub fn current_thread(&mut self) -> anyhow::Result<&mut VMThread> {
        self.thread_queue.front_mut().ok_or(VMError::NoSuchThread.into())
    }

    /// Adds a virtual machine thread to the queue for execution.
    pub fn enqueue_thread(&mut self, thread: VMThread) {
        self.thread_queue.push_back(thread);
    }

    /// Forks the currently executing thread to `jump_target`, maintaining the
    /// state at the moment of forking.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the thread cannot be forked.
    pub fn fork_current_thread(&mut self, jump_target: u32) -> anyhow::Result<()> {
        let new_thread = self.current_thread()?.fork(jump_target);
        self.enqueue_thread(new_thread);

        Ok(())
    }

    /// Checks if the current thread has been killed.
    pub fn current_thread_killed(&self) -> bool {
        self.current_thread_killed
    }

    /// Says that the current thread has encountered an instruction that forces
    /// it to cease execution.
    pub fn kill_current_thread(&mut self) {
        self.current_thread_killed = true;
    }

    /// Gets the count of remaining threads of execution for this virtual
    /// machine.
    pub fn remaining_thread_count(&self) -> usize {
        self.thread_queue.len()
    }

    /// Gets the queue of remaining threads for inspection.
    pub fn remaining_threads(&mut self) -> &mut VecDeque<VMThread> {
        &mut self.thread_queue
    }

    /// Checks if the virtual machine has any more code to execute.
    pub fn is_complete(&self) -> bool {
        self.remaining_thread_count() == 0
    }

    /// Gets the instruction stream associated with this virtual machine.
    pub fn instructions(&self) -> &InstructionStream {
        &self.instructions
    }

    /// Gets the stored states that have resulted from execution in this virtual
    /// machine.
    pub fn stored_states(&self) -> &[VMState] {
        self.stored_states.as_slice()
    }

    /// Consumes the virtual machine to convert it into the data necessary for
    /// the analysis in the [`crate::unifier::Unifier`].
    pub fn consume(self) -> (InstructionStream, Vec<VMState>) {
        (self.instructions, self.stored_states)
    }
}

/// The configuration for the virtual machine instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Config {
    /// The maximum amount of gas that the virtual machine can consume.
    ///
    /// Note that this limit is applied optimistically, assuming that every
    /// operation takes the minimal amount of gas it can. In reality, execution
    /// on an EVM will not get as far as symbolic execution can here.
    gas_limit: usize,
}

impl Default for Config {
    fn default() -> Self {
        let gas_limit = BLOCK_GAS_LIMIT;
        Self { gas_limit }
    }
}

#[cfg(test)]
mod test {
    use crate::vm::{Config, VM};

    #[test]
    fn can_construct_new_vm() -> anyhow::Result<()> {
        let instructions = util::basic_instruction_stream();
        let vm = VM::new(instructions, Config::default())?;

        // A newly-constructed virtual machine should have one thread of
        // execution to explore.
        assert_eq!(vm.remaining_thread_count(), 1);

        Ok(())
    }

    /// Utilities for aiding in the testing of the virtual machine.
    mod util {
        use crate::vm::instructions::InstructionStream;

        /// Constructs a basic instruction stream for testing purposes.
        pub fn basic_instruction_stream() -> InstructionStream {
            let bytes: Vec<u8> = vec![
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x10, 0x11,
                0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x20, 0x30,
                0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e,
            ];

            InstructionStream::try_from(bytes.as_slice()).unwrap()
        }
    }
}
