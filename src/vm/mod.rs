//! This module contains the symbolic virtual machine.

pub mod data;
pub mod state;
pub mod thread;
pub mod value;

use std::collections::VecDeque;

use crate::{
    constant::{
        BLOCK_GAS_LIMIT,
        DEFAULT_CONDITIONAL_JUMP_PER_TARGET_FORK_LIMIT,
        DEFAULT_ITERATIONS_PER_OPCODE,
        DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES,
        DEFAULT_PERMISSIVE_ERRORS_ENABLED,
        DEFAULT_VALUE_SIZE_LIMIT,
    },
    disassembly::{ExecutionThread, InstructionStream},
    error::{
        self,
        container::Locatable,
        execution::{Error, Errors, LocatedError, Result},
    },
    opcode::DynOpcode,
    vm::{
        data::JumpTargets,
        state::{stack::LocatedStackHandle, VMState},
        thread::VMThread,
        value::{known::KnownWord, Provenance, RuntimeBoxedVal, RSV, RSVD},
    },
    watchdog::DynWatchdog,
};

/// The virtual machine used to perform symbolic execution of the contract
/// bytecode.
///
/// It is designed so as to be a 1:1 match for the semantics of a real runtime
/// EVM wherever such semantics can be represented symbolically.
#[derive(Clone, Debug)]
pub struct VM {
    /// The instructions that are being executed by this virtual machine.
    instructions: InstructionStream,

    /// Global tracking for jump target information, allowing global bounding of
    /// how many times each target is conditionally jumped to.
    jump_targets: JumpTargets,

    /// The queue of execution threads that will be taken when executing the
    /// provided `instructions`.
    thread_queue: VecDeque<VMThread>,

    /// The stored states that are no longer associated with a thread of
    /// execution.
    stored_states: Vec<VMState>,

    /// The configuration of the virtual machine.
    config: Config,

    /// Whether the currently executing thread needs to die.
    current_thread_killed: bool,

    /// Any errors that were encountered during the course of execution.
    errors: Errors,

    /// A builder for new values with configuration.
    builder: ValueBuilder,

    /// A watchdog that gets polled at intervals to check whether the analysis
    /// needs to exit.
    watchdog: DynWatchdog,
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
    ///
    /// # Panics
    ///
    /// Panics if the length of the instruction stream exceeds [`u32::MAX`].
    /// This is a programmer bug.
    pub fn new(
        instructions: InstructionStream,
        config: Config,
        watchdog: DynWatchdog,
    ) -> Result<Self> {
        // Create the initial thread internally as we can't use the function for this
        // while `self` doesn't exist.
        let instructions_len = instructions
            .len()
            .try_into()
            .unwrap_or_else(|_| panic!("Instruction length should not exceed {}", u32::MAX));
        let initial_state = VMState::new_at_start(instructions_len, config.clone());
        let initial_instruction_thread = instructions.new_thread(0)?;
        let initial_thread = VMThread::new(initial_state, initial_instruction_thread);
        let jump_targets = JumpTargets::new(
            instructions.new_thread(0)?,
            config.maximum_forks_per_fork_target,
        );

        // Set up the data for the VM.
        let mut thread_queue = VecDeque::new();
        thread_queue.push_back(initial_thread);
        let stored_states = Vec::new();
        let current_thread_killed = false;
        let errors = Errors::default();
        let builder = ValueBuilder::new(&config);

        Ok(Self {
            instructions,
            jump_targets,
            thread_queue,
            stored_states,
            config,
            current_thread_killed,
            errors,
            builder,
            watchdog,
        })
    }

    /// Performs symbolic execution of the entire bytecode.
    ///
    /// Running out of gas just stops execution of that thread, thereby allowing
    /// exploration of the full scope of what could potentially execute on
    /// chain.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if an internal error occurs, or at the end of execution
    /// if any thread failed to execute. Errors that are fatal are forwarded
    /// immediately, while errors that can allow execution to continue are
    /// buffered.
    ///
    /// Note that if this errors, it will still be possible to collect any
    /// stored state information for as far as execution proceeded.
    #[allow(clippy::missing_panics_doc)] // All panics are guarded by conditions
    pub fn execute(&mut self) -> std::result::Result<(), Errors> {
        let poll_interval = self.watchdog.poll_every();
        let mut counter = 0;

        while let Ok(instruction) = self.current_instruction() {
            let instruction_pointer = self
                .thread_queue
                .front_mut()
                .expect("We already know a thread is present")
                .instructions_mut()
                .instruction_pointer();

            // If we have been told to stop, stop and return an error.
            if counter % poll_interval == 0 && self.watchdog.should_stop() {
                Err(Error::StoppedByWatchdog).locate(instruction_pointer)?;
            }

            // We have to mark as being visited beforehand, so this is reflected in any
            // state bifurcations
            let current_thread = self.current_thread_mut()?;
            current_thread
                .state_mut()
                .visited_instructions_mut()
                .mark_visited(instruction_pointer)?;

            let result = instruction.execute(self);
            match result {
                Ok(_) => {
                    self.current_thread_mut()
                        .expect(
                            "We already know a thread is present as we executed an instruction \
                             from it",
                        )
                        .consume_gas(instruction.min_gas_cost());
                }
                Err(payload) => {
                    // If execution errored and we are not in permissive error mode, add the error
                    // to the collection of them and then kill the current
                    // thread to continue. If we are in permissive error mode we
                    // will only collect critical errors.
                    match payload.payload {
                        error::execution::Error::InvalidOffsetForJump { .. }
                        | error::execution::Error::InvalidJumpTarget { .. }
                        | error::execution::Error::NonExistentJumpTarget { .. }
                        | error::execution::Error::NoConcreteJumpDestination => {
                            if !self.config.permissive_errors {
                                self.errors.add(payload);
                            }
                        }
                        _ => {
                            self.errors.add(payload);
                        }
                    }
                    self.kill_current_thread();
                }
            }

            // This should never be called if there is nothing to advance to, so if it
            // errors we forward it immediately.
            self.advance()?;

            counter += 1;
        }

        // If we reach here, we have run out of things to execute.
        if self.errors.is_empty() {
            // If no errors have resulted, we can return happily.
            Ok(())
        } else {
            // Otherwise we return the descriptive errors.
            Err(self.errors.clone())
        }
    }

    /// Gets the instruction indicated by the current instruction pointer.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if there is no current thread.
    pub fn current_instruction(&self) -> Result<DynOpcode> {
        self.current_thread().map(|thread| thread.instructions().current())
    }

    /// Advances the virtual machine to the next instruction.
    ///
    /// This function handles correctly modifying the instruction pointer,
    /// tracking gas usage, and dealing with other limitations placed on
    /// execution.
    ///
    /// # Errors
    ///
    /// If the virtual machine cannot be advanced, or if advancing would result
    /// in the virtual machine pointing to an invalid instruction.
    #[allow(clippy::missing_panics_doc)] // All panics are guarded by impossible conditions
    pub fn advance(&mut self) -> Result<()> {
        if self.thread_queue.is_empty() {
            return Err(Error::InvalidStep.locate(self.instructions_len()));
        }

        let instruction_pointer = self
            .thread_queue
            .front_mut()
            .expect("We already know a thread is present")
            .instructions_mut()
            .instruction_pointer();
        let instructions_len = self.instructions_len();
        let current_thread = self.current_thread_mut()?;
        let next_offset = instruction_pointer + 1;

        // It is a programmer bug if a non-existent opcode is asked about here, so the
        // error is immediately forwarded.
        let oob_instruction = next_offset >= instructions_len;
        let exceeded_iteration_limit = oob_instruction
            || current_thread
                .state()
                .visited_instructions()
                .at_visit_limit(next_offset)?;

        let is_out_of_gas = self
            .thread_queue
            .front_mut()
            .expect("We already know a thread is present")
            .gas_usage()
            > self.config.gas_limit;
        let should_die = self.current_thread_killed;

        if exceeded_iteration_limit || is_out_of_gas || should_die {
            // In this case we are at the end of this thread, so we need to collect it and
            // move on by removing it from the queue. We already know that the queue isn't
            // empty, so it's safe to `unwrap`.
            let thread = self
                .thread_queue
                .pop_front()
                .expect("We already know a thread is present");
            self.stored_states.push(thread.into());

            // The thread no longer is the current, so whether is was or wasn't killed the
            // next one certainly isn't.
            self.current_thread_killed = false;

            // If we have run out of gas, mark it as an error.
            if is_out_of_gas {
                self.errors.add_located(instruction_pointer, Error::GasLimitExceeded);
            }
        } else {
            // And then continue execution on the current thread.
            self.current_thread_mut()
                .expect("We already know a thread is present")
                .instructions_mut()
                .step();
        }

        Ok(())
    }

    /// Gets a handle for the virtual machine stack of the current thread.
    ///
    /// # Getting the Actual Stack
    ///
    /// If you want to get the actual VM stack, rather than the wrapped  view
    /// onto it, call `.state()?.stack` instead.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if there is no current thread.
    pub fn stack_handle(&mut self) -> Result<LocatedStackHandle<'_>> {
        let instruction_pointer = self.instruction_pointer()?;
        self.current_thread_mut()
            .map(|thread| thread.state_mut().stack_mut().new_located(instruction_pointer))
    }

    /// Gets the virtual machine state for the thread that is currently being
    /// executed.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if there is no current thread.
    pub fn state(&mut self) -> Result<&mut VMState> {
        self.current_thread_mut().map(VMThread::state_mut)
    }

    /// Gets the execution thread for the thread that is currently being
    /// executed.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if there is no current thread.
    pub fn execution_thread(&self) -> Result<&ExecutionThread> {
        self.current_thread().map(VMThread::instructions)
    }

    /// Gets the execution thread for the thread that is currently being
    /// executed.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if there is no current thread.
    pub fn execution_thread_mut(&mut self) -> Result<&mut ExecutionThread> {
        self.current_thread_mut().map(VMThread::instructions_mut)
    }

    /// Gets the current tracking for jump target visits.
    #[must_use]
    pub fn jump_targets(&self) -> &JumpTargets {
        &self.jump_targets
    }

    /// Gets the current tracking for jump target visits.
    #[must_use]
    pub fn jump_targets_mut(&mut self) -> &mut JumpTargets {
        &mut self.jump_targets
    }

    /// Gets the current value of the instruction pointer for the thread that is
    /// being executed.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if there is no current thread.
    pub fn instruction_pointer(&mut self) -> Result<u32> {
        self.current_thread_mut()
            .map(|thread| thread.instructions_mut().instruction_pointer())
    }

    /// Gets the currently executing virtual machine thread.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if there is no current thread.
    pub fn current_thread(&self) -> Result<&VMThread> {
        self.thread_queue
            .front()
            .ok_or(Error::NoSuchThread.locate(self.instructions_len()))
    }

    /// Gets the currently executing virtual machine thread.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if there is no current thread.
    pub fn current_thread_mut(&mut self) -> Result<&mut VMThread> {
        let offset = self.instructions_len();
        self.thread_queue
            .front_mut()
            .ok_or(Error::NoSuchThread.locate(offset))
    }

    /// Adds a virtual machine thread to the queue of threads to be executed.
    pub fn enqueue_thread(&mut self, thread: VMThread) {
        self.thread_queue.push_back(thread);
    }

    /// Forks the currently executing thread to `jump_target`, maintaining the
    /// state at the moment of forking in the new thread.
    ///
    /// The new thread is then added to the thread queue to await execution.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the thread cannot be forked.
    pub fn fork_current_thread(&mut self, jump_target: u32) -> Result<()> {
        // It is a programmer error to ask for a thread to be forked when none exists,
        // so we forward the error immediately.
        let new_thread = self.current_thread_mut()?.fork(jump_target);
        self.enqueue_thread(new_thread);

        Ok(())
    }

    /// Checks if the current thread has been killed.
    #[must_use]
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
    #[must_use]
    pub fn remaining_thread_count(&self) -> usize {
        self.thread_queue.len()
    }

    /// Gets the queue of remaining threads for inspection.
    #[must_use]
    pub fn remaining_threads(&self) -> &VecDeque<VMThread> {
        &self.thread_queue
    }

    /// Gets the queue of remaining threads for inspection or modification.
    #[must_use]
    pub fn remaining_threads_mut(&mut self) -> &mut VecDeque<VMThread> {
        &mut self.thread_queue
    }

    /// Checks if the virtual machine has any more code to execute.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.remaining_thread_count() == 0
    }

    /// Gets the instruction stream associated with this virtual machine.a
    #[must_use]
    pub fn instructions(&self) -> &InstructionStream {
        &self.instructions
    }

    /// Gets the length of the instruction stream.
    ///
    /// # Panics
    ///
    /// Panics if the instructions length exceeds [`u32::MAX`] as this a
    /// programmer error.
    #[must_use]
    fn instructions_len(&self) -> u32 {
        self.instructions
            .len()
            .try_into()
            .unwrap_or_else(|_| panic!("Instruction length should not exceed {}", u32::MAX))
    }

    /// Gets the stored states that have resulted from execution in this virtual
    /// machine.
    #[must_use]
    pub fn stored_states(&self) -> &[VMState] {
        self.stored_states.as_slice()
    }

    /// Stores the provided error into the error buffer.
    pub fn store_error(&mut self, error: LocatedError) {
        self.errors.add(error);
    }

    /// Gets the value [`ValueBuilder`] associated with this VM instance.
    ///
    /// This is used for creating new values without having to manually pass
    /// configuration from the virtual machine to each call to the value
    /// constructor functions.
    #[must_use]
    pub fn build(&self) -> &ValueBuilder {
        &self.builder
    }

    /// Gets a reference to the virtual machine's watchdog instance, allowing it
    /// to be used for monitoring during loops in the opcode implementations.
    #[must_use]
    pub fn watchdog(&self) -> &DynWatchdog {
        &self.watchdog
    }

    /// Gets a reference to the virtual machine's watchdog instance, allowing it
    /// to be used for monitoring during loops in the opcode implementations.
    #[must_use]
    pub fn watchdog_mut(&mut self) -> &mut DynWatchdog {
        &mut self.watchdog
    }

    /// Gets a reference to the virtual machine's configuration.
    #[must_use]
    pub fn config(&self) -> &Config {
        &self.config
    }

    /// Consumes the virtual machine to convert it into the data necessary for
    /// the analysis in the [`crate::tc::TypeChecker`].
    #[must_use]
    pub fn consume(self) -> ExecutionResult {
        ExecutionResult {
            instructions: self.instructions,
            states:       self.stored_states,
            errors:       self.errors,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ExecutionResult {
    /// The instructions over which the execution result was gathered.
    pub instructions: InstructionStream,

    /// The states that resulted from total symbolic execution of
    /// `instructions`.
    pub states: Vec<VMState>,

    /// Any errors that arose during execution.
    ///
    /// Note that if `errors` is not empty, the execution result may not have
    /// full coverage of the bytecode. It is recommended to inspect the errors
    /// themselves before continuing to determine if the data is useful to use
    /// as the basis for continued analysis.
    pub errors: Errors,
}

impl ExecutionResult {
    /// Gathers all of the symbolic values known about by the execution result,
    /// consuming the execution result in the process.
    pub fn all_values(self) -> Vec<RuntimeBoxedVal> {
        self.states.into_iter().flat_map(VMState::all_values).collect()
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
    ///
    /// Defaults to [`BLOCK_GAS_LIMIT`].
    pub gas_limit: usize,

    /// The maximum number of times that the virtual machine will visit each
    /// opcode.
    ///
    /// This limit is enforced _per-thread_ in the virtual machine.
    ///
    /// Defaults to [`DEFAULT_ITERATIONS_PER_OPCODE`].
    pub maximum_iterations_per_opcode: usize,

    /// The maximum number of times that the virtual machine will fork from any
    /// conditional jump to a given jump target.
    ///
    /// This limit is enforced globally to prevent exponential blowup of threads
    /// when symbolically executing the bytecode.
    ///
    /// Defaults to [`DEFAULT_CONDITIONAL_JUMP_PER_TARGET_FORK_LIMIT`].
    pub maximum_forks_per_fork_target: usize,

    /// The maximum number of nodes that a symbolic value can contain before it
    /// is culled.
    ///
    /// Defaults to [`DEFAULT_VALUE_SIZE_LIMIT`].
    pub value_size_limit: usize,

    /// The maximum number of symbolic "bytes" that can be copied in a single
    /// memory operation.
    ///
    /// Defaults to [`DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES`].
    pub single_memory_operation_size_limit: usize,

    /// Whether to continue execution when non critical errors happen during
    /// execution.
    pub permissive_errors: bool,
}

impl Config {
    /// Sets the `maximum_forks_per_fork_target` config parameter to `value`.
    #[must_use]
    pub fn with_max_forks_per_fork_target(mut self, value: usize) -> Self {
        self.maximum_forks_per_fork_target = value;
        self
    }

    /// Sets the `maximum_iterations_per_opcode` config parameter to `value`.
    #[must_use]
    pub fn with_max_iterations_per_opcode(mut self, value: usize) -> Self {
        self.maximum_iterations_per_opcode = value;
        self
    }

    /// Sets the `gas_limit` config parameter to `value`.
    #[must_use]
    pub fn with_gas_limit(mut self, value: usize) -> Self {
        self.gas_limit = value;
        self
    }

    /// Sets the value size limit configuration parameter to `value`.
    #[must_use]
    pub fn with_value_size_limit(mut self, value: usize) -> Self {
        self.value_size_limit = value;
        self
    }

    /// Sets the memory max bytes configuration parameter to `value`.
    #[must_use]
    pub fn with_memory_max_bytes(mut self, value: usize) -> Self {
        self.single_memory_operation_size_limit = value;
        self
    }

    /// Sets the permissive errors configuration parameter to `value`.
    #[must_use]
    pub fn with_permissive_errors(mut self, value: bool) -> Self {
        self.permissive_errors = value;
        self
    }
}

impl Default for Config {
    fn default() -> Self {
        let gas_limit = BLOCK_GAS_LIMIT;
        let maximum_iterations_per_opcode = DEFAULT_ITERATIONS_PER_OPCODE;
        let maximum_forks_per_fork_target = DEFAULT_CONDITIONAL_JUMP_PER_TARGET_FORK_LIMIT;
        let value_size_limit = DEFAULT_VALUE_SIZE_LIMIT;
        let single_memory_operation_size_limit = DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES;
        let permissive_errors = DEFAULT_PERMISSIVE_ERRORS_ENABLED;
        Self {
            gas_limit,
            maximum_iterations_per_opcode,
            maximum_forks_per_fork_target,
            value_size_limit,
            single_memory_operation_size_limit,
            permissive_errors,
        }
    }
}

/// A structure that provides an interface to building new [`RSV`]s with access
/// to the VM's configuration.
///
/// It should be used for building all values that are constructed during the
/// course of execution as it ensures that size and structure invariants are
/// enforced for those values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValueBuilder {
    config: Config,
}

impl ValueBuilder {
    /// Constructs a new value builder with access to the specified `config`.
    #[must_use]
    pub fn new(config: &Config) -> Self {
        let config = config.clone();
        Self { config }
    }

    /// Constructs a new bare value at `instruction_pointer` with the specified
    /// `provenance`.
    ///
    /// This function exists to make it easier to construct values with the
    /// specified [`Config::value_size_limit`] without the need to pass it every
    /// time to the raw constructor.
    #[must_use]
    pub fn value(&self, instruction_pointer: u32, provenance: Provenance) -> RuntimeBoxedVal {
        RSV::new_value(instruction_pointer, provenance)
    }

    /// Constructs a new `SymbolicValue` representing the operation performed at
    /// `instruction_pointer` on the symbolic `data` and with the specified
    /// `provenance`.
    ///
    /// This function exists to make it easier to construct values with the
    /// specified [`Config::value_size_limit`] without the need to pass it every
    /// time to the raw constructor.
    #[must_use]
    pub fn symbolic(
        &self,
        instruction_pointer: u32,
        data: RSVD,
        provenance: Provenance,
    ) -> RuntimeBoxedVal {
        RSV::new(
            instruction_pointer,
            data,
            provenance,
            Some(self.config.value_size_limit),
        )
    }

    /// Constructs a new `SymbolicValue` representing the operation performed at
    /// `instruction_pointer` on the symbolic `data` and with its provenance
    /// being [`Provenance::Execution`].
    ///
    /// This function exists to make it easier to construct values with the
    /// specified [`Config::value_size_limit`] without the need to pass it every
    /// time to the raw constructor.
    #[must_use]
    pub fn symbolic_exec(&self, instruction_pointer: u32, data: RSVD) -> RuntimeBoxedVal {
        RSV::new_from_execution(
            instruction_pointer,
            data,
            Some(self.config.value_size_limit),
        )
    }

    /// Constructs a new `SymbolicValue` representing a known value of
    /// `value_data` created at `instruction_pointer` with the specified
    /// `provenance`.
    ///
    /// This function exists to make it easier to construct values with the
    /// specified [`Config::value_size_limit`] without the need to pass it every
    /// time to the raw constructor.
    #[must_use]
    pub fn known(
        &self,
        instruction_pointer: u32,
        value_data: KnownWord,
        provenance: Provenance,
    ) -> RuntimeBoxedVal {
        RSV::new_known_value(
            instruction_pointer,
            value_data,
            provenance,
            Some(self.config.value_size_limit),
        )
    }

    /// Constructs a new `SymbolicValue` representing a known value of
    /// `value_data` created at `instruction_pointer` with its provenance being
    /// [`Provenance::Execution`].
    ///
    /// This function exists to make it easier to construct values with the
    /// specified [`Config::value_size_limit`] without the need to pass it every
    /// time to the raw constructor.
    #[must_use]
    pub fn known_exec(&self, instruction_pointer: u32, value_data: KnownWord) -> RuntimeBoxedVal {
        RSV::new_known_value(
            instruction_pointer,
            value_data,
            Provenance::Execution,
            Some(self.config.value_size_limit),
        )
    }
}

#[cfg(test)]
mod test {
    use crate::{
        bytecode,
        disassembly::InstructionStream,
        error::execution::{Error, LocatedError},
        opcode::{
            control::{Invalid, JumpDest, JumpI, Return},
            logic::IsZero,
            memory::{CallDataSize, MStore, PushN, SStore},
        },
        vm::{Config, VM},
        watchdog::LazyWatchdog,
    };

    #[test]
    fn can_construct_new_vm() -> anyhow::Result<()> {
        let instructions = util::basic_instruction_stream();
        let vm = VM::new(instructions, Config::default(), LazyWatchdog.in_rc())?;

        // A newly-constructed virtual machine should have one thread of
        // execution to explore.
        assert_eq!(vm.remaining_thread_count(), 1);

        Ok(())
    }

    #[test]
    fn vm_executes_on_valid_bytecode() -> anyhow::Result<()> {
        // Create the instruction stream for this VM
        let bytes = bytecode![
            CallDataSize,               // Get a symbolic value
            IsZero,                     // Check if the size is zero
            PushN::new(1, vec![0x0b])?, // Push the jump destination offset onto the stack
            JumpI,                      // Jump if the condition is true
            PushN::new(1, vec![0x00])?, // Value to store
            PushN::new(1, vec![0x00])?, // Key under which to store it
            SStore,                     // Storage
            Invalid::default(),         // Return from this thread with invalid instruction
            JumpDest,                   // The destination for the jump
            PushN::new(1, vec![0xff])?, // The value to store into memory
            PushN::new(1, vec![0x00])?, // The offset in memory to store it at
            MStore,                     // Store to memory
            PushN::new(1, vec![0x01])?, // The size of the data to return
            PushN::new(1, vec![0x00])?, // The location in memory to return
            Return                      // Return from this thread
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the vm itself
        let config = Config::default();
        let mut vm = VM::new(instructions, config, LazyWatchdog.in_rc())?;

        // Execute the VM
        let result = vm.execute();
        assert!(result.is_ok());

        // Get the analysis data and see what happened
        let mut data = vm.consume();

        // We should have seen two threads due to the fork point
        assert_eq!(data.states.len(), 2);

        // In the first thread
        let thread_1 = &mut data.states[0];
        assert!(thread_1.memory_mut().is_empty());
        assert!(thread_1.stack_mut().is_empty());
        assert_eq!(thread_1.recorded_values().len(), 1);
        assert_eq!(thread_1.storage_mut().entry_count(), 1);

        // In the second thread
        let thread_2 = &mut data.states[1];
        assert_eq!(thread_2.memory_mut().entry_count(), 1);
        assert!(thread_2.stack_mut().is_empty());
        assert_eq!(thread_2.recorded_values().len(), 2);
        assert_eq!(thread_2.storage_mut().entry_count(), 0);

        Ok(())
    }

    #[test]
    fn vm_executes_in_the_presence_of_errors() -> anyhow::Result<()> {
        // Create the instruction stream for this VM
        let bytes = bytecode![
            CallDataSize,               // Get a symbolic value
            IsZero,                     // Check if the size is zero
            PushN::new(1, vec![0x0b])?, // Push the jump destination offset onto the stack
            JumpI,                      // Jump if the condition is true
            SStore,                     // Storage with invalid operands so the thread dies
            Invalid::default(),         // Return from this thread with invalid instruction
            JumpDest,                   // The destination for the jump
            PushN::new(1, vec![0xff])?, // The value to store into memory
            PushN::new(1, vec![0x00])?, // The offset in memory to store it at
            MStore,                     // Store to memory
            PushN::new(1, vec![0x01])?, // The size of the data to return
            PushN::new(1, vec![0x00])?, // The location in memory to return
            Return                      // Return from this thread
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the vm itself
        let config = Config::default();
        let mut vm = VM::new(instructions, config, LazyWatchdog.in_rc())?;

        // Execute the VM
        let result = vm.execute();
        assert!(result.is_err());

        // Get the analysis data and see what happened
        let mut data = vm.consume();

        // We should only see one thread due to the jump being invalid
        assert_eq!(data.states.len(), 1);

        // In the first thread
        let thread_1 = &mut data.states[0];
        assert!(thread_1.memory_mut().is_empty());
        assert!(thread_1.stack_mut().is_empty());
        assert_eq!(thread_1.recorded_values().len(), 2);

        // It should never have stored anything
        assert_eq!(thread_1.storage_mut().entry_count(), 0);

        // We should have multiple errors
        let error_container = result.unwrap_err();
        assert_eq!(error_container.len(), 2);
        assert_eq!(
            error_container.payloads()[0],
            LocatedError {
                location: 4,
                payload:  Error::InvalidJumpTarget { offset: 11 },
            }
        );
        assert_eq!(
            error_container.payloads()[1],
            LocatedError {
                location: 5,
                payload:  Error::NoSuchStackFrame { depth: 0 },
            }
        );

        Ok(())
    }

    /// Utilities for aiding in the testing of the virtual machine.
    mod util {
        use crate::disassembly::InstructionStream;

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
