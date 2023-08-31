//! This module contains the definition of the [`VMThread`] type, representing
//! the divergent execution paths that can be taken during symbolic execution.

use crate::{disassembly::ExecutionThread, vm::state::VMState};

/// A `VMThread` is a representation of a given execution path during the course
/// of symbolic execution.
///
/// The construct can be forked at will to represent the branches in execution,
/// but contains no logic for performing that execution itself.
#[derive(Clone, Debug)]
pub struct VMThread {
    /// The virtual machine's state for this thread of execution.
    state: VMState,

    /// The instruction stream and instruction pointer.
    thread: ExecutionThread,

    /// The amount of gas used in executing this thread.
    gas_usage: usize,
}

impl VMThread {
    /// Constructs a new virtual machine thread with `state` as the initial
    /// state at `thread.instruction_pointer()`.
    #[must_use]
    pub fn new(state: VMState, thread: ExecutionThread) -> Self {
        let gas_usage = 0;
        Self {
            state,
            thread,
            gas_usage,
        }
    }

    /// Gets the current virtual machine state for this virtual machine thread.
    #[must_use]
    pub fn state(&self) -> &VMState {
        &self.state
    }

    /// Gets the current virtual machine state for this virtual machine thread.
    #[must_use]
    pub fn state_mut(&mut self) -> &mut VMState {
        &mut self.state
    }

    /// Gets the instruction stream and current execution position associated
    /// with this virtual machine thread.
    #[must_use]
    pub fn instructions(&self) -> &ExecutionThread {
        &self.thread
    }

    /// Gets the instruction stream and current execution position associated
    /// with this virtual machine thread.
    #[must_use]
    pub fn instructions_mut(&mut self) -> &mut ExecutionThread {
        &mut self.thread
    }

    /// Forks the virtual machine thread at the current point of execution,
    /// jumping the new thread to `target` and leaving the current thread at the
    /// current point of execution.
    ///
    /// This method performs no validation as to whether the fork point is a
    /// valid fork point. This is up to the VM itself.
    #[must_use]
    pub fn fork(&self, target: u32) -> Self {
        let instruction_pointer = self.thread.instruction_pointer();
        let state = self.state.fork(instruction_pointer);
        let gas_usage = self.gas_usage;
        let mut thread = self.thread.clone();
        thread.at(target);

        Self {
            state,
            thread,
            gas_usage,
        }
    }

    /// Adds the provided `gas` to the gas usage of this thread.
    pub fn consume_gas(&mut self, gas: usize) {
        self.gas_usage += gas;
    }

    /// Gets the gas usage of this thread.
    #[must_use]
    pub fn gas_usage(&self) -> usize {
        self.gas_usage
    }
}

impl From<VMThread> for VMState {
    fn from(value: VMThread) -> Self {
        value.state
    }
}

#[cfg(test)]
mod test {
    use crate::{
        disassembly::InstructionStream,
        vm::{state::VMState, thread::VMThread, Config},
    };

    #[test]
    fn can_fork_vm_thread() -> anyhow::Result<()> {
        let instruction_stream = InstructionStream::try_from(
            vec![0x00u8, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06].as_slice(),
        )?;
        let state = VMState::new_at_start(
            u32::try_from(instruction_stream.len()).unwrap(),
            Config::default(),
        );
        let execution_thread = instruction_stream.new_thread(0)?;
        let mut vm_thread = VMThread::new(state, execution_thread);

        // Step the execution to a different point.
        vm_thread.thread.step().expect("Execution was not able to step");

        // Now we can fork with a different jump target.
        let mut forked_thread = vm_thread.fork(4);

        // These move independently.
        let forked_position_start = forked_thread.thread.instruction_pointer();
        assert_ne!(
            forked_position_start,
            vm_thread.thread.instruction_pointer()
        );
        forked_thread.thread.step().expect("Execution was not able to step");
        assert_ne!(
            forked_position_start,
            forked_thread.thread.instruction_pointer()
        );
        assert_eq!(forked_thread.thread.current().as_byte(), 0x05);

        Ok(())
    }
}
