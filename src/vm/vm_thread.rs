//! This module contains the definition of the [`VMThread`] type, representing
//! the divergent execution paths that can be taken during symbolic execution.

use crate::vm::{instruction_stream::ExecutionThread, state::VMState};

/// A `VMThread` is a representation of a given execution path during the course
/// of symbolic execution.
///
/// The construct can be forked at will to represent the branches in execution,
/// but contains no logic for performing that execution itself.
pub struct VMThread<'et> {
    /// The virtual machine's state for this thread of execution.
    state: VMState,

    /// The instruction stream and instruction pointer.
    thread: ExecutionThread<'et>,
}

impl<'et> VMThread<'et> {
    /// Constructs a new virtual machine thread with `state` as the initial
    /// state at `thread.instruction_pointer()`.
    pub fn new(state: VMState, thread: ExecutionThread<'et>) -> Self {
        Self { state, thread }
    }

    /// Gets the current virtual machine state for this virtual machine thread.
    pub fn state(&mut self) -> &mut VMState {
        &mut self.state
    }

    /// Gets the instruction stream and current execution position associated
    /// with this virtual machine thread.
    pub fn instructions(&mut self) -> &mut ExecutionThread<'et> {
        &mut self.thread
    }

    /// Forks the virtual machine thread at the current point of execution,
    /// jumping the new thread to `target`.
    ///
    /// This method performs no validation as to whether the fork point is a
    /// valid fork point. This is up to the VM itself.
    pub fn fork(&self, target: u32) -> Self {
        let instruction_pointer = self.thread.instruction_pointer();
        let state = self.state.fork(instruction_pointer);
        let mut thread = self.thread;
        thread.at(target);

        Self { state, thread }
    }
}

#[cfg(test)]
mod test {
    use crate::vm::{instruction_stream::InstructionStream, state::VMState, vm_thread::VMThread};

    #[test]
    fn can_fork_vm_thread() -> anyhow::Result<()> {
        let instruction_stream = InstructionStream::try_from(
            vec![0x00u8, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06].as_slice(),
        )?;
        let state = VMState::default();
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
