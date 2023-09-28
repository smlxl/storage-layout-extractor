//! This module contains miscellaneous small data-types that are used throughout
//! the virtual machine.

use std::collections::HashMap;

use crate::{
    disassembly::ExecutionThread,
    error::{container::Locatable, execution, execution::Error},
    opcode::control::{JumpDest, JumpI},
};

/// A container that tracks how many times an opcode has been visited by the
/// virtual machine.
///
/// This ensures that we visit all opcodes no more than `iterations_per_opcode`
/// number of times during a given thread of execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VisitedOpcodes {
    instructions_len: u32,
    maximum_iterations_per_opcode: usize,
    data: HashMap<u32, usize>,
}

impl VisitedOpcodes {
    /// Constructs a new visited opcodes container for up to `instructions_len`
    /// opcodes.
    #[must_use]
    pub fn new(instructions_len: u32, maximum_iterations_per_opcode: usize) -> Self {
        let data = HashMap::default();

        Self {
            instructions_len,
            maximum_iterations_per_opcode,
            data,
        }
    }

    /// Marks the instruction at `instruction_pointer` as having been visited.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the provided `instruction_pointer` is out of bounds
    /// in the instruction stream.
    pub fn mark_visited(&mut self, instruction_pointer: u32) -> execution::Result<()> {
        if instruction_pointer < self.instructions_len {
            self.data
                .entry(instruction_pointer)
                .and_modify(|count| *count = count.saturating_add(1))
                .or_insert(1);
            Ok(())
        } else {
            Err(Error::InstructionPointerOutOfBounds {
                requested: instruction_pointer as usize,
                available: self.instructions_len as usize,
            }
            .locate(instruction_pointer))
        }
    }

    /// Un-marks the instruction at `instruction_pointer` as having been
    /// visited.
    ///
    /// This is useful for branches of execution where you discover something
    /// that invalidates all analysis done for that branch and hence opcodes
    /// need to be able to be visited again on other branches.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the provided `instruction_pointer` is out of bounds
    /// in the instruction stream.
    pub fn unmark_visited(&mut self, instruction_pointer: u32) -> execution::Result<()> {
        if instruction_pointer < self.instructions_len {
            self.data
                .entry(instruction_pointer)
                .and_modify(|count| *count = count.saturating_sub(1))
                .or_insert(0);
            Ok(())
        } else {
            Err(Error::InstructionPointerOutOfBounds {
                requested: instruction_pointer as usize,
                available: self.instructions_len as usize,
            }
            .locate(instruction_pointer))
        }
    }

    /// Gets the number of times that the instruction at `instruction_pointer`
    /// has been visited.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the provided `instruction_pointer` is out of bounds
    /// in the instruction stream.
    pub fn visit_count(&self, instruction_pointer: u32) -> execution::Result<usize> {
        if instruction_pointer < self.instructions_len {
            Ok(*self.data.get(&instruction_pointer).unwrap_or(&0))
        } else {
            Err(Error::InstructionPointerOutOfBounds {
                requested: instruction_pointer as usize,
                available: self.instructions_len as usize,
            }
            .locate(instruction_pointer))
        }
    }

    /// Checks if the opcode at `instruction_pointer` has reached the maximum
    /// number of times that it can be visited.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the provided `instruction_pointer` is out of bounds
    /// in the instruction stream.
    pub fn at_visit_limit(&self, instruction_pointer: u32) -> execution::Result<bool> {
        if instruction_pointer < self.instructions_len {
            Ok(self.data.get(&instruction_pointer).unwrap_or(&0)
                >= &self.maximum_iterations_per_opcode)
        } else {
            Err(Error::InstructionPointerOutOfBounds {
                requested: instruction_pointer as usize,
                available: self.instructions_len as usize,
            }
            .locate(instruction_pointer))
        }
    }
}

/// A container that tracks how many times a given jump target has been visited
/// by the virtual machine from conditional jumps.
///
/// This ensures that we fork at a given jump target no more than a number of
/// times given by some limit.
#[derive(Clone, Debug)]
pub struct JumpTargets {
    /// The instructions over which the virtual machine is executing.
    instructions: ExecutionThread,

    /// Tracking for how many times a given opcode has been visited.
    ///
    /// This is used to implement tracking specific to jump targets and via
    /// conditional jumps.
    tracker: VisitedOpcodes,
}

impl JumpTargets {
    /// Creates a new tracker for jump targets.
    #[allow(clippy::missing_panics_doc)] // Instructions len has already been checked
    #[must_use]
    pub fn new(instructions: ExecutionThread, maximum_forks_per_jump_target: usize) -> Self {
        let instructions_len = instructions.len();
        let tracker = VisitedOpcodes::new(
            u32::try_from(instructions_len).expect("Invalid instruction length provided"),
            maximum_forks_per_jump_target,
        );
        Self {
            instructions,
            tracker,
        }
    }

    /// Requests that the VM fork from the conditional jump at
    /// `current_instruction` to the jump target at `target_instruction`.
    ///
    /// If the fork is successful, the count for that target is incremented and
    /// `true` is returned. Otherwise, `false` is returned.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `current_instruction` is not [`JumpI`] or if
    /// `target_instruction` is not [`JumpDest`].
    pub fn fork_to(
        &mut self,
        current_instruction: u32,
        target_instruction: u32,
    ) -> execution::Result<bool> {
        let concrete_current_inst = self.instructions.instruction(current_instruction).ok_or(
            Error::InstructionPointerOutOfBounds {
                requested: target_instruction as usize,
                available: self.instructions.len(),
            }
            .locate(current_instruction),
        )?;
        let concrete_target_inst = self.instructions.instruction(target_instruction).ok_or(
            Error::InstructionPointerOutOfBounds {
                requested: target_instruction as usize,
                available: self.instructions.len(),
            }
            .locate(current_instruction),
        )?;

        // The source instruction needs to be a conditional jump.
        if concrete_current_inst
            .as_ref()
            .as_any()
            .downcast_ref::<JumpI>()
            .is_none()
        {
            Err(Error::NotJumpSource {
                pointer: current_instruction,
            }
            .locate(current_instruction))?;
        }

        // And the destination needs to be a jump target.
        if concrete_target_inst
            .as_ref()
            .as_any()
            .downcast_ref::<JumpDest>()
            .is_none()
        {
            Err(Error::NotJumpTarget {
                pointer: target_instruction,
            }
            .locate(current_instruction))?;
        }

        // With that out of the way we can jump
        if self.tracker.at_visit_limit(target_instruction)? {
            Ok(false)
        } else {
            self.tracker.mark_visited(target_instruction)?;
            Ok(true)
        }
    }

    /// Gets the number of times that the virtual machine has conditionally
    /// jumped to the jump target at `instruction_pointer`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if `instruction_pointer` is not in the bounds of the
    /// instruction stream, or if it points to a non [`JumpDest`] instruction.
    pub fn cond_jump_count(&self, instruction_pointer: u32) -> execution::Result<usize> {
        let concrete_target_inst = self.instructions.instruction(instruction_pointer).ok_or(
            Error::InstructionPointerOutOfBounds {
                requested: instruction_pointer as usize,
                available: self.instructions.len(),
            }
            .locate(instruction_pointer),
        )?;

        // The destination needs to be a jump target.
        if concrete_target_inst
            .as_ref()
            .as_any()
            .downcast_ref::<JumpDest>()
            .is_none()
        {
            Err(Error::NotJumpTarget {
                pointer: instruction_pointer,
            }
            .locate(instruction_pointer))?;
        }

        self.tracker.visit_count(instruction_pointer)
    }
}

#[cfg(test)]
mod test {
    mod visited_opcodes {
        use crate::{error::execution, vm::data::VisitedOpcodes};

        #[test]
        fn can_mark_instructions_as_visited() -> anyhow::Result<()> {
            let mut tracker = VisitedOpcodes::new(20, 1);
            tracker.mark_visited(17)?;

            assert!(tracker.at_visit_limit(17).unwrap());

            Ok(())
        }

        #[test]
        fn can_visit_instructions_multiple_times() -> anyhow::Result<()> {
            let mut tracker = VisitedOpcodes::new(20, 3);
            for _ in 0..3 {
                tracker.mark_visited(17)?;
            }

            assert!(tracker.at_visit_limit(17).unwrap());

            Ok(())
        }

        #[test]
        fn can_unmark_instructions_as_visited() -> anyhow::Result<()> {
            let mut tracker = VisitedOpcodes::new(20, 1);
            tracker.mark_visited(17)?;
            tracker.unmark_visited(17)?;

            assert!(!tracker.at_visit_limit(17).unwrap());

            Ok(())
        }

        #[test]
        fn cannot_mark_invalid_instructions_as_visited() {
            let mut tracker = VisitedOpcodes::new(20, 1);
            let mark = tracker
                .mark_visited(1000)
                .expect_err("Impossible instruction was marked as visited.");

            assert_eq!(
                mark.payload,
                execution::Error::InstructionPointerOutOfBounds {
                    requested: 1000,
                    available: 20,
                }
            );
        }

        #[test]
        fn cannot_unmark_invalid_instructions_as_visited() {
            let mut tracker = VisitedOpcodes::new(20, 1);
            let mark = tracker
                .unmark_visited(1000)
                .expect_err("Impossible instruction was marked as visited.");

            assert_eq!(
                mark.payload,
                execution::Error::InstructionPointerOutOfBounds {
                    requested: 1000,
                    available: 20,
                }
            );
        }
    }

    mod jump_targets {
        use crate::{
            bytecode,
            disassembly::InstructionStream,
            error::{container::Locatable, execution::Error},
            opcode::{
                control::{JumpDest, JumpI},
                memory::Push0,
            },
            vm::data::JumpTargets,
        };

        #[test]
        fn can_track_visits_to_jump_targets() -> anyhow::Result<()> {
            // Create some opcodes
            let opcodes = bytecode![JumpI, JumpDest];
            let instructions = InstructionStream::try_from(opcodes.as_slice())?;
            let thread = instructions.new_thread(0)?;

            // Create the container
            let mut targets = JumpTargets::new(thread, 2);

            let result = targets.fork_to(0, 1)?;
            assert!(result);

            Ok(())
        }

        #[test]
        fn errors_if_source_is_not_conditional_jump() -> anyhow::Result<()> {
            // Create some opcodes
            let opcodes = bytecode![Push0, JumpDest];
            let instructions = InstructionStream::try_from(opcodes.as_slice())?;
            let thread = instructions.new_thread(0)?;

            // Create the container
            let mut targets = JumpTargets::new(thread, 2);

            let result = targets.fork_to(0, 1);
            assert_eq!(result, Err(Error::NotJumpSource { pointer: 0 }.locate(0)));

            Ok(())
        }

        #[test]
        fn errors_if_target_is_not_jump_dest() -> anyhow::Result<()> {
            // Create some opcodes
            let opcodes = bytecode![JumpI, Push0];
            let instructions = InstructionStream::try_from(opcodes.as_slice())?;
            let thread = instructions.new_thread(0)?;

            // Create the container
            let mut targets = JumpTargets::new(thread, 2);

            let result = targets.fork_to(0, 1);
            assert_eq!(result, Err(Error::NotJumpTarget { pointer: 1 }.locate(0)));

            Ok(())
        }

        #[test]
        fn returns_false_if_at_limit() -> anyhow::Result<()> {
            // Create some opcodes
            let opcodes = bytecode![JumpI, JumpDest];
            let instructions = InstructionStream::try_from(opcodes.as_slice())?;
            let thread = instructions.new_thread(0)?;

            // Create the container
            let mut targets = JumpTargets::new(thread, 1);

            let result = targets.fork_to(0, 1)?;
            assert!(result);

            let result = targets.fork_to(0, 1)?;
            assert!(!result);

            Ok(())
        }

        #[test]
        fn can_check_limit() -> anyhow::Result<()> {
            // Create some opcodes
            let opcodes = bytecode![JumpI, JumpDest];
            let instructions = InstructionStream::try_from(opcodes.as_slice())?;
            let thread = instructions.new_thread(0)?;

            // Create the container
            let mut targets = JumpTargets::new(thread, 1);
            targets.fork_to(0, 1)?;

            let result = targets.cond_jump_count(1)?;
            assert_eq!(result, 1);

            Ok(())
        }
    }
}
