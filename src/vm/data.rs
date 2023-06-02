//! This module contains miscellaneous small data-types that are used throughout
//! the virtual machine.

use std::collections::HashSet;

use crate::error::{container::Locatable, execution, execution::Error};

/// A container that tracks whether an opcode has been visited by the virtual
/// machine.
///
/// This ensures that we visit all opcodes _exactly once_.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VisitedOpcodes {
    instructions_len: u32,
    data:             HashSet<u32>,
}

impl VisitedOpcodes {
    /// Constructs a new visited opcodes container for up to `instructions_len`
    /// opcodes.
    pub fn new(instructions_len: u32) -> Self {
        let data = HashSet::default();

        Self {
            instructions_len,
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
            self.data.insert(instruction_pointer);
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
            self.data.remove(&instruction_pointer);
            Ok(())
        } else {
            Err(Error::InstructionPointerOutOfBounds {
                requested: instruction_pointer as usize,
                available: self.instructions_len as usize,
            }
            .locate(instruction_pointer))
        }
    }

    /// Checks if the opcode at `instruction_pointer` has been visited.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the provided `instruction_pointer` is out of bounds
    /// in the instruction stream.
    pub fn visited(&mut self, instruction_pointer: u32) -> execution::Result<bool> {
        if instruction_pointer < self.instructions_len {
            Ok(self.data.contains(&instruction_pointer))
        } else {
            Err(Error::InstructionPointerOutOfBounds {
                requested: instruction_pointer as usize,
                available: self.instructions_len as usize,
            }
            .locate(instruction_pointer))
        }
    }
}

#[cfg(test)]
mod test {
    mod visited_opcodes {
        use crate::{error::execution, vm::data::VisitedOpcodes};

        #[test]
        fn can_mark_instructions_as_visited() -> anyhow::Result<()> {
            let mut tracker = VisitedOpcodes::new(20);
            tracker.mark_visited(17)?;

            assert!(tracker.visited(17).unwrap());

            Ok(())
        }

        #[test]
        fn can_unmark_instructions_as_visited() -> anyhow::Result<()> {
            let mut tracker = VisitedOpcodes::new(20);
            tracker.mark_visited(17)?;
            tracker.unmark_visited(17)?;

            assert!(!tracker.visited(17).unwrap());

            Ok(())
        }

        #[test]
        fn cannot_mark_invalid_instructions_as_visited() -> anyhow::Result<()> {
            let mut tracker = VisitedOpcodes::new(20);
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

            Ok(())
        }

        #[test]
        fn cannot_unmark_invalid_instructions_as_visited() -> anyhow::Result<()> {
            let mut tracker = VisitedOpcodes::new(20);
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

            Ok(())
        }
    }
}
