//! This module contains miscellaneous small data-types that are used throughout
//! the virtual machine.

use std::collections::HashMap;

use crate::error::{container::Locatable, execution, execution::Error};

/// A container that tracks whether an opcode has been visited by the virtual
/// machine.
///
/// This ensures that we visit all opcodes exactly `iterations_per_opcode`
/// number of times.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VisitedOpcodes {
    instructions_len:      u32,
    iterations_per_opcode: usize,
    data:                  HashMap<u32, usize>,
}

impl VisitedOpcodes {
    /// Constructs a new visited opcodes container for up to `instructions_len`
    /// opcodes.
    #[must_use]
    pub fn new(instructions_len: u32, iterations_per_opcode: usize) -> Self {
        let data = HashMap::default();

        Self {
            instructions_len,
            iterations_per_opcode,
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

    /// Checks if the opcode at `instruction_pointer` has been visited.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the provided `instruction_pointer` is out of bounds
    /// in the instruction stream.
    pub fn at_visit_limit(&self, instruction_pointer: u32) -> execution::Result<bool> {
        if instruction_pointer < self.instructions_len {
            Ok(self.data.get(&instruction_pointer).unwrap_or(&0) >= &self.iterations_per_opcode)
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
}
