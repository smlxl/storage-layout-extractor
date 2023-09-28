//! This module contains errors pertaining to the symbolic execution of the
//! bytecode.

use thiserror::Error;

use crate::{error::container, vm::value::known::KnownWord};

/// Errors that occur during the execution of the bytecode by the
/// [`crate::vm::VM`].
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum Error {
    #[error(
        "Instruction pointer {requested:?} is out of bounds in bytecode of length {available:?}"
    )]
    InstructionPointerOutOfBounds { requested: usize, available: usize },

    #[error("Maximum stack depth exceeded with request for {requested:?} frames")]
    StackDepthExceeded { requested: usize },

    #[error("A stack frame at depth {depth:?} was requested but none was available")]
    NoSuchStackFrame { depth: i64 },

    #[error("A VM thread was requested but none are available")]
    NoSuchThread,

    #[error("Tried to step the virtual machine when no target instruction exists")]
    InvalidStep,

    #[error("{data:?} cannot be used as an immediate for a jump")]
    InvalidOffsetForJump { data: KnownWord },

    #[error("The opcode at {offset:?} is not a valid jump destination")]
    InvalidJumpTarget { offset: u32 },

    #[error("No opcode exists at {offset:?}")]
    NonExistentJumpTarget { offset: u32 },

    #[error("No concrete immediate was found for the jump destination")]
    NoConcreteJumpDestination,

    #[error("Gas limit exceeded")]
    GasLimitExceeded,

    #[error("The instruction at {pointer} is not a JUMPDEST")]
    NotJumpTarget { pointer: u32 },

    #[error("The instruction at {pointer} is not a JUMPI")]
    NotJumpSource { pointer: u32 },

    #[error("Execution was stopped by the watchdog")]
    StoppedByWatchdog,
}

/// An execution error with an associated location in the bytecode.
pub type LocatedError = container::Located<Error>;

/// A container of execution errors used for aggregation of errors during
/// execution.
pub type Errors = container::Errors<LocatedError>;

/// The result type for methods that may have execution errors.
pub type Result<T> = std::result::Result<T, LocatedError>;

/// Make it possible to attach locations to these errors.
impl container::Locatable for Error {
    type Located = LocatedError;

    fn locate(self, instruction_pointer: u32) -> Self::Located {
        container::Located {
            location: instruction_pointer,
            payload:  self,
        }
    }
}
