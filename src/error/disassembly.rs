//! This module contains the error type that pertains to the disassembly
//! process.

use thiserror::Error;

use crate::error::container;

/// Errors that occur during the process of disassembling the bytecode into the
/// library's rich internal [`crate::opcode::Opcode`] types.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum Error {
    #[error("Invalid number of topics {_0:?} provided to the `LOG` opcode")]
    InvalidTopicCount(u8),

    #[error("Invalid size {_0:?} provided to the `PUSH` opcode")]
    InvalidPushSize(u8),

    #[error("Invalid stack item {item:?} provided for the `{name}` opcode")]
    InvalidStackItem { item: u8, name: String },

    #[error("Bytecode cannot be empty")]
    EmptyBytecode,

    #[error("The provided hexadecimal input had an odd length")]
    InvalidHexLength,

    #[error("Encountered invalid hex char {_0:?} at index {_1:?}")]
    InvalidHexCharacter(char, usize),

    #[error("The length of the bytecode exceeded {}", u32::MAX)]
    BytecodeTooLarge,
}

/// A disassembly error with an associated location in the bytecode.
pub type LocatedError = container::Located<Error>;

/// The result type for functions that may return disassembly errors.
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
