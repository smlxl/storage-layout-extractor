//! This module contains error types for the analyser, split into a number of
//! enums by subsystem.
//!
//! All of the errors implement [`std::error::Error`], and hence can be used
//! with [`anyhow::Error`].

use thiserror::Error;

use crate::vm::value::known_data::KnownData;

/// Errors from the [`crate::vm`] subsystem of the library.
#[derive(Debug, Eq, Error, PartialEq)]
pub enum VMError {
    #[error(
        "Instruction pointer {requested:?} is out of bounds in stream of length {available:?}"
    )]
    InstructionPointerOutOfBounds { requested: usize, available: usize },

    #[error("Maximum stack depth exceeded with request for {requested:?} frames")]
    StackDepthExceeded { requested: usize },

    #[error("A stack frame at depth {depth:?} was requested but none was available")]
    NoSuchStackFrame { depth: i64 },

    #[error("A VM thread was requested but none are available")]
    NoSuchThread,

    #[error("Tried to step the virtual machine when no target exists")]
    InvalidStep,

    #[error("{data:?} cannot be used as an immediate for a jump")]
    InvalidOffsetForJump { data: KnownData },

    #[error("The opcode at {offset:?} is not a valid jump destination")]
    InvalidJumpTarget { offset: u32 },

    #[error("No opcode exists at {offset:?}")]
    NonExistentJumpTarget { offset: u32 },

    #[error("No concrete immediate was found for the jump destination")]
    NoConcreteJumpDestination,
}

/// Errors encountered during parsing a bytecode stream in
/// [`crate::vm::instructions`].
#[derive(Debug, Eq, Error, PartialEq)]
pub enum ParseError {
    #[error("{_0:?} is not a valid EVM opcode")]
    InvalidOpcode(u8),

    #[error("Bytecode cannot be empty")]
    EmptyBytecode,

    #[error("The provided hexadecimal input had an odd length")]
    InvalidHexLength,

    #[error("Encountered invalid hex char {_0:?} at index {_1:?}")]
    InvalidHexCharacter(char, usize),
}

/// Errors from the [`crate::opcode`] subsystem of the library.
#[derive(Debug, Eq, Error, PartialEq)]
pub enum OpcodeError {
    #[error("Invalid number of topics {_0:?} provided to the `LOG` opcode")]
    InvalidTopicCount(u8),

    #[error("Invalid size {_0:?} provided to the `PUSH` opcode")]
    InvalidPushSize(u8),

    #[error("Invalid stack item {item:?} provided for the `{name}` opcode")]
    InvalidStackItem { item: u8, name: String },
}
