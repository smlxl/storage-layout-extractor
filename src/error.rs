//! This module contains error types for the analyser, split into a number of
//! enums by subsystem.
//!
//! All of the errors implement [`std::error::Error`], and hence can be used
//! with [`anyhow::Error`].

use thiserror::Error;

/// Errors from the [`crate::vm`] subsystem of the library.
#[derive(Debug, Eq, Error, PartialEq)]
pub enum VMError {
    #[error(
        "Instruction pointer {requested:?} is out of bounds in stream of length {available:?}"
    )]
    InstructionPointerOutOfBounds { requested: usize, available: usize },
}

/// Errors encountered during parsing a bytecode stream.
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