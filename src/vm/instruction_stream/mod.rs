//! This module contains the implementation of the [`InstructionStream`], a type
//! that represents a sequence of bytecode instructions and provides utilities
//! for implementing it.

mod macros;
mod parser;

use std::ops::Range;

use crate::{error::VMError, opcode::DynOpcode};

/// The maximum size of an instruction stream, in bytes.
pub const INSTRUCTION_STREAM_MAX_SIZE: u32 = u32::MAX;

/// The instruction stream is a representation of a sequence of [`Opcode`]s that
/// implements some program.
///
/// # Non-Emptiness
///
/// The instruction stream is required to contain _at least one_ instruction.
/// This is validated at construction time.
///
/// # Stream Validity
///
/// This `InstructionStream` is a pure representation of the sequence of
/// instructions and performs no validation that the instruction stream is a
/// valid one. Such validation is up to the [`super::VM`] that utilises the
/// instruction stream.
///
/// To that end, it is _perfectly_ possible, and allowable, to construct an
/// instruction stream containing invalid instructions.
///
/// # Byte-Instruction Correspondence
///
/// Where most [`crate::opcode::Opcode`]s occupy a single byte, the
/// [`crate::opcode::memory::PushN`] opcode is followed in the instruction
/// stream by the data (of size `N` bytes) that needs to be pushed onto the
/// stack.
///
/// To that end, construction of the `InstructionStream` must maintain that
/// correspondence by inserting `N` [`crate::opcode::control::Nop`] opcodes
/// after each instance of `PushN`. They are ignored during execution.
///
/// # Size Limits
///
/// The instruction stream cannot contain more than
/// [`INSTRUCTION_STREAM_MAX_SIZE`] [`crate::opcode::Opcode`]s. This is fine, as
/// the maximum size of a deployed contract's bytecode is 24576 bytes (see
/// [`crate::constant::CONTRACT_MAXIMUM_SIZE_BYTES`]). Even accounting for the
/// analysis of non-deployable contracts, 2^32 bytes should be more than enough
/// to contain the instruction stream of any contract.
///
/// This limit is validated upon construction of the instruction stream, but the
/// stream makes no guarantees as to being able to allocate sufficient memory to
/// contain that many opcodes.
#[derive(Debug)]
pub struct InstructionStream {
    /// The sequence of [`crate::opcode::Opcode`]s.
    instructions: Vec<DynOpcode>,
}

impl InstructionStream {
    /// Gets a new thread of execution as a view on the instruction stream.
    ///
    /// Each view has its independent `instruction_pointer` and can represent a
    /// different thread of execution over the bytecode.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the requested instruction pointer is out of range for
    /// the instruction stream.
    pub fn new_thread(&self, instruction_pointer: u32) -> anyhow::Result<ExecutionThread<'_>> {
        if instruction_pointer as usize >= self.instructions.len() {
            let err = VMError::InstructionPointerOutOfBounds {
                requested: 1,
                available: 1,
            };
            return Err(err.into());
        }
        let instructions = &self.instructions;
        Ok(ExecutionThread {
            instruction_pointer,
            instructions,
        })
    }

    /// Gets the length of the instruction stream in bytes.
    #[allow(clippy::len_without_is_empty)] // The structure cannot be empty.
    pub fn len(&self) -> usize {
        self.instructions.len()
    }
}

/// An [`InstructionStream`] is usually created from a byte array of bytecode.
impl<'a> TryFrom<&'a [u8]> for InstructionStream {
    type Error = anyhow::Error;

    fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
        let instructions = parser::parse(value)?;
        Ok(Self { instructions })
    }
}

/// An [`InstructionStream`] can be created from a string as long as that string
/// is a hexadecimal encoding of the equivalent bytes.
impl TryFrom<&str> for InstructionStream {
    type Error = anyhow::Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let bytes = hex::decode(value)?;
        InstructionStream::try_from(bytes.as_slice())
    }
}

/// A view into the [`InstructionStream`] that allows tracking and manipulation
/// of the instruction pointer. It represents a given stream of execution.
///
/// # Invariants
///
/// The current execution position, as represented by the `instruction_pointer`
/// is guaranteed to always point to an instruction in the stream.
#[derive(Copy, Clone, Debug)]
pub struct ExecutionThread<'opcode> {
    /// The current position of execution, represented as a reference to a slot
    /// in the sequence of instructions.
    instruction_pointer: u32,

    /// The sequence of [`crate::opcode::Opcode`]s.
    instructions: &'opcode Vec<DynOpcode>,
}

impl<'opcode> ExecutionThread<'opcode> {
    /// Gets the opcode at the current execution position.
    pub fn current(&self) -> &DynOpcode {
        &self.instructions[self.instruction_pointer as usize]
    }

    /// Gets the instruction at the specified byte position, if it exists.
    ///
    /// If no instruction exists at the specified instruction pointer location
    /// this method returns [`None`].
    pub fn instruction(&self, byte_offset: u32) -> Option<&DynOpcode> {
        self.instructions.get(byte_offset as usize)
    }

    /// Steps the instruction pointer, moving it to the next instruction and
    /// returning that instruction.
    ///
    /// If the instruction pointer cannot be stepped within the instruction
    /// stream, it will return [`None`] and leave the instruction pointer
    /// unchanged.
    pub fn step(&mut self) -> Option<&DynOpcode> {
        self.jump(1)
    }

    /// Steps the instruction pointer, moving it to the previous instruction and
    /// returning that instruction.
    ///
    /// If the instruction pointer cannot be stepped backward within the
    /// instruction stream, it will return [`None`] and leave the instruction
    /// pointer unchanged.
    pub fn step_backward(&mut self) -> Option<&DynOpcode> {
        self.jump(-1)
    }

    /// Jumps `jump` bytes in the instruction stream.
    ///
    /// If the jump target is not an instruction within the bounds of the
    /// instruction stream, returns [`None`] and leaves the instruction pointer
    /// unchanged.
    pub fn jump(&mut self, jump: i64) -> Option<&DynOpcode> {
        let new_pointer: u32 = if self.instruction_pointer as i64 + jump < 0 {
            return None;
        } else {
            self.instruction_pointer - jump as u32
        };
        if let Some(opcode) = self.instructions.get(new_pointer as usize) {
            self.instruction_pointer = new_pointer;
            Some(opcode)
        } else {
            None
        }
    }

    /// Gets the slice of opcodes in the requested range.
    ///
    /// The provided `range` is left-inclusive and right-exclusive.
    pub fn slice(&mut self, range: Range<u32>) -> Option<&[DynOpcode]> {
        #[allow(clippy::cast_possible_truncation)] // Safe due to length invariant.
        let bound = self.len() as u32;
        if range.is_empty() || range.start >= bound || range.end >= bound {
            return None;
        }

        let range_usize: Range<usize> = Range {
            start: range.start as usize,
            end:   range.end as usize,
        };

        Some(&self.instructions[range_usize])
    }

    /// Gets the first instruction in the opcode stream without altering the
    /// position of the instruction pointer.
    pub fn start(&self) -> &DynOpcode {
        &self.instructions[0]
    }

    /// Gets the last instruction in the opcode stream without altering the
    /// position of the instruction pointer.
    pub fn end(&self) -> &DynOpcode {
        &self.instructions[self.instructions.len() - 1]
    }

    /// Gets the length of the instruction stream in bytes.
    #[allow(clippy::len_without_is_empty)] // The structure cannot be empty.
    pub fn len(&self) -> usize {
        self.instructions.len()
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn can_parse_from_bytes() -> anyhow::Result<()> {
        todo!()
    }
}
