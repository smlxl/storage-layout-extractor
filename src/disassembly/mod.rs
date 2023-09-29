//! This module contains the implementation of the [`InstructionStream`], a type
//! that represents a sequence of bytecode instructions and provides utilities
//! for implementing it.

mod disassembler;

use std::{ops::Range, rc::Rc};

use downcast_rs::Downcast;
use hex::FromHexError;

use crate::{
    error::{container::Locatable, disassembly, disassembly::Error, execution},
    opcode::{DynOpcode, Opcode},
};

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
/// valid one. Such validation is up to the [`crate::vm::VM`] that utilises the
/// instruction stream.
///
/// To that end, it is _perfectly_ possible, and allowable, to construct an
/// instruction stream containing invalid instructions.
///
/// # Byte-Instruction Correspondence
///
/// Where most [`Opcode`]s occupy a single byte, the
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
/// stream makes _no guarantees_ as to being able to allocate sufficient memory
/// to contain that many opcodes.
#[derive(Clone, Debug)]
pub struct InstructionStream {
    /// The sequence of [`Opcode`]s.
    instructions: Rc<Vec<DynOpcode>>,
}

impl InstructionStream {
    /// Gets a new thread of execution as a view on the instruction stream.
    ///
    /// Each view has its independent `instruction_pointer` and can represent a
    /// different thread of execution over the bytecode.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the requested `instruction_pointer` is out of range for
    /// the instruction stream.
    pub fn new_thread(&self, instruction_pointer: u32) -> execution::Result<ExecutionThread> {
        if instruction_pointer as usize >= self.instructions.len() {
            return Err(execution::Error::InstructionPointerOutOfBounds {
                requested: 1,
                available: 1,
            }
            .locate(instruction_pointer));
        }
        let instructions = self.instructions.clone();
        Ok(ExecutionThread {
            instruction_pointer,
            instructions,
        })
    }

    /// Gets the length of the instruction stream in bytes.
    #[allow(clippy::len_without_is_empty)] // The structure cannot be empty.
    #[must_use]
    pub fn len(&self) -> usize {
        self.instructions.len()
    }

    /// Converts the instructions in the instruction stream to their
    /// corresponding bytecode.
    ///
    /// This should always result in the same bytecode as the input to the
    /// disassembly process.
    #[must_use]
    pub fn as_bytecode(&self) -> Vec<u8> {
        self.instructions.iter().flat_map(|opcode| opcode.encode()).collect()
    }
}

/// An [`InstructionStream`] is usually created from a byte array of bytecode.
impl<'a> TryFrom<&'a [u8]> for InstructionStream {
    type Error = disassembly::LocatedError;

    fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
        let instructions = Rc::new(disassembler::disassemble(value)?);
        let result = Self { instructions };

        // An assertion that will be disabled in production builds, but a good sanity
        // check that disassembly didn't go wrong
        assert_eq!(result.as_bytecode().as_slice(), value);
        Ok(result)
    }
}

/// An [`InstructionStream`] can be created from a string as long as that string
/// is a hexadecimal encoding of the equivalent bytes.
impl TryFrom<&str> for InstructionStream {
    type Error = disassembly::LocatedError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let bytes = match hex::decode(value) {
            Ok(b) => b,
            Err(e) => {
                let locate =
                    |val| u32::try_from(val).map_err(|_| Error::BytecodeTooLarge.locate(u32::MAX));

                let error = if let FromHexError::InvalidHexCharacter { c, index } = e {
                    let location = locate(index);
                    Error::InvalidHexCharacter(c, index).locate(location?)
                } else {
                    let location = locate(value.len());
                    Error::InvalidHexLength.locate(location?)
                };

                return Err(error);
            }
        };
        InstructionStream::try_from(bytes.as_slice())
    }
}

/// Allows converting the [`InstructionStream`] back to the corresponding
/// bytecode representation.
///
/// This should always result in the same bytecode as the input to the
/// disassembly process.
impl From<InstructionStream> for Vec<u8> {
    fn from(value: InstructionStream) -> Self {
        value.instructions.iter().flat_map(|opcode| opcode.encode()).collect()
    }
}

impl From<InstructionStream> for Rc<Vec<DynOpcode>> {
    fn from(value: InstructionStream) -> Self {
        value.instructions
    }
}

/// A view into the [`InstructionStream`] that allows tracking and manipulation
/// of the instruction pointer. It represents a given stream of execution.
///
/// # Invariants
///
/// The current execution position, as represented by the `instruction_pointer`
/// is guaranteed to always point to an instruction in the stream.
#[derive(Clone, Debug)]
pub struct ExecutionThread {
    /// The current position of execution, represented as a reference to a slot
    /// in the sequence of instructions.
    instruction_pointer: u32,

    /// The sequence of [`Opcode`]s.
    instructions: Rc<Vec<DynOpcode>>,
}

impl ExecutionThread {
    /// Gets the current value of the instruction pointer for this thread of
    /// execution.
    #[must_use]
    pub fn instruction_pointer(&self) -> u32 {
        self.instruction_pointer
    }

    /// Gets the opcode at the current execution position.
    #[must_use]
    pub fn current(&self) -> DynOpcode {
        self.instructions[self.instruction_pointer as usize].clone()
    }

    /// Gets the instruction at the specified `instruction_pointer` location, if
    /// it exists.
    ///
    /// If no instruction exists at the specified `instruction_pointer` location
    /// this method returns [`None`].
    #[must_use]
    pub fn instruction(&self, instruction_pointer: u32) -> Option<DynOpcode> {
        self.instructions.get(instruction_pointer as usize).cloned()
    }

    /// Gets the instruction at the specified `instruction_pointer` location as
    /// the specified concrete type `T`, if it exists.
    ///
    /// If no instruction exists at the specified `instruction_pointer`
    /// location, or the instruction exists but is not of type `T`, this method
    /// returns [`None`],
    #[must_use]
    pub fn instruction_as<T: Opcode + Clone>(&self, instruction_pointer: u32) -> Option<T> {
        self.instruction(instruction_pointer)
            .and_then(|op| op.as_any().downcast_ref::<T>().cloned())
    }

    /// Steps the instruction pointer, moving it to the next instruction and
    /// returning that instruction.
    ///
    /// If the instruction pointer cannot be stepped within the instruction
    /// stream, it will return [`None`] and leave the instruction pointer
    /// unchanged.
    pub fn step(&mut self) -> Option<DynOpcode> {
        self.jump_by(1)
    }

    /// Steps the instruction pointer, moving it to the previous instruction and
    /// returning that instruction.
    ///
    /// If the instruction pointer cannot be stepped backward within the
    /// instruction stream, it will return [`None`] and leave the instruction
    /// pointer unchanged.
    pub fn step_backward(&mut self) -> Option<DynOpcode> {
        self.jump_by(-1)
    }

    /// Jumps by `jump` bytes in the instruction stream.
    ///
    /// If the jump target is not an instruction within the bounds of the
    /// instruction stream, returns [`None`] and leaves the instruction pointer
    /// unchanged.
    pub fn jump_by(&mut self, jump: i64) -> Option<DynOpcode> {
        let new_pointer: u32 = if i64::from(self.instruction_pointer) + jump < 0 {
            return None;
        } else if let Ok(ptr) = u32::try_from(i64::from(self.instruction_pointer) + jump) {
            ptr
        } else {
            return None;
        };

        if let Some(opcode) = self.instructions.get(new_pointer as usize) {
            self.instruction_pointer = new_pointer;
            Some(opcode.clone())
        } else {
            None
        }
    }

    /// Jumps to the opcode at an offset of `target` bytes in the instruction
    /// stream.
    ///
    /// Returns [`None`] if the `target` is not within the bounds of the
    /// instruction stream, and leaves the pointer unchanged.
    pub fn jump(&mut self, target: u32) -> Option<DynOpcode> {
        if (target as usize) < self.len() {
            self.instruction_pointer = target;
            Some(self.current())
        } else {
            None
        }
    }

    /// Sets the execution position to the opcode at `offset` in the instruction
    /// stream if possible, returning that opcode if so.
    ///
    /// Returns [`None`] if there is no opcode at `offset`.
    pub fn at(&mut self, offset: u32) -> Option<DynOpcode> {
        if offset as usize >= self.instructions.len() {
            return None;
        }

        self.instruction_pointer = offset;

        Some(self.current())
    }

    /// Gets the slice of opcodes in the requested range.
    ///
    /// The provided `range` is left-inclusive and right-exclusive.
    ///
    /// # Panics
    ///
    /// If the length of the bytecode exceeds [`u32::MAX`]. This is a programmer
    /// error.
    #[must_use]
    pub fn slice(&mut self, range: Range<u32>) -> Option<&[DynOpcode]> {
        let bound = u32::try_from(self.len())
            .unwrap_or_else(|_| panic!("Bytecode length cannot exceed u32::MAX"));
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
    #[must_use]
    pub fn start(&self) -> DynOpcode {
        self.instructions[0].clone()
    }

    /// Gets the last instruction in the opcode stream without altering the
    /// position of the instruction pointer.
    #[must_use]
    pub fn end(&self) -> DynOpcode {
        self.instructions[self.instructions.len() - 1].clone()
    }

    /// Gets the length of the instruction stream in bytes.
    #[allow(clippy::len_without_is_empty)] // The structure cannot be empty.
    #[must_use]
    pub fn len(&self) -> usize {
        self.instructions.len()
    }
}

#[cfg(test)]
mod test {
    use crate::{
        constant::{DUP_OPCODE_BASE_VALUE, LOG_OPCODE_BASE_VALUE, SWAP_OPCODE_BASE_VALUE},
        disassembly::InstructionStream,
        error::disassembly,
        opcode::{control, memory, Opcode},
    };

    #[test]
    fn can_parse_from_bytes() {
        // Let's get all of the non-consolidated opcodes as bytes.
        let bytes = util::get_non_consolidated_opcode_bytes();

        // It should result in a valid stream of opcodes.
        let instruction_stream =
            InstructionStream::try_from(bytes.as_slice()).expect("Parsing errored");

        // The bytecode from it should equal the original bytecode.
        let bytecode: Vec<u8> = instruction_stream.into();
        assert_eq!(bytecode, bytes);
    }

    #[test]
    fn can_parse_from_hex_stream() {
        let bytes = util::get_non_consolidated_opcode_bytes();
        let hex_string = hex::encode(bytes.as_slice());

        // It should result in a valid stream of opcodes.
        let instruction_stream =
            InstructionStream::try_from(hex_string.as_str()).expect("Parsing errored");

        // The bytecode from this should equal the original bytecode.
        let bytecode: Vec<u8> = instruction_stream.into();
        assert_eq!(bytecode, bytes);
    }

    #[test]
    fn translates_unknown_opcode_to_invalid() {
        // This opcode doesn't exist.
        let bytes: Vec<u8> = vec![0xf9];

        // So this should fail.
        let result = InstructionStream::try_from(bytes.as_slice()).expect("Parsing errored");
        let thread = result.new_thread(0).unwrap();
        assert_eq!(
            thread.instruction(0).unwrap().as_ref().encode(),
            control::Invalid::new(0xf9).encode()
        );
    }

    #[test]
    fn emits_parse_error_on_incorrectly_encoded_hex_string() {
        // This is not actually hex-encoded.
        let not_hex_encoded = "ab70anx7302842";

        // It should fail to parse.
        let result =
            InstructionStream::try_from(not_hex_encoded).expect_err("Parsing did not error");

        // It should be a specific error.
        assert_eq!(result.location, 5);
        assert_eq!(
            result.payload,
            disassembly::Error::InvalidHexCharacter('n', 5)
        );
    }

    #[test]
    fn emits_parse_error_on_hex_string_with_bad_length() {
        // This is hex encoded but bad length
        let bad_length = "ab21fe9b5";

        // It should fail to parse.
        let result = InstructionStream::try_from(bad_length).expect_err("Parsing did not error");

        // It should be a specific error.
        assert_eq!(result.location, u32::try_from(bad_length.len()).unwrap());
        assert_eq!(result.payload, disassembly::Error::InvalidHexLength);
    }

    #[test]
    fn emits_parse_error_on_empty_input() {
        // Our input is empty.
        let input: Vec<u8> = vec![];

        // It should fail to parse.
        let result =
            InstructionStream::try_from(input.as_slice()).expect_err("Parsing did not error");

        // It should be a specific error.
        assert_eq!(result.location, 0);
        assert_eq!(result.payload, disassembly::Error::EmptyBytecode);
    }

    #[test]
    fn can_parse_push_opcode() -> anyhow::Result<()> {
        // The input is all of the push opcodes `PUSH1..=PUSH32`, with random data
        // encoded after them as the data to push.
        let bytes = util::get_valid_push_opcodes(1..=32)?;

        // This should parse correctly, and end up with something of the same length so
        // as to maintain offsets.
        let result = InstructionStream::try_from(bytes.as_slice()).expect("Parsing failed");
        assert_eq!(result.len(), bytes.len());

        // The bytecode from this should equal the original bytecode.
        let bytecode: Vec<u8> = result.into();
        assert_eq!(bytecode, bytes);

        Ok(())
    }

    #[test]
    fn can_parse_dup_opcode() {
        // The input is all of the dup opcodes.
        let mut bytes: Vec<u8> = vec![];
        for x in 1..=16 {
            bytes.push(DUP_OPCODE_BASE_VALUE + x);
        }

        // This should parse correctly.
        let result = InstructionStream::try_from(bytes.as_slice()).expect("Parsing failed");

        // The bytecode from this should equal the original bytecode.
        let bytecode: Vec<u8> = result.into();
        assert_eq!(bytecode, bytes);
    }

    #[test]
    fn can_parse_swap_opcode() {
        // The input is all of the swap opcodes.
        let mut bytes: Vec<u8> = vec![];
        for x in 1..=16 {
            bytes.push(SWAP_OPCODE_BASE_VALUE + x);
        }

        // This should parse correctly.
        let result = InstructionStream::try_from(bytes.as_slice()).expect("Parsing failed");

        // The bytecode from this should equal the original bytecode.
        let bytecode: Vec<u8> = result.into();
        assert_eq!(bytecode, bytes);
    }

    #[test]
    fn can_parse_log_opcode() {
        // The input is all of the log opcodes.
        let mut bytes: Vec<u8> = vec![];
        for x in 0..=4 {
            bytes.push(LOG_OPCODE_BASE_VALUE + x);
        }

        // This should parse correctly.
        let result = InstructionStream::try_from(bytes.as_slice()).expect("Parsing failed");

        // The bytecode from this should equal the original bytecode.
        let bytecode: Vec<u8> = result.into();
        assert_eq!(bytecode, bytes);
    }

    #[test]
    fn maintains_byte_offsets_with_push() -> anyhow::Result<()> {
        // The input is all of the push opcodes with their data.
        let bytes = util::get_valid_push_opcodes(1..=32)?;

        // Let's get the instruction stream and a thread of execution on it starting at
        // the first instruction.
        let instructions = InstructionStream::try_from(bytes.as_slice()).expect("Parsing failed");
        let thread = instructions.new_thread(0)?;

        // These should have the same length.
        assert_eq!(thread.len(), bytes.len());

        // The bytes corresponding to an arbitrary push instruction should be the same.
        let push3 = thread.instruction(5).unwrap();
        assert_eq!(push3.as_byte(), bytes[5]);

        // But the bytes after it should exist in the instruction not the stream,
        // replaced by NOP.
        assert_eq!(
            thread.instruction(6).unwrap().as_text_code(),
            control::Nop.as_text_code()
        );
        let concrete = push3
            .as_ref()
            .as_any()
            .downcast_ref::<memory::PushN>()
            .expect("Was not a PUSH opcode");
        let opcode_byte_stream = concrete.encode();
        let expected_bytes = &bytes[5..=8];
        assert_eq!(opcode_byte_stream.as_slice(), expected_bytes);

        Ok(())
    }

    /// Utilities for writing the tests.
    mod util {
        use std::ops::RangeInclusive;

        use anyhow::anyhow;

        use crate::constant::PUSH_OPCODE_BASE_VALUE;

        /// Provides the bytes corresponding to all of the non-consolidated
        /// opcodes.
        pub fn get_non_consolidated_opcode_bytes() -> Vec<u8> {
            let bytes: Vec<u8> = vec![
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x10, 0x11,
                0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x20, 0x30,
                0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e,
                0x3f, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x50, 0x51, 0x52, 0x53,
                0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5f, 0xf0, 0xf1, 0xf2, 0xf3, 0xf4,
                0xf5, 0xfa, 0xfd, 0xfe, 0xff,
            ];

            bytes
        }

        /// Creates a valid set of push opcodes (with random data to be pushed
        /// encoded after them) for the provided range.
        ///
        /// # Errors
        ///
        /// If the range is outside 1..=32.
        pub fn get_valid_push_opcodes(range: RangeInclusive<u8>) -> anyhow::Result<Vec<u8>> {
            if *range.start() < 1 || *range.end() > 32 {
                return Err(anyhow!("Invalid range of sizes for push opcodes"));
            }
            let mut bytes: Vec<u8> = vec![];

            for size in range {
                let mut op_and_data = vec![PUSH_OPCODE_BASE_VALUE + size];
                for _ in 0..size {
                    op_and_data.push(rand::random());
                }

                bytes.extend(op_and_data);
            }

            Ok(bytes)
        }
    }
}
