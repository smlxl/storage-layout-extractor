//! This module contains constants that are needed throughout the codebase.

/// The maximum size that a contract can have when being deployed on the
/// blockchain.
///
/// This is specified in [EIP-170](https://eips.ethereum.org/EIPS/eip-170).
pub const CONTRACT_MAXIMUM_SIZE_BYTES: usize = 24576;

/// The maximum amount of gas that can be spent in a given block on the EVM.
pub const BLOCK_GAS_LIMIT: usize = 30_000_000;

/// The base byte value for the `PUSH` opcode, for `N > 0`.
///
/// This is constructed such that for `PUSHN`, `PUSH_OPCODE_BASE_VALUE` + `N`
/// equals the byte value for the corresponding `PUSH` opcode.
pub const PUSH_OPCODE_BASE_VALUE: u8 = 0x5f;

/// The base byte value for the `DUP` opcode.
///
/// This is constructed such that for `DUPN`, `DUP_OPCODE_BASE_VALUE` + `N`
/// equals the byte value for the corresponding `DUP` opcode.
pub const DUP_OPCODE_BASE_VALUE: u8 = 0x7f;

/// The base byte value for the `SWAP` opcode.
///
/// This is constructed such that for `SWAPN`, `SWAP_OPCODE_BASE_VALUE` + `N`
/// equals the byte value for the corresponding `SWAP` opcode.
pub const SWAP_OPCODE_BASE_VALUE: u8 = 0x8f;

/// The base byte value for the `LOG` opcode.
///
/// This is constructed such that for `LOGN`, `LOG_OPCODE_BASE_VALUE` + `N`
/// equals the byte value for the corresponding `LOG` opcode.
pub const LOG_OPCODE_BASE_VALUE: u8 = 0xa0;

/// The maximum number of bytes that can be pushed at once using the `PUSH`
/// opcode.
pub const PUSH_OPCODE_MAX_BYTES: u8 = 32;

/// The maximum stack depth for the EVM.
pub const MAXIMUM_STACK_DEPTH: usize = 1024;

/// The width of word on the EVM in bits.
pub const WORD_SIZE: usize = 256;

/// The default number of times that the virtual machine will visit each opcode.
pub const DEFAULT_ITERATIONS_PER_OPCODE: usize = 10;
