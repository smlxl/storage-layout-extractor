//! This module contains constants that are needed throughout the codebase.

/// The maximum size that a contract can have when being deployed on the
/// blockchain.
///
/// This is specified in [EIP-170](https://eips.ethereum.org/EIPS/eip-170).
pub const CONTRACT_MAXIMUM_SIZE_BYTES: usize = 24_576;

/// The maximum amount of gas that can be spent in a given block on the EVM.
pub const BLOCK_GAS_LIMIT: usize = 30_000_000;

/// The maximum size that memory can be within the block gas limit.
///
/// Obtained by solving:
///
/// ```text
/// 3 * a + (a^2 / 512) = 30,000,000
/// ```
pub const MAX_MEMORY_SIZE_WORDS: usize = 123_170;

/// The maximum memory size within the block limit in bits.
pub const MAX_MEMORY_SIZE_BITS: usize = MAX_MEMORY_SIZE_WORDS * WORD_SIZE_BITS;

/// The maximum amount of data that will be copied in a single memory operation.
///
/// This is used to bound execution and ensure that we don't end up allocating
/// too much data into memory.
pub const DEFAULT_MEMORY_SINGLE_OPERATION_MAX_BYTES: usize = MAX_MEMORY_SIZE_WORDS * 32 / 10_000;

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
pub const WORD_SIZE_BITS: usize = 256;

/// The width of a byte on the EVM (and most other places) in bits.
pub const BYTE_SIZE_BITS: usize = 8;

/// The width of a word on the EVM in bytes.
pub const WORD_SIZE_BYTES: usize = WORD_SIZE_BITS / BYTE_SIZE_BITS;

/// The bit-width of a bool type.
pub const BOOL_WIDTH_BITS: usize = BYTE_SIZE_BITS;

/// The bit-width of an address type.
pub const ADDRESS_WIDTH_BITS: usize = 160;

/// The bit-width of a selector type.
pub const SELECTOR_WIDTH_BITS: usize = 32;

/// The bit-width of a function type.
pub const FUNCTION_WIDTH_BITS: usize = ADDRESS_WIDTH_BITS + SELECTOR_WIDTH_BITS;

/// The default maximum number of times that the virtual machine will visit each
/// opcode.
pub const DEFAULT_ITERATIONS_PER_OPCODE: usize = 10;

/// The default maximum number of times that the virtual machine will fork
/// during a conditional jump to a given jump target.
pub const DEFAULT_CONDITIONAL_JUMP_PER_TARGET_FORK_LIMIT: usize = 50;

/// The default number of nodes that a symbolic value can contain before it is
/// culled.
pub const DEFAULT_VALUE_SIZE_LIMIT: usize = 250;

/// The default number of loop iterations the extractor will wait before polling
/// the watchdog.
pub const DEFAULT_WATCHDOG_POLL_LOOP_ITERATIONS: usize = 100;

/// The value that solidity uses to type tag `string` in ABI encoding.
pub const SOLIDITY_STRING_POINTER: usize = 0x20;

/// The default value for whether to execute the virtual machine in permissive
/// errors mode.
///
/// Permissive errors mode allows the VM to complete successfully in the
/// presence of non-fatal errors. See [`crate::vm::Config`] for more information
/// on what this entails.
pub const DEFAULT_PERMISSIVE_ERRORS_ENABLED: bool = false;
