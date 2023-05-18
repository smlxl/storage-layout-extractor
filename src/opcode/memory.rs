//! Opcodes that perform operations on memory or stack on the EVM.

#![allow(unused_variables)] // Temporary allow to suppress valid warnings for now.

use crate::{
    constant::{
        DUP_OPCODE_BASE_VALUE,
        PUSH_OPCODE_BASE_VALUE,
        PUSH_OPCODE_MAX_BYTES,
        SWAP_OPCODE_BASE_VALUE,
    },
    error::OpcodeError,
    opcode::Opcode,
    vm::VM,
};

/// The `CALLDATALOAD` opcode gets the input data for the current environment.
///
/// # Semantics
///
/// | Stack Index | Input    | Output                                   |
/// | :---------: | :------: | :--------------------------------------: |
/// | 1           | `offset` | `result := msg.data\[offset:offset+32\]` |
///
/// where:
///
/// - `offset` is the byte offset in the call data from which to start loading
/// - `result` is the result of the specified load, with any bytes after the end
///   of the calldata set to zero
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallDataLoad;

impl Opcode for CallDataLoad {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "CALLDATALOAD".into()
    }

    fn as_byte(&self) -> u8 {
        0x35
    }
}

/// The `CALLDATASIZE` opcode gets the size of the input data for the current
/// environment.
///
/// # Semantics
///
/// | Stack Index | Input | Output          |
/// | :---------: | :---: | :-------------: |
/// | 1           |       | `len(msg.data)` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallDataSize;

impl Opcode for CallDataSize {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "CALLDATASIZE".into()
    }

    fn as_byte(&self) -> u8 {
        0x36
    }
}

/// The `CALLDATACOPY` opcode copies the input data for the current environment
/// into memory.
///
/// # Semantics
///
/// | Stack Index | Input        | Output |
/// | :---------: | :----------: | :----: |
/// | 1           | `destOffset` |        |
/// | 2           | `offset`     |        |
/// | 3           | `size`       |        |
///
/// where:
///
/// - `destOffset` is the byte offset in the memory where the call data will be
///   copied to (`mem\[destOffset:destOffset+size\] :=
///   msg.data\[offset:offset+size\]`)
/// - `offset` is the byte offset in the call data from which to start copying
/// - `size` is the number of bytes to copy
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallDataCopy;

impl Opcode for CallDataCopy {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "CALLDATACOPY".into()
    }

    fn as_byte(&self) -> u8 {
        0x37
    }
}

/// The `CODESIZE` opcode gets the code size of the current contract.
///
/// # Semantics
///
/// | Stack Index | Input | Output           |
/// | :---------: | :---: | :--------------: |
/// | 1           |       | `len(this.code)` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CodeSize;

impl Opcode for CodeSize {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "CODESIZE".into()
    }

    fn as_byte(&self) -> u8 {
        0x38
    }
}

/// The `CODECOPY` opcode copies the current contract's code into memory.
///
/// # Semantics
///
/// | Stack Index | Input        | Output |
/// | :---------: | :----------: | :----: |
/// | 1           | `destOffset` |        |
/// | 2           | `offset`     |        |
/// | 3           | `size`       |        |
///
/// where:
///
/// - `destOffset` is the byte offset in the memory where the call data will be
///   copied to (`mem\[destOffset:destOffset+size\] :=
///   this.code\[offset:offset+size\]`)
/// - `offset` is the byte offset in the code from which to start copying
/// - `size` is the number of bytes to copy
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CodeCopy;

impl Opcode for CodeCopy {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "CODECOPY".into()
    }

    fn as_byte(&self) -> u8 {
        0x39
    }
}

/// The `EXTCODESIZE` opcode gets the code size of the contract at the target
/// address.
///
/// # Semantics
///
/// | Stack Index | Input     | Output              |
/// | :---------: | :-------: | :-----------------: |
/// | 1           | `address` | `len(address.code)` |
///
/// where:
///
/// - `address` is the address of the contract to get the code size from
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ExtCodeSize;

impl Opcode for ExtCodeSize {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "EXTCODESIZE".into()
    }

    fn as_byte(&self) -> u8 {
        0x3b
    }
}

/// The `CODECOPY` opcode copies the current contract's code into memory.
///
/// # Semantics
///
/// | Stack Index | Input        | Output |
/// | :---------: | :----------: | :----: |
/// | 1           | `address`    |        |
/// | 2           | `destOffset` |        |
/// | 3           | `offset`     |        |
/// | 4           | `size`       |        |
///
/// where:
///
/// - `address` is the address of the contract to copy the code from
/// - `destOffset` is the byte offset in the memory where the call data will be
///   copied to (`mem\[destOffset:destOffset+size\] :=
///   address.code\[offset:offset+size\]`)
/// - `offset` is the byte offset in the code from which to start copying
/// - `size` is the number of bytes to copy
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ExtCodeCopy;

impl Opcode for ExtCodeCopy {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        4
    }

    fn as_text_code(&self) -> String {
        "EXTCODECOPY".into()
    }

    fn as_byte(&self) -> u8 {
        0x3c
    }
}

/// The `RETURNDATASIZE` opcode gets the size of the output data from the
/// previous (sub-)context.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | `size` |
///
/// where:
///
/// - `size` is the size of the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ReturnDataSize;

impl Opcode for ReturnDataSize {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "RETURNDATASIZE".into()
    }

    fn as_byte(&self) -> u8 {
        0x3d
    }
}

/// The `RETURNDATACOPY` opcode copies the output data from the previous call
/// into memory.
///
/// # Semantics
///
/// | Stack Index | Input        | Output |
/// | :---------: | :----------: | :----: |
/// | 1           | `destOffset` |        |
/// | 2           | `offset`     |        |
/// | 3           | `size`       |        |
///
/// where:
///
/// - `destOffset` is the byte offset in the memory where the call data will be
///   copied to (`mem\[destOffset:destOffset+size\] :=
///   returnData\[offset:offset+size\]`)
/// - `offset` is the byte offset in the code from which to start copying
/// - `size` is the number of bytes to copy
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ReturnDataCopy;

impl Opcode for ReturnDataCopy {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "RETURNDATACOPY".into()
    }

    fn as_byte(&self) -> u8 {
        0x3e
    }
}

/// The `POP` opcode pops the top item from the stack.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | `i`   |        |
///
/// where:
///
/// - `i` is the current top item on the stack
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Pop;

impl Opcode for Pop {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "POP".into()
    }

    fn as_byte(&self) -> u8 {
        0x50
    }
}

/// The `MLOAD` opcode loads a word from memory.
///
/// # Semantics
///
/// | Stack Index | Input    | Output                    |
/// | :---------: | :------: | :-----------------------: |
/// | 1           | `offset` | `result := mem\[offset:offset+32\]` |
///
/// where:
///
/// - `offset` is the byte offset in memory to read the word from
/// - `result` is the 32 bytes beginning at `offset`, with any bytes beyond the
///   current memory size (see [`MSize`]) filled with 0s
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MLoad;

impl Opcode for MLoad {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "MLOAD".into()
    }

    fn as_byte(&self) -> u8 {
        0x51
    }
}

/// The `MSTORE` opcode stores a word to memory.
///
/// # Semantics
///
/// | Stack Index | Input    | Output                            |
/// | :---------: | :------: | :-------------------------------: |
/// | 1           | `offset` |                                   |
/// | 2           | `value`  |                                   |
///
/// where:
///
/// - `offset` is the target byte offset in the memory
/// - `value` is the 32-byte value to write at `offset` as follows
///   `mem\[offset:offset+32\] := value`
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MStore;

impl Opcode for MStore {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "MSTORE".into()
    }

    fn as_byte(&self) -> u8 {
        0x52
    }
}

/// The `MSTORE8` opcode stores a byte to memory.
///
/// # Semantics
///
/// | Stack Index | Input    | Output |
/// | :---------: | :------: | :----: |
/// | 1           | `offset` |        |
/// | 2           | `value`  |        |
///
/// where:
///
/// - `offset` is the byte offset in memory to write to
/// - `value` is the one-byte value to write at `offset` as follows
///   `mem\[offset:offset+1\] := v`
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MStore8;

impl Opcode for MStore8 {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "MSTORE8".into()
    }

    fn as_byte(&self) -> u8 {
        0x53
    }
}

/// The `SLOAD` opcode loads a word from storage.
///
/// # Semantics
///
/// | Stack Index | Input | Output                    |
/// | :---------: | :---: | :-----------------------: |
/// | 1           | `key` | `value := storage\[key\]` |
///
/// where:
///
/// - `key` is the 32-byte storage key to read from
/// - `value` is the 32-byte value read from storage, or 0 if that key was never
///   written to
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SLoad;

impl Opcode for SLoad {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "SLOAD".into()
    }

    fn as_byte(&self) -> u8 {
        0x54
    }
}

/// The `SSTORE` opcode writes a word to storage based on a 32-byte key `k`.
///
/// # Semantics
///
///
/// | Stack Index | Input   | Output |
/// | :---------: | :-----: | :----: |
/// | 1           | `key`   |        |
/// | 2           | `value` |        |
///
/// where:
///
/// - `key` is the 32-byte storage key to write to
/// - `value` is the 32-byte value to be written to as follows `storage\[key\]
///   := value`
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SStore;

impl Opcode for SStore {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "SSTORE".into()
    }

    fn as_byte(&self) -> u8 {
        0x55
    }
}

/// The `MSIZE` opcode gets the size of the active memory in bytes. This is
/// equivalent to the highest offset that has been accessed during the current
/// execution.
///
/// # Semantics
///
/// | Stack Index | Input | Output     |
/// | :---------: | :---: | :--------: |
/// | 1           |       | `len(mem)` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MSize;

impl Opcode for MSize {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "MSIZE".into()
    }

    fn as_byte(&self) -> u8 {
        0x59
    }
}

/// The `PUSH0` opcode places the value 0 on the top of the stack.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | `0`    |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Push0;

impl Opcode for Push0 {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "PUSH0".into()
    }

    fn as_byte(&self) -> u8 {
        0x5f
    }
}

/// The `PUSHN` opcodes push an `N`-byte item onto the stack, where `0 < N <=
/// 32`. The item is specified as the next `N` bytes of the instruction stream.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | `item` |
///
/// where:
///
/// - `item` is the next `N` bytes of the instruction stream; the value to push
///   onto the stack
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PushN {
    byte_count: u8,
    bytes:      Vec<u8>,
}

impl PushN {
    /// Construct a new instance of the `PUSHN` opcode for some `n`.
    ///
    /// # Errors
    ///
    /// If `n` is not in the specified range.
    pub fn new(n: u8, bytes: impl Into<Vec<u8>>) -> anyhow::Result<Self> {
        let bytes: Vec<u8> = bytes.into();
        if n > 0 && n <= PUSH_OPCODE_MAX_BYTES && bytes.len() == n as usize {
            Ok(Self {
                byte_count: n,
                bytes,
            })
        } else {
            let err = OpcodeError::InvalidPushSize(n);
            Err(err.into())
        }
    }

    /// Get the number of bytes this `PUSHN` opcode pushes onto the stack.
    pub fn byte_size(&self) -> u8 {
        self.byte_count
    }

    /// Get the data to be pushed onto the stack by this opcode. It is
    /// guaranteed that `bytes_data.len() == byte_size()`.
    pub fn bytes_data(&self) -> &[u8] {
        &self.bytes
    }
}

impl Opcode for PushN {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        format!("PUSH{}", self.byte_count)
    }

    fn as_byte(&self) -> u8 {
        PUSH_OPCODE_BASE_VALUE + self.byte_count
    }

    fn encode(&self) -> Vec<u8> {
        let mut data = vec![self.as_byte()];
        data.extend(self.bytes_data());
        data
    }
}

/// The `DUPN` opcode duplicates the `N`th item on the stack, where `0 < N <=
/// 16`, pushing it on the top of the stack. This makes the duplicated item the
/// `N+1`th item.
///
/// # Semantics
///
/// | Stack Index | Input  | Output |
/// | :---------: | :----: | :----: |
/// | 1           |        | `item` |
/// | ...         |        |        |
/// | `N+1`       | `item` | `item` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Dup {
    item: u8,
}

impl Dup {
    /// Constructs a new instance of the `DUPN` opcode.
    ///
    /// # Errors
    ///
    /// If the provided `n` is not in the specified range.
    pub fn new(n: u8) -> anyhow::Result<Self> {
        if 0 < n && n <= 16 {
            Ok(Self { item: n })
        } else {
            let err = OpcodeError::InvalidStackItem {
                item: n,
                name: "DUP".into(),
            };
            Err(err.into())
        }
    }

    /// Gets the item on the stack that this opcode is duplicating.
    pub fn n(&self) -> u8 {
        self.item
    }
}

impl Opcode for Dup {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        self.item as usize
    }

    fn as_text_code(&self) -> String {
        format!("DUP{}", self.item)
    }

    fn as_byte(&self) -> u8 {
        DUP_OPCODE_BASE_VALUE + self.item
    }
}

/// The `SWAPN` opcode exchanges the first and `N+1`th stack items, where `0 < N
/// <= 16`.
///
/// # Semantics
///
/// | Stack Index | Input   | Output  |
/// | :---------: | :-----: | :-----: |
/// | 1           | `item1` | `item2` |
/// | ...         |         |         |
/// | `N+1`       | `item2` | `item1` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SwapN {
    item: u8,
}

impl SwapN {
    /// Constructs a new instance of the `SWAPN` opcode.
    ///
    /// # Errors
    ///
    /// If the provided `n` is not in the specified range.
    pub fn new(n: u8) -> anyhow::Result<Self> {
        if 0 < n && n <= 16 {
            Ok(Self { item: n })
        } else {
            let err = OpcodeError::InvalidStackItem {
                item: n,
                name: "SWAP".into(),
            };
            Err(err.into())
        }
    }

    /// Gets the item on the stack that this opcode is swapping with.
    pub fn n(&self) -> u8 {
        self.item
    }
}

impl Opcode for SwapN {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        self.item as usize + 1
    }

    fn as_text_code(&self) -> String {
        format!("SWAP{}", self.item)
    }

    fn as_byte(&self) -> u8 {
        SWAP_OPCODE_BASE_VALUE + self.item
    }
}
