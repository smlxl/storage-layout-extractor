//! Opcodes that perform operations on memory or stack on the EVM.

#![allow(dead_code)] // Temporary allow to suppress valid warnings for now.

use anyhow::anyhow;

use crate::{opcode::Opcode, vm::VM};

/// The `CALLDATALOAD` opcode gets the input data for the current environment.
///
/// # Semantics
///
/// | Stack Index | Input | Output             |
/// | :---------: | :---: | :----------------: |
/// | 1           | i     | msg.data\[i:i+32\] |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallDataLoad;

impl Opcode for CallDataLoad {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | Stack Index | Input | Output        |
/// | :---------: | :---: | :-----------: |
/// | 1           |       | len(msg.data) |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallDataSize;

impl Opcode for CallDataSize {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// It has no output, but performs the following operation:
///
/// ```text
/// mem[d:d+s] := msg.data[o:o+s]
/// ```
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | d     |        |
/// | 2           | o     |        |
/// | 3           | s     |        |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallDataCopy;

impl Opcode for CallDataCopy {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | Stack Index | Input | Output         |
/// | :---------: | :---: | :------------: |
/// | 1           |       | len(this.code) |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CodeSize;

impl Opcode for CodeSize {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// It has no output, but performs the following operation:
///
/// ```text
/// mem[d:d+s] := this.code[o:o+s]
/// ```
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | d     |        |
/// | 2           | o     |        |
/// | 3           | s     |        |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CodeCopy;

impl Opcode for CodeCopy {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | Stack Index | Input | Output      |
/// | :---------: | :---: | :---------: |
/// | 1           | a     | len(a.code) |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ExtCodeSize;

impl Opcode for ExtCodeSize {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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

/// The `EXTCODECOPY` opcode performs a greater-than comparison.
///
/// # Semantics
///
/// | Stack Index | Input | Output                             |
/// | :---------: | :---: | :--------------------------------: |
/// | 1           | a     | mem\[d:d+s\] := addr.code\[o:o+s\] |
/// | 2           | d     |                                    |
/// | 3           | o     |                                    |
/// | 4           | s     |                                    |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ExtCodeCopy;

impl Opcode for ExtCodeCopy {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// previous call.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | size   |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ReturnDataSize;

impl Opcode for ReturnDataSize {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | Stack Index | Input | Output                              |
/// | :---------: | :---: | :---------------------------------: |
/// | 1           | d     | mem\[d:d+s\] := returndata\[o:o+s\] |
/// | 2           | o     |                                     |
/// | 2           | s     |                                     |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ReturnDataCopy;

impl Opcode for ReturnDataCopy {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | 1           | i     |        |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Pop;

impl Opcode for Pop {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | o     | mem\[o:o+32\] |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MLoad;

impl Opcode for MLoad {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | o     | mem\[o:o+32\] = v |
/// | 2           | v     |        |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MStore;

impl Opcode for MStore {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | o     | mem\[o:o+1\] = v |
/// | 2           | v     |        |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MStore8;

impl Opcode for MStore8 {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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

/// The `SLOAD` opcode loads a word from storage based on a 32-byte key `k`.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | k     | storage\[k\] |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SLoad;

impl Opcode for SLoad {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | k     | storage\[k\] := v |
/// | 2           | v     |        |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SStore;

impl Opcode for SStore {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | len(mem) |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MSize;

impl Opcode for MSize {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// | 1           |       | 0 |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Push0;

impl Opcode for Push0 {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
/// 32`. The item is initialized to all zeroes.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |      | stack\[1\] |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct PushN {
    bytes: u8,
}

impl PushN {
    /// Construct a new instance of the `PUSHN` opcode for some `n`.
    ///
    /// # Errors
    ///
    /// If `n` is not in the specified range.
    pub fn new(n: u8) -> anyhow::Result<Self> {
        if n > 0 && n <= 32 {
            Ok(Self { bytes: n })
        } else {
            Err(anyhow!("Invalid number of bytes for PUSH opcode: {n}"))
        }
    }

    /// Get the number of bytes this `PUSHN` opcode pushes onto the stack.
    pub fn bytes(&self) -> u8 {
        self.bytes
    }
}

impl Opcode for PushN {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        format!("PUSH{}", self.bytes)
    }

    fn as_byte(&self) -> u8 {
        const BASE_VALUE: u8 = 0x5f;
        BASE_VALUE + self.bytes
    }
}

/// The `DUPN` opcode duplicates the `N`th item on the stack, where `0 < N <=
/// 16`, pushing it on the top of the stack. This makes the duplicated item the
/// `N+1`th item.
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
            Err(anyhow!(
                "Invalid stack item provided for the DUP opcode: {n}"
            ))
        }
    }

    /// Gets the item on the stack that this opcode is duplicating.
    pub fn n(&self) -> u8 {
        self.item
    }
}

impl Opcode for Dup {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
        const BASE_VALUE: u8 = 0x7f;
        BASE_VALUE + self.item
    }
}

/// The `SWAPN` opcode exchanges the first and `N+1`th stack items, where `0 < N
/// <= 16`.
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
            Err(anyhow!(
                "Invalid stack item provided for the SWAP opcode: {n}"
            ))
        }
    }

    /// Gets the item on the stack that this opcode is swapping with.
    pub fn n(&self) -> u8 {
        self.item
    }
}

impl Opcode for SwapN {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
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
        const BASE_VALUE: u8 = 0x8f;
        BASE_VALUE + self.item
    }
}
