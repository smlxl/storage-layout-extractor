//! Opcodes that perform control(-flow) operations on the EVM.

#![allow(dead_code)] // Temporary allow to suppress valid warnings for now.

use crate::{opcode::Opcode, vm::VM};

/// The `STOP` opcode halts execution on the EVM, exiting the current call
/// context.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Stop;

impl Opcode for Stop {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!();
    }

    fn min_gas_cost(&self) -> usize {
        0
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "STOP".into()
    }

    fn as_byte(&self) -> u8 {
        0x00
    }
}

/// The `INVALID` opcode is invalid and instantly reverts execution.
///
/// Equivalent to [`Revert`] with 0 and 0 as its stack parameters.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Invalid;

impl Opcode for Invalid {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        0
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "INVALID".into()
    }

    fn as_byte(&self) -> u8 {
        0xfe
    }
}

/// The `JUMP` opcode alters the program counter to a new offset in the code.
///
/// The destination `counter` must be a [`JumpDest`] instruction.
///
/// # Semantics
///
/// | Stack Index | Input     | Output           |
/// | :---------: | :-------: | :--------------: |
/// | 1           | `counter` | `$pc := counter` |
///
/// where:
///
/// - `$pc` is the program counter
/// - `counter` is the new value for the program counter
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
///
/// Execution is reverted if the target instruction is not `JUMPDEST`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Jump;

impl Opcode for Jump {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        8
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "JUMP".into()
    }

    fn as_byte(&self) -> u8 {
        0x56
    }
}

/// The `JUMPI` opcode conditionally alters the program counter based on the
/// value of a boolean `b`.
///
/// The destination `c` must be a [`JumpDest`] instruction.
///
/// # Semantics
///
/// | Stack Index | Input     | Output                                        |
/// | :---------: | :-------: | :-------------------------------------------: |
/// | 1           | `counter` | `if cond then $pc := counter else $pc := $pc` |
/// | 2           | `cond`    |                                               |
///
/// where:
///
/// - `$pc` is the program counter
/// - `counter` is the new value for the program counter
/// - `cond` is the boolean value to check before executing the jump.
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
///
/// Execution is reverted if the target instruction is not `JUMPDEST`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct JumpI;

impl Opcode for JumpI {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        10
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "JUMPI".into()
    }

    fn as_byte(&self) -> u8 {
        0x57
    }
}

/// The `PC` opcode gets the value of the program counter _prior_ to the
/// increment corresponding to this instruction.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | $pc - 1 |
///
/// where:
///
/// - `$pc` is the value of the program counter
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct PC;

impl Opcode for PC {
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
        "PC".into()
    }

    fn as_byte(&self) -> u8 {
        0x58
    }
}

/// The `JUMPDEST` opcode marks a valid destination for a jump.
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct JumpDest;

impl Opcode for JumpDest {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        1
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "JUMPDEST".into()
    }

    fn as_byte(&self) -> u8 {
        0x5b
    }
}

/// The `CALL` opcode performs a message call into an account.
///
/// # Semantics
///
/// | Stack Index | Input       | Output                             |
/// | :---------: | :---------: | :--------------------------------: |
/// | 1           | `gas`       | `if call_did_revert then 0 else 1` |
/// | 2           | `addr`      |                                    |
/// | 3           | `value`     |                                    |
/// | 4           | `argOffset` |                                    |
/// | 5           | `argSize`   |                                    |
/// | 6           | `retOffset` |                                    |
/// | 7           | `retSize`   |                                    |
///
/// where:
///
/// - `gas` is the amount of gas sent to the sub-context for execution
/// - `address` is the account with the context to execute
/// - `value` is the value in WEI to send to `address`
/// - `argOffset` is the byte offset in the memory where the calldata can be
///   found
/// - `argSize` is the number of bytes in memory from `argOffset` to the end of
///   the calldata
/// - `retOffset` the byte offset in memory where the return data from the sub
///   context can be found
/// - `retSize` the number of bytes to copy for the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Call;

impl Opcode for Call {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        7
    }

    fn as_text_code(&self) -> String {
        "CALL".into()
    }

    fn as_byte(&self) -> u8 {
        0xf1
    }
}

/// The `CALLCODE` opcode performs a message call into the current account with
/// another account's code.
///
/// # Note
///
/// This opcode is deprecated and almost never used.
///
/// # Semantics
///
/// | Stack Index | Input       | Output                             |
/// | :---------: | :---------: | :--------------------------------: |
/// | 1           | `gas`       | `if call_did_revert then 0 else 1` |
/// | 2           | `addr`      |                                    |
/// | 3           | `value`     |                                    |
/// | 4           | `argOffset` |                                    |
/// | 5           | `argSize`   |                                    |
/// | 6           | `retOffset` |                                    |
/// | 7           | `retSize`   |                                    |
///
/// where:
///
/// - `gas` is the amount of gas sent to the sub-context for execution
/// - `address` is the account with the code to execute
/// - `value` is the value in WEI to send to `address`
/// - `argOffset` is the byte offset in the memory where the calldata can be
///   found
/// - `argSize` is the number of bytes in memory from `argOffset` to the end of
///   the calldata
/// - `retOffset` the byte offset in memory where the return data from the sub
///   context can be found
/// - `retSize` the number of bytes to copy for the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallCode;

impl Opcode for CallCode {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        7
    }

    fn as_text_code(&self) -> String {
        "CALLCODE".into()
    }

    fn as_byte(&self) -> u8 {
        0xf2
    }
}

/// The `DELEGATECALL` opcode performs a call using code from another account
/// while reusing the storage, sender, and value of the current account.
///
/// # Semantics
///
/// | Stack Index | Input       | Output                             |
/// | :---------: | :---------: | :--------------------------------: |
/// | 1           | `gas`       | `if call_did_revert then 0 else 1` |
/// | 2           | `addr`      |                                    |
/// | 3           | `value`     |                                    |
/// | 4           | `argOffset` |                                    |
/// | 5           | `argSize`   |                                    |
/// | 6           | `retOffset` |                                    |
/// | 7           | `retSize`   |                                    |
///
/// where:
///
/// - `gas` is the amount of gas sent to the sub-context for execution
/// - `address` is the account with the code to execute
/// - `value` is the value in WEI to send to `address`
/// - `argOffset` is the byte offset in the memory where the calldata can be
///   found
/// - `argSize` is the number of bytes in memory from `argOffset` to the end of
///   the calldata
/// - `retOffset` the byte offset in memory where the return data from the sub
///   context can be found
/// - `retSize` the number of bytes to copy for the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct DelegateCall;

impl Opcode for DelegateCall {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        7
    }

    fn as_text_code(&self) -> String {
        "DELEGATECALL".into()
    }

    fn as_byte(&self) -> u8 {
        0xf4
    }
}

/// The `STATICCALL` opcode performs a call using code from another account
/// while disallowing modification of state in the sub-context.
///
/// In particular, it disallows use of the following opcodes:
///
/// - [`crate::opcode::environment::Create`]
/// - [`crate::opcode::environment::Create2`]
/// - [`crate::opcode::environment::LogN`]
/// - [`crate::opcode::memory::SStore`]
/// - [`crate::opcode::environment::SelfDestruct`]
/// - [`Call`] if the `value` sent is not 0
///
/// # Semantics
///
/// | Stack Index | Input       | Output                             |
/// | :---------: | :---------: | :--------------------------------: |
/// | 1           | `gas`       | `if call_did_revert then 0 else 1` |
/// | 2           | `addr`      |                                    |
/// | 3           | `value`     |                                    |
/// | 4           | `argOffset` |                                    |
/// | 5           | `argSize`   |                                    |
/// | 6           | `retOffset` |                                    |
/// | 7           | `retSize`   |                                    |
///
/// where:
///
/// - `gas` is the amount of gas sent to the sub-context for execution
/// - `address` is the account with the context to execute
/// - `value` is the value in WEI to send to `address`
/// - `argOffset` is the byte offset in the memory where the calldata can be
///   found
/// - `argSize` is the number of bytes in memory from `argOffset` to the end of
///   the calldata
/// - `retOffset` the byte offset in memory where the return data from the sub
///   context can be found
/// - `retSize` the number of bytes to copy for the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct StaticCall;

impl Opcode for StaticCall {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        7
    }

    fn as_text_code(&self) -> String {
        "STATICCALL".into()
    }

    fn as_byte(&self) -> u8 {
        0xfa
    }
}

/// The `RETURN` opcode halts execution and returns the provided data of `size`
/// at `offset` in memory.
///
/// This opcode exits the current context with a success.
///
/// # Semantics
///
/// | Stack Index | Input    | Output |
/// | :---------: | :------: | :----: |
/// | 1           | `offset` |        |
/// | 2           | `size`   |        |
///
/// where:
///
/// - `offset` is the byte offset in memory where the return data is located
/// - `size` the number of bytes in the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Return;

impl Opcode for Return {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        0
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "RETURN".into()
    }

    fn as_byte(&self) -> u8 {
        0xf3
    }
}

/// The `REVERT` opcode halts execution returning data specified at the `offset`
/// and `size` in memory. It reverts any state changes and returns any unused
/// gas.
///
/// This opcode exits the current context with a success.
///
/// # Semantics
///
/// | Stack Index | Input    | Output |
/// | :---------: | :------: | :----: |
/// | 1           | `offset` |        |
/// | 2           | `size`   |        |
///
/// where:
///
/// - `offset` is the byte offset in memory where the return data is located
/// - `size` the number of bytes in the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Revert;

impl Opcode for Revert {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        0
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "REVERT".into()
    }

    fn as_byte(&self) -> u8 {
        0xfd
    }
}

/// Not a true EVM opcode, this structure exists to help in maintaining the
/// correspondence between position in the instruction stream and the byte
/// offset in the bytecode.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Nop;

impl Opcode for Nop {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        0
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "NOP".into()
    }

    fn as_byte(&self) -> u8 {
        panic!("NOP cannot be converted into a byte")
    }

    fn encode(&self) -> Vec<u8> {
        vec![] // This operation takes up no space in the instruction stream.
    }
}
