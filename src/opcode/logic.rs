//! Opcodes that deal with performing boolean logic on the EVM.

#![allow(dead_code)] // Temporary allow to suppress valid warnings for now.

use crate::{opcode::Opcode, vm::VM};

/// The `LT` opcode performs a less-than comparison.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a < b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Lt;

impl Opcode for Lt {
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
        "LT".into()
    }

    fn as_byte(&self) -> u8 {
        0x10
    }
}

/// The `GT` opcode performs a greater-than comparison.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a > b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Gt;

impl Opcode for Gt {
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
        "GT".into()
    }

    fn as_byte(&self) -> u8 {
        0x11
    }
}

/// The `SLT` opcode performs a less-than comparison, treating both operands as
/// signed two's complement integers.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a < b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SLt;

impl Opcode for SLt {
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
        "SLT".into()
    }

    fn as_byte(&self) -> u8 {
        0x12
    }
}

/// The `SGT` opcode performs a greater-than comparison, treating both operands
/// as signed two's complement integers.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a > b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SGt;

impl Opcode for SGt {
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
        "SAR".into()
    }

    fn as_byte(&self) -> u8 {
        0x13
    }
}

/// The `EQ` opcode performs an equality comparison.
///
/// # Semantics
///
/// | Stack Index | Input | Output   |
/// | :---------: | :---: | :------: |
/// | 1           | `a`   | `a == b` |
/// | 2           | `b`   |          |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Eq;

impl Opcode for Eq {
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
        "EQ".into()
    }

    fn as_byte(&self) -> u8 {
        0x14
    }
}

/// The `ISZERO` opcode checks if its operand is zero.
///
/// # Semantics
///
/// | Stack Index | Input | Output   |
/// | :---------: | :---: | :------: |
/// | 1           | `a`   | `a == 0` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct IsZero;

impl Opcode for IsZero {
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
        "ISZERO".into()
    }

    fn as_byte(&self) -> u8 {
        0x15
    }
}

/// The `AND` opcode performs a bitwise conjunction of its operands.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a & b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct And;

impl Opcode for And {
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
        "AND".into()
    }

    fn as_byte(&self) -> u8 {
        0x16
    }
}

/// The `OR` opcode performs a bitwise disjunction of its operands.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a | b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Or;

impl Opcode for Or {
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
        "OR".into()
    }

    fn as_byte(&self) -> u8 {
        0x17
    }
}

/// The `XOR` opcode performs a bitwise exclusive disjunction of its operands
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a ^ b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Xor;

impl Opcode for Xor {
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
        "XOR".into()
    }

    fn as_byte(&self) -> u8 {
        0x18
    }
}

/// The `NOT` opcode performs a bitwise negation of its operand
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | `a`   | `~a`   |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Not;

impl Opcode for Not {
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
        "NOT".into()
    }

    fn as_byte(&self) -> u8 {
        0x19
    }
}

/// The `BYTE` opcode retrieves a single byte from a word.
///
/// # Semantics
///
/// | Stack Index | Input    | Output                                 |
/// | :---------: | :------: | :------------------------------------: |
/// | 1           | `offset` | `(value >> (248 - offset * 8)) & 0xFF` |
/// | 2           | `value`  |                                        |
///
/// where:
///
/// - `offset` is the byte offset in `value` to retrieve, starting from the most
///   significant byte
/// - `value` is the word-sized (32 byte) value
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Byte;

impl Opcode for Byte {
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
        "BYTE".into()
    }

    fn as_byte(&self) -> u8 {
        0x1a
    }
}

/// The `SHL` opcode performs a left shift (toward the MSB).
///
/// The bits moved after the 256th one are discarded, the new bits are set to 0.
///
/// # Semantics
///
/// | Stack Index | Input   | Output           |
/// | :---------: | :-----: | :--------------: |
/// | 1           | `shift` | `value << shift` |
/// | 2           | `value` |                  |
///
/// where:
///
/// - `shift` is the number of bits shifted to the left
/// - `value` the 32-byte value to shift
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Shl;

impl Opcode for Shl {
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
        "SHL".into()
    }

    fn as_byte(&self) -> u8 {
        0x1b
    }
}

/// The `SHR` opcode performs a right shift (toward the LSB).
///
/// The bits moved before the first one are discarded, the new bits are set to
/// 0.
///
/// # Semantics
///
/// | Stack Index | Input   | Output           |
/// | :---------: | :-----: | :--------------: |
/// | 1           | `shift` | `value >> shift` |
/// | 2           | `value` |                  |
///
/// where:
///
/// - `shift` is the number of bits shifted to the right
/// - `value` the 32-byte value to shift
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Shr;

impl Opcode for Shr {
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
        "SHR".into()
    }

    fn as_byte(&self) -> u8 {
        0x1c
    }
}

/// The `SAR` opcode performs a signed (arithmetic) right shift (toward the
/// LSB).
///
/// The bits moved before the first one are discarded, the new bits are set to 0
/// if the previous most significant bit was 0, otherwise the new bits are set
/// to 1.
///
/// # Semantics
///
/// | Stack Index | Input   | Output           |
/// | :---------: | :-----: | :--------------: |
/// | 1           | `shift` | `value >> shift` |
/// | 2           | `value` |                  |
///
/// where:
///
/// - `shift` is the number of bits shifted to the right
/// - `value` the 32-byte value to shift
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Sar;

impl Opcode for Sar {
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
        "SAR".into()
    }

    fn as_byte(&self) -> u8 {
        0x1d
    }
}
