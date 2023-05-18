//! Opcodes that perform arithmetic operations on the EVM.

#![allow(unused_variables)] // Temporary allow to suppress valid warnings for now.

use crate::{opcode::Opcode, vm::VM};

/// The `ADD` opcode performs addition.
///
/// # Semantics
///
/// | Stack Index | Input | Output             |
/// | :---------: | :---: | :----------------: |
/// | 1           | `a`   | `(a + b) % 2**256` |
/// | 2           | `b`   |                    |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Add;

impl Opcode for Add {
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
        "ADD".into()
    }

    fn as_byte(&self) -> u8 {
        0x01
    }
}

/// The `MUL` opcode performs multiplication.
///
/// # Semantics
///
/// | Stack Index | Input | Output             |
/// | :---------: | :---: | :----------------: |
/// | 1           | `a`   | `(a * b) % 2**256` |
/// | 2           | `b`   |                    |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Mul;

impl Opcode for Mul {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "MUL".into()
    }

    fn as_byte(&self) -> u8 {
        0x02
    }
}

/// The `SUB` opcode performs subtraction.
///
/// # Semantics
///
/// | Stack Index | Input | Output             |
/// | :---------: | :---: | :----------------: |
/// | 1           | `a`   | `(a - b) % 2**256` |
/// | 2           | `b`   |                    |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Sub;

impl Opcode for Sub {
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
        "SUB".into()
    }

    fn as_byte(&self) -> u8 {
        0x03
    }
}

/// The `DIV` opcode performs integer division.
///
/// # Semantics
///
/// | Stack Index | Input | Output                           |
/// | :---------: | :---: | :------------------------------: |
/// | 1           | `a`   | `if b == 0 then 0 else (a // b)` |
/// | 2           | `b`   |                                  |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Div;

impl Opcode for Div {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "DIV".into()
    }

    fn as_byte(&self) -> u8 {
        0x04
    }
}

/// The `SDIV` opcode performs signed integer division.
///
/// Both operands and the result are treated as two's complement signed 256-bit
/// integers.
///
/// # Semantics
///
/// | Stack Index | Input | Output                           |
/// | :---------: | :---: | :------------------------------: |
/// | 1           | `a`   | `if b == 0 then 0 else (a // b)` |
/// | 2           | `b`   |                                  |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SDiv;

impl Opcode for SDiv {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "SDIV".into()
    }

    fn as_byte(&self) -> u8 {
        0x05
    }
}

/// The `MOD` opcode performs integer modulo.
///
/// # Semantics
///
/// | Stack Index | Input | Output                          |
/// | :---------: | :---: | :-----------------------------: |
/// | 1           | `a`   | `if b == 0 then 0 else (a % b)` |
/// | 2           | `b`   |                                 |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Mod;

impl Opcode for Mod {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "MOD".into()
    }

    fn as_byte(&self) -> u8 {
        0x06
    }
}

/// The `SMOD` opcode performs signed integer modulo.
///
/// Both operands and the result are treated as two's complement signed 256-bit
/// integers.
///
/// # Semantics
///
/// | Stack Index | Input | Output                          |
/// | :---------: | :---: | :-----------------------------: |
/// | 1           | `a`   | `if b == 0 then 0 else (a % b)` |
/// | 2           | `b`   |                                 |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SMod;

impl Opcode for SMod {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "SMOD".into()
    }

    fn as_byte(&self) -> u8 {
        0x07
    }
}

/// The `ADDMOD` opcode performs addition followed by modulo.
///
/// # Note
///
/// All intermediate values of this calculation **are not** computed modulo
/// 2**256.
///
/// # Semantics
///
/// | Stack Index | Input | Output                              |
/// | :---------: | :---: | :---------------------------------: |
/// | 1           | `a`   | `if N == 0 then 0 else (a + b) % N` |
/// | 2           | `b`   |                                     |
/// | 3           | `N`   |                                     |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct AddMod;

impl Opcode for AddMod {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        8
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "ADDMOD".into()
    }

    fn as_byte(&self) -> u8 {
        0x08
    }
}

/// The `MULMOD` opcode performs multiplication followed by modulo.
///
/// # Note
///
/// All intermediate values of this calculation **are not** computed modulo
/// 2**256.
///
/// # Semantics
///
/// | Stack Index | Input | Output                              |
/// | :---------: | :---: | :---------------------------------: |
/// | 1           | `a`   | `if N == 0 then 0 else (a * b) % N` |
/// | 2           | `b`   |                                     |
/// | 3           | `N`   |                                     |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MulMod;

impl Opcode for MulMod {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        8
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "MULMOD".into()
    }

    fn as_byte(&self) -> u8 {
        0x09
    }
}

/// The `EXP` opcode performs exponentiation.
///
/// # Semantics
///
/// | Stack Index | Input | Output              |
/// | :---------: | :---: | :-----------------: |
/// | 1           | `a`   | `(a ** b) % 2**256` |
/// | 2           | `b`   |                     |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Exp;

impl Opcode for Exp {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        10
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "EXP".into()
    }

    fn as_byte(&self) -> u8 {
        0x0a
    }
}

/// The `SIGNEXTEND` opcode extends the length of a two's complement signed
/// integer.
///
/// # Semantics
///
/// | Stack Index | Input | Output             |
/// | :---------: | :---: | :----------------: |
/// | 1           | `a`   | `SIGNEXTEND(a, x)` |
/// | 2           | `x`   |                    |
///
/// where:
/// - `x` is the integer value to sign extend
/// - `a` is the size in bytes - 1 of the integer to sign extend
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SignExtend;

impl Opcode for SignExtend {
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "SIGNEXTEND".into()
    }

    fn as_byte(&self) -> u8 {
        0x0b
    }
}
