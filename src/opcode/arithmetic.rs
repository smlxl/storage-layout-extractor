//! Opcodes that perform arithmetic operations on the EVM.

use crate::{
    opcode::Opcode,
    vm::{state::VMState, VM},
};

/// The `ADD` opcode performs integer addition.
///
/// # Semantics
///
/// | Stack Index | Input | Output          |
/// | :---------: | :---: | :-------------: |
/// | 1           | a     | (a + b) & 2^256 |
/// | 2           | b     |                 |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug)]
pub struct Add;

impl Opcode for Add {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn gas_cost(&self, _state: &VMState) -> anyhow::Result<usize> {
        Ok(3)
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
