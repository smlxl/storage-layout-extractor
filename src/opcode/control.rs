//! Opcodes that perform control(-flow) operations on the EVM.

use crate::{
    opcode::Opcode,
    vm::{state::VMState, VM},
};

/// The `STOP` opcode halts execution on the EVM, exiting the current call
/// context.
#[derive(Copy, Clone, Debug)]
pub struct Stop;

impl Opcode for Stop {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!();
    }

    fn gas_cost(&self, _state: &VMState) -> anyhow::Result<usize> {
        Ok(0)
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
