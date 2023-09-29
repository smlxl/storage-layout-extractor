//! This module contains the [`Opcode`] trait, and the concrete implementation
//! of each of the EVM's [opcodes](https://ethereum.org/en/developers/docs/evm/opcodes/).

pub mod arithmetic;
pub mod control;
pub mod environment;
pub mod logic;
mod macros;
pub mod memory;
mod util;

use std::{any::Any, fmt::Debug, rc::Rc};

use downcast_rs::Downcast;

use crate::{error::execution::Result, vm::VM};

/// This trait forms the core of the `Opcode` representation. It provides the
/// basic set of operations that are required of all opcodes, and is implemented
/// by each of the concrete opcodes.
///
/// # Object Safety
///
/// This trait must remain
/// [object safe](https://doc.rust-lang.org/reference/items/traits.html#object-safety)
/// as the implementors of the trait will be used in dynamic dispatch.
///
/// # Self Bounds
///
/// The bounds on `Self` are required by these traits for the following reasons:
///
/// - [`Any`] allows downcasting to concrete implementations of `Opcode` if
///   needed.
/// - [`Debug`] to provide representations to aid in debugging. It is
///   recommended to use the derive feature for this.
/// - [`Downcast`] for easy conversions _to_ [`Any`] for downcasting.
///
/// In addition, it is recommended but not enforced that implementors of this
/// trait also implement [`Copy`], [`Clone`], [`Eq`] and [`PartialEq`].
///
/// # Terminology
///
/// When referring to stack slots, we treat index 1 as being the top of the
/// stack.
pub trait Opcode
where
    Self: Any + Debug + Downcast,
{
    /// Executes the opcode described by `self`, modifying the state of the `vm`
    /// as necessary.
    ///
    /// It should not modify the instruction position in the general case, as
    /// this is handled outside the evaluation of the individual opcodes.
    /// Similarly, it should not manipulate the gas tracking in the general
    /// case, as this is handled by the VM itself.
    ///
    /// # Errors
    ///
    /// If the state of the virtual machine does not allow execution of the
    /// Opcode, or if execution would yield an invalid state in the virtual
    /// machine.
    fn execute(&self, vm: &mut VM) -> ExecuteResult;

    /// Gets the minimum cost of the opcode in gas.
    ///
    /// The vast majority of opcodes have a state-independent gas cost, but some
    /// have cost that depends on their arguments. During symbolic execution,
    /// however, there is no access to the true values of variables. To this
    /// end, the gas estimator just uses the smallest possible cost of the
    /// operation, thereby allowing execution to proceed as far as possible.
    fn min_gas_cost(&self) -> usize;

    /// Gets the number of arguments that the opcode accepts from the virtual
    /// machine's stack.
    fn arg_count(&self) -> usize;

    /// Gets a textual representation of the opcode to aid in debugging.
    fn as_text_code(&self) -> String;

    /// Gets the byte representation of the opcode.
    fn as_byte(&self) -> u8;

    /// Encodes the instruction as a sequence of bytes.
    ///
    /// # Note
    /// The default implementation delegates to [`Opcode::as_byte`], as this is
    /// the correct encoding for the vast majority of the opcodes.
    fn encode(&self) -> Vec<u8> {
        vec![self.as_byte()]
    }
}

/// A type for an [`Opcode`] that is dynamically dispatched.
pub type DynOpcode = Rc<dyn Opcode>;

/// The result of the [`Opcode::execute`] methods.
pub type ExecuteResult = Result<()>;

#[cfg(test)]
mod test_util {
    use crate::{
        disassembly::InstructionStream,
        vm::{value::RuntimeBoxedVal, Config, VM},
        watchdog::LazyWatchdog,
    };

    /// Constructs a new virtual machine with the provided `values` pushed
    /// onto its stack in order.
    ///
    /// This means that the last item in `values` will be put on the top of
    /// the stack.
    pub fn new_vm_with_values_on_stack(values: Vec<RuntimeBoxedVal>) -> anyhow::Result<VM> {
        // We don't actually care what these are for this test, so we just have
        // _something_ long enough to account for what is going on.
        let bytes: Vec<u8> = vec![
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x10, 0x11,
        ];

        let instructions = InstructionStream::try_from(bytes.as_slice())?;
        new_vm_with_instructions_and_values_on_stack(instructions, values)
    }

    /// Constructs a new virtual machine with the provided `instructions` and
    /// with the provided `values` pushed onto its stack in order.
    ///
    /// This means that the last item in `values` will be put on the top of
    /// the stack.
    pub fn new_vm_with_instructions_and_values_on_stack(
        instructions: InstructionStream,
        values: Vec<RuntimeBoxedVal>,
    ) -> anyhow::Result<VM> {
        let config = Config::default();

        let mut vm = VM::new(instructions, config, LazyWatchdog.in_rc())?;
        let stack = vm.state()?.stack_mut();

        let values_len = values.len();
        for val in values {
            stack.push(val).expect("Failed to insert value into stack");
        }

        // Check that we have constructed the stack correctly
        assert_eq!(stack.depth(), values_len);

        Ok(vm)
    }
}
