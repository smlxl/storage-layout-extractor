//! This module contains the [`Opcode`] trait, and the concrete implementation
//! of each of the EVM's [opcodes](https://ethereum.org/en/developers/docs/evm/opcodes/).

mod arithmetic;
mod control;
mod environment;
mod logic;
mod memory;

use std::{any::Any, fmt::Debug};

use crate::vm::{state::VMState, VM};

/// This trait forms the core of the `Opcode` representation. It provides the
/// basic set of operations that are required of all opcodes, and is implemented
/// by each of the concrete opcodes.
///
/// # Object Safety and Enum Completeness
///
/// This trait must remain
/// [object safe](https://doc.rust-lang.org/reference/items/traits.html#object-safety)
/// as the implementors of the trait will be used in dynamic dispatch.
///
/// However, the intention is also to be able to wrap subsets of the `Opcode`s
/// into enums during the analysis phase.
///
/// # Self Bounds
///
/// The bounds on `Self` are required by these traits for the following reasons:
///
/// - [`Any`] allows downcasting to concrete implementations of `Opcode` if
///   needed.
/// - [`Clone`] and [`Copy`] to allow for cloning and copying. It is recommended
///   to use the derive feature for these.
/// - [`Debug`] to provide representations to aid in debugging. It is
///   recommended to use the derive feature for this.
///
/// # Terminology
///
/// When referring to stack slots, we treat index 1 as being the top of the
/// stack.
pub trait Opcode
where
    Self: Any + Clone + Copy + Debug,
{
    /// Executes the opcode, modifying the state of the [`VM`] appropriately.
    ///
    /// # Errors
    ///
    /// If the state of the virtual machine does not allow execution of the
    /// Opcode, or if execution would yield an invalid state in the virtual
    /// machine.
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()>;

    /// Gets the cost of the opcode in gas.
    ///
    /// The vast majority of opcodes have a state-independent gas cost, but some
    /// have cost that depends on their arguments. To that end, the [`VMState`]
    /// for which the calculation is requested is passed to allow the inspection
    /// of the opcode's arguments on the stack.
    ///
    /// # Errors
    ///
    /// If the state of the virtual machine does not allow execution of the
    /// Opcode, or if execution would yield an invalid state in the virtual
    /// machine.
    fn gas_cost(&self, state: &VMState) -> anyhow::Result<usize>;

    /// Gets the number of arguments that the opcode accepts from the virtual
    /// machine's stack.
    fn arg_count(&self) -> usize;

    /// Gets a textual representation of the opcode to aid in debugging.
    fn as_text_code(&self) -> String;

    /// Gets the byte representation of the opcode.
    fn as_byte(&self) -> u8;
}

/// A type for an [`Opcode`] that is dynamically dispatched.
pub type DynOpcode = Box<dyn Opcode>;
