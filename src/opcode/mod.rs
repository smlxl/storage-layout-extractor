//! This module contains the [`Opcode`] trait, and the concrete implementation
//! of each of the EVM's [opcodes](https://ethereum.org/en/developers/docs/evm/opcodes/).

pub mod arithmetic;
pub mod control;
pub mod environment;
pub mod logic;
pub mod memory;

use std::{any::Any, fmt::Debug};

use downcast_rs::Downcast;

use crate::vm::VM;

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
    /// Executes the opcode, modifying the state of the [`VM`] appropriately.
    ///
    /// # Errors
    ///
    /// If the state of the virtual machine does not allow execution of the
    /// Opcode, or if execution would yield an invalid state in the virtual
    /// machine.
    fn execute(&self, vm: &mut VM) -> anyhow::Result<()>;

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
pub type DynOpcode = Box<dyn Opcode>;
