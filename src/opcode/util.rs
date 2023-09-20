//! This file contains utilities for implementing the symbolic executable
//! semantics of the opcodes.

use crate::{
    error::{container::Locatable, execution},
    opcode::control::JumpDest,
    vm::{
        value::{RuntimeBoxedVal, RSVD},
        VM,
    },
};

/// Validates that the provided `counter` represents a valid jump destination in
/// the provided `vm`.
///
/// Validating the destination may cause the execution of the current thread in
/// the VM to be halted.
///
/// # Errors
///
/// This returns [`Err`] in the following situations:
///
/// - When the provided `counter` is not a valid, known, immediate.
/// - When the jump target destination is not in bounds in the instruction
///   stream.
/// - When the jump target is not a valid [`JumpDest`] instruction.
///
/// It is assumed that all errors returned by this function are instances of
/// [`crate::error::execution::Error`].
#[allow(clippy::boxed_local)] // We always pass around boxed values during execution
pub fn validate_jump_destination(counter: &RuntimeBoxedVal, vm: &mut VM) -> execution::Result<u32> {
    let instruction_pointer = vm.instruction_pointer()?;
    let jump_target = match counter.constant_fold().data() {
        RSVD::KnownData { value, .. } => value.value_le().as_u32(),
        _ => {
            return Err(execution::Error::NoConcreteJumpDestination.locate(instruction_pointer));
        }
    };

    // We need to check that the jump target is valid.
    let thread = vm.execution_thread_mut()?;
    let target_instruction = thread.instruction(jump_target).ok_or(
        execution::Error::NonExistentJumpTarget {
            offset: jump_target,
        }
        .locate(instruction_pointer),
    )?;

    if !target_instruction.as_ref().as_any().is::<JumpDest>() {
        return Err(execution::Error::InvalidJumpTarget {
            offset: jump_target,
        }
        .locate(instruction_pointer));
    }

    Ok(jump_target)
}
