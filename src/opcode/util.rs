//! This file contains utilities for implementing the symbolic executable
//! semantics of the opcodes.

use std::mem;

use ethnum::U256;

use crate::{
    error::{container::Locatable, execution},
    opcode::control::JumpDest,
    vm::{
        value::{BoxedVal, SymbolicValueData},
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
/// [`VMError`].
#[allow(clippy::boxed_local)] // We always pass around boxed values during execution
pub fn validate_jump_destination(counter: &BoxedVal, vm: &mut VM) -> execution::Result<u32> {
    let instruction_pointer = vm.instruction_pointer()?;
    let jump_target = match &counter.clone().constant_fold().data {
        SymbolicValueData::KnownData { value, .. } => value.into(),
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

/// Provides a generic way to convert to an integral type from data contained in
/// the first `N` bytes of a byte buffer.
///
/// # Note
///
/// This trait could be greatly improved with the advent of the
/// [`generic_const_exprs`](https://github.com/rust-lang/rust/issues/76560)
/// feature, but that is not stable yet.
///
/// In particular, an associated const could be used, removing the need to
/// duplicate the const generic parameter in each implementation.
trait IntegerFromBytes<const N: usize>
where
    Self: Sized,
{
    /// Converts to the specified `Self` integral type by taking the first `N`
    /// items in `bytes`.
    ///
    /// Returns [`None`] if `bytes` does not contain >= `N` bytes.
    fn from_bytes<'a>(bytes: impl Into<&'a [u8]>) -> Option<Self> {
        let bytes = bytes.into();

        if bytes.len() < N {
            return None;
        }

        let mut buf: [u8; N] = [0; N];
        buf[..N].copy_from_slice(&bytes[..N]);

        Some(Self::from_le_bytes(buf))
    }

    /// Converts to the type from a fixed number of bytes.
    fn from_le_bytes(bytes: [u8; N]) -> Self;
}

impl IntegerFromBytes<{ mem::size_of::<u8>() }> for u8 {
    fn from_le_bytes(bytes: [u8; mem::size_of::<u8>()]) -> Self {
        u8::from_le_bytes(bytes)
    }
}

impl IntegerFromBytes<{ mem::size_of::<u16>() }> for u16 {
    fn from_le_bytes(bytes: [u8; mem::size_of::<u16>()]) -> Self {
        u16::from_le_bytes(bytes)
    }
}

impl IntegerFromBytes<{ mem::size_of::<u32>() }> for u32 {
    fn from_le_bytes(bytes: [u8; mem::size_of::<u32>()]) -> Self {
        u32::from_le_bytes(bytes)
    }
}

impl IntegerFromBytes<{ mem::size_of::<u64>() }> for u64 {
    fn from_le_bytes(bytes: [u8; mem::size_of::<u64>()]) -> Self {
        u64::from_le_bytes(bytes)
    }
}

impl IntegerFromBytes<{ mem::size_of::<u128>() }> for u128 {
    fn from_le_bytes(bytes: [u8; mem::size_of::<u128>()]) -> Self {
        u128::from_le_bytes(bytes)
    }
}

impl IntegerFromBytes<{ mem::size_of::<U256>() }> for U256 {
    fn from_le_bytes(bytes: [u8; mem::size_of::<U256>()]) -> Self {
        U256::from_le_bytes(bytes)
    }
}
