//! This module deals with the implementation of the symbolic virtual machine.

pub mod instruction_stream;
pub mod state;
pub mod symbolic_value;

/// The virtual machine used to perform symbolic execution of the contract
/// bytecode.
#[derive(Debug)]
pub struct VM {}

// TODO [Ara] Tracking for visited opcodes.

// TODO [Ara] FIFO queue of branches, registered by their JUMPS. We only spawn
//   new branches if the source jump hasn't been bifurcated and enqueued before.

// TODO [Ara] `Path`, each containing an `ExecutionThread` and `VMState`

// TODO [Ara] `newPath` function.

// TODO [Ara] Precomputed keccaks for the early storage slots to help with
//   recognition of constants. With arrays.

// TODO [Ara] When a symbolic value is going to disappear it should be added to
//   the `VM`s buffer of them.
