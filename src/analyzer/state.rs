//! This module contains the state tracking functionality for the analyzer.

use std::fmt::Debug;

use crate::vm::{instructions::InstructionStream, ExecutionResult, VM};

/// A marker trait that says that the type implementing it is an analyzer state.
pub trait State
where
    Self: Clone + Debug + Sized,
{
}

/// The initial state for the analyzer.
#[derive(Clone, Debug)]
pub struct HasContract;
impl State for HasContract {}

/// The analyzer has successfully disassembled the bytecode.
#[derive(Clone, Debug)]
pub struct DisassemblyComplete {
    /// The disassembled bytecode for the contract being analyzed.
    pub bytecode: InstructionStream,
}
impl State for DisassemblyComplete {}

/// The analyzer has prepared the virtual machine to symbolically execute the
/// contract's bytecode.
#[derive(Clone, Debug)]
pub struct VMReady {
    pub vm: VM,
}
impl State for VMReady {}

#[derive(Clone, Debug)]
pub struct ExecutionComplete {
    /// The results from executing the bytecode.
    pub execution_result: ExecutionResult,
}
impl State for ExecutionComplete {}
