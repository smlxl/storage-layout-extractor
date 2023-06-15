//! This module contains the state tracking functionality for the analyzer.

use std::fmt::Debug;

use crate::{
    unifier::Unifier,
    vm::{instructions::InstructionStream, ExecutionResult, VM},
    StorageLayout,
};

/// A marker trait that says that the type implementing it is an analyzer state.
pub trait State
where
    Self: Debug + Sized,
{
}

/// The initial state for the analyzer.
#[derive(Debug)]
pub struct HasContract;
impl State for HasContract {}

/// The analyzer has successfully disassembled the bytecode.
#[derive(Debug)]
pub struct DisassemblyComplete {
    /// The disassembled bytecode for the contract being analyzed.
    pub bytecode: InstructionStream,
}
impl State for DisassemblyComplete {}

/// The analyzer has prepared the virtual machine to symbolically execute the
/// contract's bytecode.
#[derive(Debug)]
pub struct VMReady {
    pub vm: VM,
}
impl State for VMReady {}

#[derive(Debug)]
pub struct ExecutionComplete {
    /// The results from executing the bytecode.
    pub execution_result: ExecutionResult,
}
impl State for ExecutionComplete {}

/// The analyzer has prepared the unifier to perform its processes.
#[derive(Debug)]
pub struct UnifierReady {
    pub unifier: Unifier,
}
impl State for UnifierReady {}

/// The analyzer has completed its unification and inference process, and is now
/// ready to provide the concrete storage layout.
#[derive(Debug)]
pub struct UnificationComplete {
    pub layout: StorageLayout,
}
impl State for UnificationComplete {}
