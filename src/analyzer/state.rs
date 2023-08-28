//! This module contains the state tracking functionality for the analyzer.

use std::fmt::Debug;

use crate::{
    disassembly::InstructionStream,
    inference,
    inference::InferenceEngine,
    vm,
    vm::{ExecutionResult, VM},
    watchdog::DynWatchdog,
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
pub struct HasContract {
    /// The virtual machine configuration.
    pub vm_config: vm::Config,

    /// The unifier configuration.
    pub unifier_config: inference::Config,

    /// The watchdog that is monitoring the progress of the analyzer.
    pub watchdog: DynWatchdog,
}
impl State for HasContract {}

/// The analyzer has successfully disassembled the bytecode.
#[derive(Debug)]
pub struct DisassemblyComplete {
    /// The disassembled bytecode for the contract being analyzed.
    pub bytecode: InstructionStream,

    /// The virtual machine configuration.
    pub vm_config: vm::Config,

    /// The unifier configuration.
    pub unifier_config: inference::Config,

    /// The watchdog that is monitoring the progress of the analyzer.
    pub watchdog: DynWatchdog,
}
impl State for DisassemblyComplete {}

/// The analyzer has prepared the virtual machine to symbolically execute the
/// contract's bytecode.
#[derive(Debug)]
pub struct VMReady {
    /// The prepared virtual machine.
    pub vm: VM,

    /// The unifier configuration.
    pub unifier_config: inference::Config,

    /// The watchdog that is monitoring the progress of the analyzer.
    pub watchdog: DynWatchdog,
}
impl State for VMReady {}

#[derive(Debug)]
pub struct ExecutionComplete {
    /// The results from executing the bytecode.
    pub execution_result: ExecutionResult,

    /// The unifier configuration.
    pub unifier_config: inference::Config,

    /// The watchdog that is monitoring the progress of the analyzer.
    pub watchdog: DynWatchdog,
}
impl State for ExecutionComplete {}

/// The analyzer has prepared the inference engine to perform its processes.
#[derive(Debug)]
pub struct InferenceReady {
    /// The inference engine, ready to perform inference and unification.
    pub engine: InferenceEngine,

    /// The watchdog that is monitoring the progress of the analyzer.
    pub watchdog: DynWatchdog,
}
impl State for InferenceReady {}

/// The analyzer has completed its inference and unification process, and is now
/// ready to provide the concrete storage layout.
#[derive(Debug)]
pub struct InferenceComplete {
    /// The engine after it has performed inference and unification.
    pub engine: InferenceEngine,

    /// The computed storage layout.
    pub layout: StorageLayout,
}
impl State for InferenceComplete {}
