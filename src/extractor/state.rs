//! This module contains the state tracking functionality for the extractor.

use std::fmt::Debug;

use crate::{
    disassembly::InstructionStream,
    tc,
    tc::TypeChecker,
    vm,
    vm::{ExecutionResult, VM},
    watchdog::DynWatchdog,
    StorageLayout,
};

/// A marker trait that says that the type implementing it is an extractor
/// state.
///
/// Analyzer states can be transitioned between as part of the
/// [`crate::extractor::Extractor`] state machine, and are intended to enforce
/// that correct state transitions take place.
pub trait State
where
    Self: Debug + Sized,
{
}

/// The initial state for the extractor.
#[derive(Debug)]
pub struct HasContract {
    /// The virtual machine configuration.
    pub vm_config: vm::Config,

    /// The unifier configuration.
    pub tc_config: tc::Config,

    /// The watchdog that is monitoring the progress of the extractor.
    pub watchdog: DynWatchdog,
}
impl State for HasContract {}

/// The state for an extractor that has successfully disassembled the bytecode.
#[derive(Debug)]
pub struct DisassemblyComplete {
    /// The disassembled bytecode for the contract being analyzed.
    pub bytecode: InstructionStream,

    /// The configuration for the extractor's virtual machine.
    pub vm_config: vm::Config,

    /// The configuration for the extractor's type checker.
    pub tc_config: tc::Config,

    /// The watchdog that is monitoring the progress of the extractor.
    pub watchdog: DynWatchdog,
}
impl State for DisassemblyComplete {}

/// The extractor has prepared the virtual machine to symbolically execute the
/// contract's bytecode.
#[derive(Debug)]
pub struct VMReady {
    /// The virtual machine, prepared with the input contract and ready to
    /// execute.
    pub vm: VM,

    /// The configuration for the extractor's type checker.
    pub tc_config: tc::Config,

    /// The watchdog that is monitoring the progress of the extractor.
    pub watchdog: DynWatchdog,
}
impl State for VMReady {}

#[derive(Debug)]
pub struct ExecutionComplete {
    /// The result from executing the bytecode.
    pub execution_result: ExecutionResult,

    /// The configuration for the extractor's type checker.
    pub tc_config: tc::Config,

    /// The watchdog that is monitoring the progress of the extractor.
    pub watchdog: DynWatchdog,
}
impl State for ExecutionComplete {}

/// The extractor has prepared the type checker engine to perform its processes.
#[derive(Debug)]
pub struct InferenceReady {
    /// The type checker engine, ready to perform inference and unification.
    pub engine: TypeChecker,

    /// The watchdog that is monitoring the progress of the extractor.
    pub watchdog: DynWatchdog,

    /// The result of executing the virtual machine on the config.
    pub execution_result: ExecutionResult,
}
impl State for InferenceReady {}

/// The extractor has completed its inference and unification process, and is
/// now ready to provide the concrete storage layout.
#[derive(Debug)]
pub struct InferenceComplete {
    /// The type checker after it has performed inference and unification.
    pub engine: TypeChecker,

    /// The computed storage layout.
    pub layout: StorageLayout,
}
impl State for InferenceComplete {}
