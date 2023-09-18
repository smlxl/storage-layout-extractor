//! This module contains the definition of the analyzer itself.

pub mod chain;
pub mod contract;
pub mod state;

use crate::{
    analyzer::{contract::Contract, state::State},
    disassembly::InstructionStream,
    error,
    inference,
    inference::InferenceEngine,
    vm,
    vm::VM,
    watchdog::DynWatchdog,
    StorageLayout,
};

/// Creates a new analyzer wrapping the provided `contract`, and with the
/// provided `vm_config` and `unifier_config`.
#[must_use]
pub fn new(
    contract: Contract,
    vm_config: vm::Config,
    unifier_config: inference::Config,
    watchdog: DynWatchdog,
) -> Analyzer<state::HasContract> {
    let state = state::HasContract {
        vm_config,
        unifier_config,
        watchdog,
    };
    Analyzer { contract, state }
}

/// The core of the storage layout analysis, the `Analyzer` is responsible for
/// ingesting user data and outputting a storage layout.
///
/// # Enforcing Valid State Transitions
///
/// The analyzer enforces that only correct state transitions can occur through
/// use of structs that implement the exact state required by it at any given
/// point.
///
/// There is the [`Self::state`] function that provides access to the state data
/// of whichever state it is in.
pub struct Analyzer<S: State> {
    /// The contract that is being analyzed.
    contract: Contract,

    /// The internal state of the analyzer.
    state: S,
}

/// Safe operations available in all states.
impl<S: State> Analyzer<S> {
    /// Gets a reference to the contract being analyzed.
    pub fn contract(&self) -> &Contract {
        &self.contract
    }

    /// Gets a reference to the current state of the analyzer.
    pub fn state(&self) -> &S {
        &self.state
    }
}

/// Unsafe operations available in all states.
///
/// These operations are capable of **violating the state invariants** of the
/// analyzer, and must be used with the _utmost_ care.
impl<S: State> Analyzer<S> {
    /// Gets a mutable reference to the contract being analyzed.
    ///
    /// # Safety
    ///
    /// Do not mutate the contract instance unless you totally understand the
    /// state that the analyzer is in, and the implications of doing so.
    pub unsafe fn contract_mut(&mut self) -> &mut Contract {
        &mut self.contract
    }

    /// Gets a mutable reference to the current state of the analyzer.
    ///
    /// # Safety
    ///
    /// Do not mutate the state instance unless you totally understand the
    /// state that the analyzer is in, and the implications of doing so.
    pub unsafe fn state_mut(&mut self) -> &mut S {
        &mut self.state
    }

    /// Sets the analyzer's contract instance to `contract`.
    ///
    /// # Safety
    ///
    /// Do not change the contract instance used by the analyzer unless you
    /// totally understand the state that the analyzer is in, and the
    /// implications of doing so.
    pub unsafe fn set_contract(&mut self, contract: Contract) {
        self.contract = contract;
    }

    /// Forces the analyzer into `new_state`, disregarding any safety with
    /// regards to state transitions.
    ///
    /// # Safety
    ///
    /// Do not force a state transition for the analyzer unless you totally
    /// understand the state that the analyzer is in, and the implications
    /// of doing so.
    pub unsafe fn set_state<NS: State>(self, new_state: NS) -> Analyzer<NS> {
        Analyzer {
            contract: self.contract,
            state:    new_state,
        }
    }

    /// Forces the analyzer into the state `NS`, with the value of the state
    /// created by applying `transform` to the analyzer's current state and
    /// disregarding any safety with regard to state transitions.
    ///
    /// # Safety
    ///
    /// Do not force a state transition for the analyzer unless you totally
    /// understand the state that the analyzer is in, and the implications
    /// of doing so.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the provided `transform` returns [`Err`].
    pub unsafe fn transform_state<NS: State>(
        self,
        transform: impl FnOnce(S) -> error::Result<NS>,
    ) -> error::Result<Analyzer<NS>> {
        let state = transform(self.state)?;
        let contract = self.contract;

        Ok(Analyzer { contract, state })
    }
}

/// A type that allows the user to easily name the initial state of the
/// analyzer.
pub type InitialAnalyzer = Analyzer<state::HasContract>;

/// Operations available on a newly-created analyzer.
impl Analyzer<state::HasContract> {
    /// Executes the analysis process for beginning to end, performing all the
    /// intermediate steps automatically and returning the storage layout.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if any step in the process fails.
    pub fn analyze(self) -> error::Result<StorageLayout> {
        let analyzer = self.disassemble()?;
        let analyzer = analyzer.prepare_vm()?;
        let analyzer = analyzer.execute()?;
        let analyzer = analyzer.prepare_unifier();
        let analyzer = analyzer.infer()?;
        let layout = analyzer.layout();

        Ok(layout.clone())
    }

    /// Performs the disassembly process to turn the input contract code into
    /// bytecode.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if disassembly fails.
    pub fn disassemble(self) -> error::Result<Analyzer<state::DisassemblyComplete>> {
        let bytecode = InstructionStream::try_from(self.contract.bytecode().as_slice())?;
        unsafe {
            self.transform_state(|old_state| {
                let vm_config = old_state.vm_config;
                let unifier_config = old_state.unifier_config;
                let watchdog = old_state.watchdog;
                Ok(state::DisassemblyComplete {
                    bytecode,
                    vm_config,
                    unifier_config,
                    watchdog,
                })
            })
        }
    }
}

/// Operations available on an analyzer that has completed the disassembly of
/// the bytecode.
impl Analyzer<state::DisassemblyComplete> {
    /// Prepares the virtual machine for symbolic execution of the bytecode.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the virtual machine cannot be constructed for some
    /// reason.
    pub fn prepare_vm(self) -> error::Result<Analyzer<state::VMReady>> {
        unsafe {
            self.transform_state(|old_state| {
                let unifier_config = old_state.unifier_config;
                let watchdog = old_state.watchdog;
                let vm = VM::new(old_state.bytecode, old_state.vm_config, watchdog.clone())?;
                Ok(state::VMReady {
                    vm,
                    unifier_config,
                    watchdog,
                })
            })
        }
    }
}

/// Operations available on an analyzer that has a virtual machine ready to
/// execute the bytecode.
impl Analyzer<state::VMReady> {
    /// Symbolically executes the disassembled bytecode on the [`VM`] to gather
    /// symbolic values that are built during execution.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if execution in the virtual machine fails for any
    /// reason.
    pub fn execute(self) -> error::Result<Analyzer<state::ExecutionComplete>> {
        unsafe {
            self.transform_state(|mut old_state| {
                old_state.vm.execute()?;
                let execution_result = old_state.vm.consume();
                let unifier_config = old_state.unifier_config;
                let watchdog = old_state.watchdog;
                Ok(state::ExecutionComplete {
                    execution_result,
                    unifier_config,
                    watchdog,
                })
            })
        }
    }
}

/// Operations available on an analyzer that has a VM which has completed
/// execution of the bytecode.
impl Analyzer<state::ExecutionComplete> {
    /// Takes thew results of execution and uses them to prepare a new inference
    /// engine.
    #[allow(clippy::missing_panics_doc)] // Explicit closure can never return Err
    #[must_use]
    pub fn prepare_unifier(self) -> Analyzer<state::InferenceReady> {
        unsafe {
            // Safe to unwrap as we guarantee that the internal operations cannot fail.
            self.transform_state(|old_state| {
                let watchdog = old_state.watchdog;
                let execution_result = old_state.execution_result;
                let engine = InferenceEngine::new(old_state.unifier_config, watchdog.clone());
                Ok(state::InferenceReady {
                    engine,
                    watchdog,
                    execution_result,
                })
            })
            .expect("Explicit closure cannot return Err")
        }
    }
}

/// Operations available on an analyzer that has an inference engine ready to
/// perform the inference and unification processes.
impl Analyzer<state::InferenceReady> {
    /// Takes the prepared inference engine and runs the inference and
    /// unification process on the execution results.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the execution of the inference engine fails.
    pub fn infer(self) -> error::Result<Analyzer<state::InferenceComplete>> {
        unsafe {
            self.transform_state(|mut old_state| {
                let layout = old_state.engine.run(&old_state.execution_result)?;
                let engine = old_state.engine;
                Ok(state::InferenceComplete { engine, layout })
            })
        }
    }
}

/// Operations available on an analyzer that has completed unification.
impl Analyzer<state::InferenceComplete> {
    /// Gets the inference engine once it has completed inference and
    /// unification.
    #[must_use]
    pub fn engine(&self) -> &InferenceEngine {
        &self.state.engine
    }

    /// Gets the computed storage layout for the contract.
    #[must_use]
    pub fn layout(&self) -> &StorageLayout {
        &self.state.layout
    }
}
