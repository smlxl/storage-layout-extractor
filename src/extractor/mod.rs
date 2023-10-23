//! This module contains the definition of the extractor itself.

pub mod chain;
pub mod contract;
pub mod state;

use crate::{
    disassembly::InstructionStream,
    error,
    extractor::{contract::Contract, state::State},
    tc,
    tc::TypeChecker,
    vm,
    vm::VM,
    watchdog::DynWatchdog,
    StorageLayout,
};

/// Creates a new extractor wrapping the provided `contract`, and with the
/// provided `vm_config` and `unifier_config`.
#[must_use]
pub fn new(
    contract: Contract,
    vm_config: vm::Config,
    tc_config: tc::Config,
    watchdog: DynWatchdog,
) -> Extractor<state::HasContract> {
    let state = state::HasContract {
        vm_config,
        tc_config,
        watchdog,
    };
    Extractor { contract, state }
}

/// The core of the storage layout analysis, the `Extractor` is responsible for
/// ingesting user data and outputting a storage layout.
///
/// # Enforcing Valid State Transitions
///
/// The extractor enforces that only correct state transitions can occur through
/// use of structs that implement the exact state required by it at any given
/// point.
///
/// There is the [`Self::state`] function that provides access to the state data
/// of whichever state the extractor is currently in.
pub struct Extractor<S: State> {
    /// The contract that is being analyzed.
    contract: Contract,

    /// The internal state of the extractor.
    state: S,
}

/// The safe operations available in all states.
///
/// # Modifying the Extractor
///
/// If you feel the need to modify the extractor outside of the standard
/// transitions, perhaps as part of external extensions to the library, you
/// will need to use one of the following functions:
///
/// - [`Extractor::contract_mut`]
/// - [`Extractor::state_mut`]
/// - [`Extractor::set_contract`]
/// - [`Extractor::set_state`]
/// - [`Extractor::transform_state`]
///
/// All of these are unsafe as they allow violating the invariants of the
/// extractor's state. Be very careful and be sure that you know what you are
/// doing if you reach for these.
impl<S: State> Extractor<S> {
    /// Gets a reference to the contract being analyzed.
    pub fn contract(&self) -> &Contract {
        &self.contract
    }

    /// Gets an immutable reference to the current state of the extractor.
    pub fn state(&self) -> &S {
        &self.state
    }
}

/// Unsafe operations available in all states.
///
/// These operations are capable of **violating the state invariants** of the
/// extractor, and must be used with the _utmost_ care.
impl<S: State> Extractor<S> {
    /// Gets a mutable reference to the contract being analyzed.
    ///
    /// # Safety
    ///
    /// Do not mutate the contract instance unless you totally understand the
    /// state that the extractor is in, and the implications of doing so.
    pub unsafe fn contract_mut(&mut self) -> &mut Contract {
        &mut self.contract
    }

    /// Gets a mutable reference to the current state of the extractor.
    ///
    /// # Safety
    ///
    /// Do not mutate the state instance unless you totally understand the
    /// state that the extractor is in, and the implications of doing so.
    pub unsafe fn state_mut(&mut self) -> &mut S {
        &mut self.state
    }

    /// Sets the extractor's contract instance to `contract`.
    ///
    /// # Safety
    ///
    /// Do not change the contract instance used by the extractor unless you
    /// totally understand the state that the extractor is in, and the
    /// implications of doing so.
    pub unsafe fn set_contract(&mut self, contract: Contract) {
        self.contract = contract;
    }

    /// Forces the extractor into `new_state`, disregarding any safety with
    /// regards to state transitions.
    ///
    /// # Safety
    ///
    /// Do not force a state transition for the extractor unless you totally
    /// understand the state that the extractor is in, and the implications
    /// of doing so.
    pub unsafe fn set_state<NS: State>(self, new_state: NS) -> Extractor<NS> {
        Extractor {
            contract: self.contract,
            state:    new_state,
        }
    }

    /// Forces the extractor into the state `NS`, with the value of the state
    /// created by applying `transform` to the extractor's current state and
    /// disregarding any safety with regard to state transitions.
    ///
    /// # Safety
    ///
    /// Do not force a state transition for the extractor unless you totally
    /// understand the state that the extractor is in, and the implications
    /// of doing so.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the provided `transform` returns [`Err`].
    pub unsafe fn transform_state<NS: State>(
        self,
        transform: impl FnOnce(S) -> error::Result<NS>,
    ) -> error::Result<Extractor<NS>> {
        let state = transform(self.state)?;
        let contract = self.contract;

        Ok(Extractor { contract, state })
    }
}

/// A type that allows the user to easily name the initial state of the
/// extractor.
pub type InitialExtractor = Extractor<state::HasContract>;

/// Operations available on a newly-created extractor.
impl Extractor<state::HasContract> {
    /// Executes the analysis process for beginning to end, performing all the
    /// intermediate steps automatically and returning the storage layout.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if any step in the process fails.
    pub fn analyze(self) -> error::Result<StorageLayout> {
        let extractor = self.disassemble()?;
        let extractor = extractor.prepare_vm()?;
        let extractor = extractor.execute()?;
        let extractor = extractor.prepare_unifier();
        let extractor = extractor.infer()?;
        let layout = extractor.layout();

        Ok(layout.clone())
    }

    /// Performs the disassembly process to turn the input contract code into
    /// bytecode.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if disassembly fails.
    pub fn disassemble(self) -> error::Result<Extractor<state::DisassemblyComplete>> {
        let bytecode = InstructionStream::try_from(self.contract.bytecode().as_slice())?;
        unsafe {
            self.transform_state(|old_state| {
                let vm_config = old_state.vm_config;
                let tc_config = old_state.tc_config;
                let watchdog = old_state.watchdog;
                Ok(state::DisassemblyComplete {
                    bytecode,
                    vm_config,
                    tc_config,
                    watchdog,
                })
            })
        }
    }
}

/// Operations available on an extractor that has completed the disassembly of
/// the bytecode.
impl Extractor<state::DisassemblyComplete> {
    /// Prepares the virtual machine for symbolic execution of the bytecode.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the virtual machine cannot be constructed for some
    /// reason.
    pub fn prepare_vm(self) -> error::Result<Extractor<state::VMReady>> {
        unsafe {
            self.transform_state(|old_state| {
                let tc_config = old_state.tc_config;
                let watchdog = old_state.watchdog;
                let vm = VM::new(old_state.bytecode, old_state.vm_config, watchdog.clone())?;
                Ok(state::VMReady {
                    vm,
                    tc_config,
                    watchdog,
                })
            })
        }
    }
}

/// Operations available on an extractor that has a virtual machine ready to
/// execute the bytecode.
impl Extractor<state::VMReady> {
    /// Symbolically executes the disassembled bytecode on the [`VM`] to gather
    /// symbolic values that are built during execution.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if execution in the virtual machine fails for any
    /// reason.
    pub fn execute(self) -> error::Result<Extractor<state::ExecutionComplete>> {
        unsafe {
            self.transform_state(|mut old_state| {
                old_state.vm.execute()?;
                let execution_result = old_state.vm.consume();
                let tc_config = old_state.tc_config;
                let watchdog = old_state.watchdog;
                Ok(state::ExecutionComplete {
                    execution_result,
                    tc_config,
                    watchdog,
                })
            })
        }
    }
}

/// Operations available on an extractor that has a VM which has completed
/// execution of the bytecode.
impl Extractor<state::ExecutionComplete> {
    /// Takes thew results of execution and uses them to prepare a new tc
    /// engine.
    #[allow(clippy::missing_panics_doc)] // Explicit closure can never return Err
    #[must_use]
    pub fn prepare_unifier(self) -> Extractor<state::InferenceReady> {
        unsafe {
            // Safe to unwrap as we guarantee that the internal operations cannot fail.
            self.transform_state(|old_state| {
                let watchdog = old_state.watchdog;
                let execution_result = old_state.execution_result;
                let engine = TypeChecker::new(old_state.tc_config, watchdog.clone());
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

/// Operations available on an extractor that has a type checker ready to
/// perform the inference and unification processes.
impl Extractor<state::InferenceReady> {
    /// Takes the prepared type checker and runs the inference and unification
    /// process on the execution results.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the execution of the type checker fails.
    pub fn infer(self) -> error::Result<Extractor<state::InferenceComplete>> {
        unsafe {
            self.transform_state(|mut old_state| {
                let layout = old_state.engine.run(old_state.execution_result)?;
                let engine = old_state.engine;
                Ok(state::InferenceComplete { engine, layout })
            })
        }
    }
}

/// Operations available on an extractor that has completed unification.
impl Extractor<state::InferenceComplete> {
    /// Gets the type checking engine once it has completed inference and
    /// unification.
    #[must_use]
    pub fn engine(&self) -> &TypeChecker {
        &self.state.engine
    }

    /// Gets the computed storage layout for the contract.
    #[must_use]
    pub fn layout(&self) -> &StorageLayout {
        &self.state.layout
    }
}
