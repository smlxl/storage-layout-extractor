//! This module contains the definition of the analyzer itself.

pub mod chain;
pub mod state;

use crate::{
    analyzer::state::State,
    contract::Contract,
    error,
    unifier,
    unifier::Unifier,
    vm,
    vm::{instructions::InstructionStream, VM},
    StorageLayout,
};

/// Creates a new analyzer wrapping the provided `contract`, and with the
/// provided `vm_config` and `unifier_config`.
pub fn new(
    contract: Contract,
    vm_config: vm::Config,
    unifier_config: unifier::Config,
) -> Analyzer<state::HasContract> {
    let state = state::HasContract {
        vm_config,
        unifier_config,
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
    pub unsafe fn transform_state<NS: State>(
        self,
        transform: impl FnOnce(S) -> error::Result<NS>,
    ) -> error::Result<Analyzer<NS>> {
        let state = transform(self.state)?;
        let contract = self.contract;

        Ok(Analyzer { state, contract })
    }
}

/// A type that allows the user to easily name the initial state of the
/// analyzer.
pub type InitialAnalyzer = Analyzer<state::HasContract>;

/// Operations available on a newly-created analyzer.
impl Analyzer<state::HasContract> {
    /// Executes the analysis process for beginning to end, performing all the
    /// intermediate steps automatically and returning the storage layout.
    pub fn analyze(self) -> error::Result<StorageLayout> {
        let analyzer = self.disassemble()?;
        let analyzer = analyzer.prepare_vm()?;
        let analyzer = analyzer.execute()?;
        let analyzer = analyzer.prepare_unifier()?;
        let analyzer = analyzer.unify()?;
        let layout = analyzer.layout();

        Ok(layout.clone())
    }

    /// Performs the disassembly process to turn the input contract code into
    /// bytecode.
    pub fn disassemble(self) -> error::Result<Analyzer<state::DisassemblyComplete>> {
        let bytecode = InstructionStream::try_from(self.contract.bytecode().as_slice())?;
        unsafe {
            self.transform_state(|old_state| {
                let vm_config = old_state.vm_config;
                let unifier_config = old_state.unifier_config;
                Ok(state::DisassemblyComplete {
                    bytecode,
                    vm_config,
                    unifier_config,
                })
            })
        }
    }
}

/// Operations available on an analyzer that has completed the disassembly of
/// the bytecode.
impl Analyzer<state::DisassemblyComplete> {
    /// Prepares the virtual machine for symbolic execution of the bytecode.
    pub fn prepare_vm(self) -> error::Result<Analyzer<state::VMReady>> {
        unsafe {
            self.transform_state(|old_state| {
                let unifier_config = old_state.unifier_config;
                let vm = VM::new(old_state.bytecode, old_state.vm_config)?;
                Ok(state::VMReady { vm, unifier_config })
            })
        }
    }
}

/// Operations available on an analyzer that has a virtual machine ready to
/// execute the bytecode.
impl Analyzer<state::VMReady> {
    /// Symbolically executes the disassembled bytecode on the [`VM`] to gather
    /// symbolic values that are built during execution.
    pub fn execute(self) -> error::Result<Analyzer<state::ExecutionComplete>> {
        unsafe {
            self.transform_state(|mut old_state| {
                old_state.vm.execute()?;
                let execution_result = old_state.vm.consume();
                let unifier_config = old_state.unifier_config;
                Ok(state::ExecutionComplete {
                    execution_result,
                    unifier_config,
                })
            })
        }
    }
}

/// Operations available on an analyzer that has a VM which has completed
/// execution of the bytecode.
impl Analyzer<state::ExecutionComplete> {
    /// Takes thew results of execution and uses them to prepare a new unifier.
    pub fn prepare_unifier(self) -> error::Result<Analyzer<state::UnifierReady>> {
        unsafe {
            self.transform_state(|old_state| {
                let unifier = Unifier::new(old_state.unifier_config, old_state.execution_result);
                Ok(state::UnifierReady { unifier })
            })
        }
    }
}

/// Operations available on an analyzer that has a unifier ready to perform
/// inference and unification processes.
impl Analyzer<state::UnifierReady> {
    /// Takes the prepared unifier and runs the unification process on the
    /// execution results.
    pub fn unify(self) -> error::Result<Analyzer<state::UnificationComplete>> {
        unsafe {
            self.transform_state(|mut old_state| {
                let layout = old_state.unifier.run()?;
                let unifier = old_state.unifier;
                Ok(state::UnificationComplete { layout, unifier })
            })
        }
    }
}

/// Operations available on an analyzer that has completed unification.
impl Analyzer<state::UnificationComplete> {
    /// Gets the final unifier state that computed the storage layout.
    pub fn unifier(&self) -> &Unifier {
        &self.state.unifier
    }

    /// Gets the computed storage layout for the contract.
    pub fn layout(&self) -> &StorageLayout {
        &self.state.layout
    }
}
