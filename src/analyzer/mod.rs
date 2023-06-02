//! This module contains the definition of the analyzer itself.

pub mod chain;
pub mod state;

use crate::{
    analyzer::state::State,
    contract::Contract,
    error,
    vm,
    vm::{instructions::InstructionStream, VM},
};

/// Creates a new analyzer wrapping the provided `contract`.
pub fn new(contract: Contract) -> Analyzer<state::HasContract> {
    let state = state::HasContract;
    Analyzer { contract, state }
}

/// The core of the storage layout analysis, the `Analyzer` is responsible for
/// ingesting user data and outputting a storage layout.
///
/// # Basic Usage
///
/// For the most basic usage of the library, it is sufficient to construct an
/// `Analyzer` and call the `.analyze` method, passing your contract.
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

/// Operations available on a newly-created analyzer.
impl Analyzer<state::HasContract> {
    /// Executes the analysis process for beginning to end, performing all the
    /// intermediate steps automatically.
    pub fn analyze(self, config: vm::Config) -> error::Result<Analyzer<state::ExecutionComplete>> {
        let analyzer = self.disassemble()?;
        let analyzer = analyzer.prepare_vm(config)?;
        let analyzer = analyzer.execute()?;

        Ok(analyzer)
    }

    /// Performs the disassembly process to turn the input contract code into
    /// bytecode, using the provided `config` to control the VM's behaviour.
    pub fn disassemble(self) -> error::Result<Analyzer<state::DisassemblyComplete>> {
        let bytecode = InstructionStream::try_from(self.contract.bytecode().as_slice())?;
        let state = state::DisassemblyComplete { bytecode };
        Ok(unsafe { self.set_state(state) })
    }
}

/// Operations available on an analyzer that has completed the disassembly of
/// the bytecode.
impl Analyzer<state::DisassemblyComplete> {
    /// Prepares the virtual machine for symbolic execution of the bytecode.
    pub fn prepare_vm(self, config: vm::Config) -> error::Result<Analyzer<state::VMReady>> {
        unsafe {
            self.transform_state(|old_state| {
                let vm = VM::new(old_state.bytecode, config)?;
                Ok(state::VMReady { vm })
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
                Ok(state::ExecutionComplete { execution_result })
            })
        }
    }
}

#[cfg(test)]
mod test {
    use ethnum::U256;
    use project_root::get_project_root;

    use crate::{
        analyzer::chain::{
            version::{ChainVersion, EthereumVersion},
            Chain,
        },
        contract::Contract,
        vm::{
            value::{known_data::KnownData, BoxedVal, SymbolicValueData},
            Config,
        },
    };

    fn pprint_known_data(value: &KnownData) -> String {
        match value {
            KnownData::Bytes { value } => format!("bytes({:?})", value),
            KnownData::UInt { value } => {
                let mut bytes = value.clone();
                bytes.resize(32, 0);
                format!(
                    "uint({})",
                    U256::from_le_bytes(bytes.as_slice().try_into().unwrap())
                )
            }
            _ => format!("{:?}", value),
        }
    }

    fn pprint_symbolic_value_data(value: &SymbolicValueData) -> String {
        match value {
            SymbolicValueData::KnownData { value, .. } => pprint_known_data(value),
            SymbolicValueData::Sha3 {
                value,
                offset,
                size,
            } => format!(
                "sha3({}, {}, {})",
                pprint_boxed_val(value),
                pprint_boxed_val(offset),
                pprint_boxed_val(size)
            ),
            SymbolicValueData::CallData { offset, size } => format!(
                "calldata({}, {})",
                pprint_boxed_val(offset),
                pprint_boxed_val(size)
            ),
            SymbolicValueData::Or { left, right } => {
                format!(
                    "or({}, {})",
                    pprint_boxed_val(left),
                    pprint_boxed_val(right)
                )
            }
            SymbolicValueData::And { left, right } => {
                format!(
                    "and({}, {})",
                    pprint_boxed_val(left),
                    pprint_boxed_val(right)
                )
            }
            SymbolicValueData::Subtract { left, right } => {
                format!(
                    "sub({}, {})",
                    pprint_boxed_val(left),
                    pprint_boxed_val(right)
                )
            }
            SymbolicValueData::LeftShift { shift, value } => {
                format!(
                    "shl({}, {})",
                    pprint_boxed_val(value),
                    pprint_boxed_val(shift)
                )
            }
            SymbolicValueData::Not { bool } => {
                format!("not({})", pprint_boxed_val(bool))
            }
            SymbolicValueData::SLoad { key } => {
                format!("sload({})", pprint_boxed_val(key))
            }

            _ => format!("{:?}", value),
        }
    }

    fn pprint_boxed_val(value: &BoxedVal) -> String {
        return pprint_symbolic_value_data(&value.data);
    }

    #[test]
    pub fn analyze_bytecode_from_file() -> anyhow::Result<()> {
        // Get the contract to be analyzed
        let root = get_project_root().unwrap();
        let contract_path = format!("{}/asset/BytecodeExample.json", root.display());
        let contract = Contract::new_from_file(
            contract_path,
            Chain::Ethereum {
                version: EthereumVersion::latest(),
            },
        )
        .unwrap();

        // Create the analyzer
        let analyzer = crate::new(contract).analyze(Config::default()).unwrap();

        // Grab the results of execution by ref
        let results = &analyzer.state().execution_result;

        // Print out all of the various stored values
        for (i, state) in results.states.iter().enumerate() {
            println!("=== State Number {i} ===");

            let storage_keys = state.storage().keys();

            for key in storage_keys {
                println!("  ===== Slot =====");
                println!("  KEY: {}", pprint_boxed_val(key));

                let generations = state.storage().generations(key).unwrap();

                for gen in generations {
                    println!("  VALUE: {}", pprint_boxed_val(gen));
                }
            }

            println!();
        }

        Ok(())
    }
}
