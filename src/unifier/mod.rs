//! This module contains the [`Unifier`] and related utilities.

use std::collections::VecDeque;

use crate::{
    error::unification::{Errors, Result},
    unifier::{
        state::{TypeVariable, UnifierState},
        sugar::ReSugarPasses,
    },
    vm::{value::BoxedVal, ExecutionResult},
    StorageLayout,
};

pub mod abi;
pub mod expression;
pub mod state;
pub mod sugar;

// TODO [Ara] Precomputed keccaks for the early storage slots to help with
//   recognition of constants. With arrays.

// TODO [Ara] Config with the ability to take additional externally-defined
//   heuristics.

/// The `Unifier` is responsible for combining the evidence as to the type of a
/// storage variable.
#[derive(Debug)]
pub struct Unifier {
    /// The configuration of the unifier.
    config: Config,

    /// The results of executing the symbolic virtual machine on the contract's
    /// bytecode.
    execution_result: ExecutionResult,

    /// The internal state for the unifier,
    state: UnifierState,
}

impl Unifier {
    /// Constructs a new unifier configured by the provided `config` and working
    /// on the data in the provided `execution_result`.
    pub fn new(config: Config, execution_result: ExecutionResult) -> Self {
        let state = UnifierState::new();
        Self {
            config,
            execution_result,
            state,
        }
    }

    /// Executes the unifier on the data with which it was constructed,
    /// returning a storage layout where possible.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the unifier's execution fails for any reason.
    pub fn run(&mut self) -> Result<StorageLayout> {
        let sugared_values = self.re_sugar()?;
        self.assign_vars(sugared_values);
        self.analyze()?;
        self.unify()
    }

    /// Executes the re-sugaring passes on all of the available symbolic values,
    /// potentially transforming them, and then returns the associated type
    /// variables for each expression.
    ///
    /// Executing this method inserts all of the transformed values into the
    /// state of the unifier.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if one or more of the re-sugaring passes returns an
    /// error.
    pub fn re_sugar(&mut self) -> Result<Vec<BoxedVal>> {
        let mut new_values = Vec::new();
        let mut errors = Errors::new();
        for value in self.execution_result.all_values() {
            match self.config.sugar_passes.run(value.constant_fold(), &mut self.state) {
                Ok(v) => new_values.push(v),
                Err(e) => errors.add_many_located(e),
            }
        }

        if !errors.is_empty() {
            Err(errors)
        } else {
            Ok(new_values)
        }
    }

    /// Assigns type variables to all of the provided `values` and their
    /// sub-values, registering them in the unifier state and returning the
    /// sub-values associated with their type variables.
    ///
    /// This function must be run after any operations (such as
    /// [`Self::re_sugar`]) that mutate the values.
    pub fn assign_vars(&mut self, values: Vec<BoxedVal>) -> Vec<(&BoxedVal, TypeVariable)> {
        // Create a queue of values that have not yet been processed.
        let mut queue = VecDeque::new();
        queue.extend(values);

        // While the queue still has entries, we get the children of the entry, add
        // them, and register the entry.
        while let Some(v) = queue.pop_front() {
            let inline: Vec<BoxedVal> = v.children().into_iter().cloned().collect();
            queue.extend(inline);
            self.state.add(v);
        }

        // Get the expected data.
        self.state.pairs()
    }

    /// Runs the unifier's configured heuristics on all of the values that have
    /// been registered with the unifier.
    ///
    /// Analysis will produce no results if [`Self::assign_vars`] has not yet
    /// been run. It will also produce degraded results if [`Self::re_sugar`]
    /// has not been run.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if one or more of the heuristics returns an error.
    pub fn analyze(&mut self) -> Result<()> {
        todo!("Needs assign_vars to be done first")
    }

    /// Runs unification on all of the type variables registered in the unifier
    /// to discover the most concrete types for the storage slots in the
    /// contract.
    ///
    /// Analysis will produce no results if [`Self::assign_vars`] has not yet
    /// been run. It will also produce degraded results if [`Self::analyze`]
    /// has not been run.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the unification process fails.
    pub fn unify(&mut self) -> Result<StorageLayout> {
        todo!("Needs analyze to be done first")
    }

    /// Gets the unifier's configuration to allow inspection.
    pub fn config(&self) -> &Config {
        &self.config
    }

    /// Gets the execution result over which the unifier is operating.
    pub fn execution_result(&self) -> &ExecutionResult {
        &self.execution_result
    }

    /// Gets the state of the unifier.
    pub fn state(&self) -> &UnifierState {
        &self.state
    }

    /// Mutably gets the state of the unifier.
    ///
    /// # Safety
    ///
    /// This function should only be used to alter the unifier state if you
    /// clearly understand the operations this entails, and the invariants that
    /// might be violated.
    pub unsafe fn state_mut(&mut self) -> &mut UnifierState {
        &mut self.state
    }
}

/// The unifier's configuration, allowing its behaviour to be configured
/// externally.
#[derive(Debug)]
pub struct Config {
    /// The re-sugaring passes that will be run.
    ///
    /// Defaults to [`ReSugarPasses::default()`].
    pub sugar_passes: ReSugarPasses,
}

/// Creates a default unifier configuration.
impl Default for Config {
    fn default() -> Self {
        let sugar_passes = ReSugarPasses::default();
        Self { sugar_passes }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        bytecode,
        error::execution,
        opcode::control::Invalid,
        unifier::{Config, Unifier},
        vm::{
            instructions::InstructionStream,
            value::{known::KnownWord, Provenance, SymbolicValue, SVD},
            ExecutionResult,
        },
    };

    #[test]
    fn assigns_type_variables_to_all_sub_expressions() {
        let var_1 = SymbolicValue::new_value(0, Provenance::Synthetic);
        let var_2 = SymbolicValue::new_value(1, Provenance::Synthetic);
        let add = SymbolicValue::new(
            2,
            SVD::Add {
                left:  var_1.clone(),
                right: var_2.clone(),
            },
            Provenance::Synthetic,
        );
        let storage_slot = SymbolicValue::new(
            3,
            SVD::StorageSlot {
                index: KnownWord::from(10),
            },
            Provenance::Synthetic,
        );
        let mapping = SymbolicValue::new(
            4,
            SVD::MappingAddress {
                slot: storage_slot.clone(),
                key:  add.clone(),
            },
            Provenance::Synthetic,
        );
        let var_3 = SymbolicValue::new_value(5, Provenance::Synthetic);

        let values = vec![mapping.clone(), var_3.clone()];

        let config = Config::default();
        let mut unifier = Unifier::new(
            config,
            ExecutionResult {
                instructions: InstructionStream::try_from(bytecode![Invalid].as_slice()).unwrap(),
                states:       Vec::new(),
                errors:       execution::Errors::new(),
            },
        );

        unifier.assign_vars(values);
        let state = unifier.state();

        assert!(state.var_for_value(&var_1).is_some());
        assert!(state.var_for_value(&var_2).is_some());
        assert!(state.var_for_value(&add).is_some());
        assert!(state.var_for_value(&storage_slot).is_some());
        assert!(state.var_for_value(&mapping).is_some());
        assert!(state.var_for_value(&var_3).is_some());
    }
}
