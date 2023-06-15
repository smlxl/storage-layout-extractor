//! This module contains the [`Unifier`] and related utilities.

use crate::{
    error::unification::{Errors, Result},
    unifier::{state::UnifierState, sugar::ReSugarPasses},
    vm::{value::BoxedVal, ExecutionResult},
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

    /// Executes the re-sugaring passes on all of the available symbolic values,
    /// potentially transforming them, and then returns the associated type
    /// variables for each expression.
    ///
    /// Executing this method inserts all of the transformed values into the
    /// state of the unifier.
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

    // TODO [Ara] Discover storage slots in re-sugaring
    // TODO [Ara] Assign type variables
    // TODO [Ara] Run heuristics
    // TODO [Ara] Unify

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
mod test {}
