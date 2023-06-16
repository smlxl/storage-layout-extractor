//! This module contains the [`Unifier`] and related utilities.

use std::collections::VecDeque;

use crate::{
    constant::WORD_SIZE,
    error::{
        container::Locatable,
        unification::{Error, Errors, Result},
    },
    unifier::{
        abi::AbiType,
        expression::TE,
        inference_rule::InferenceRules,
        lift::LiftingPasses,
        state::{TypeVariable, TypingState},
    },
    vm::{
        value::{BoxedVal, SVD},
        ExecutionResult,
    },
    StorageLayout,
};

pub mod abi;
pub mod expression;
pub mod inference_rule;
pub mod lift;
pub mod state;

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
    state: TypingState,
}

impl Unifier {
    /// Constructs a new unifier configured by the provided `config` and working
    /// on the data in the provided `execution_result`.
    pub fn new(config: Config, execution_result: ExecutionResult) -> Self {
        // Create the state and register all initial values into it.
        let mut state = TypingState::empty();
        execution_result
            .all_values()
            .into_iter()
            .for_each(|v| _ = state.register(v));

        // Create the unifier
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
        self.lift()?;
        self.assign_vars();
        self.infer()?;
        self.cohere_equalities();
        self.unify()
    }

    /// Executes the lifting passes on all of the available symbolic values,
    /// potentially transforming them, and then returns the associated type
    /// variables for each expression.
    ///
    /// Executing this method inserts all of the transformed values into the
    /// state of the unifier.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if one or more of the lifting passes returns an error.
    pub fn lift(&mut self) -> Result<()> {
        let mut new_values = Vec::new();
        let mut errors = Errors::new();
        for value in self.values_under_analysis_cloned() {
            match self.config.sugar_passes.run(value, &self.state) {
                Ok(v) => new_values.push(v),
                Err(e) => errors.add_many_located(e),
            }
        }

        if !errors.is_empty() {
            Err(errors)
        } else {
            unsafe { self.set_values_under_analysis(new_values) };
            Ok(())
        }
    }

    /// Assigns type variables to all of the provided `values` and their
    /// sub-values, registering them in the unifier state.
    ///
    /// This function must be run after any operations (such as
    /// [`Self::lift`]) that mutate the values.
    pub fn assign_vars(&mut self) {
        // Create a queue of values that have not yet been processed.
        let mut queue: VecDeque<BoxedVal> = VecDeque::new();
        queue.extend(self.values_under_analysis_cloned());

        // While the queue still has entries, we get the children of the entry, add
        // them, and register the entry.
        while let Some(v) = queue.pop_front() {
            let inline: Vec<BoxedVal> = v.children().into_iter().cloned().collect();
            queue.extend(inline);
            self.state.register(v);
        }

        // Store the values in the unifier.
        unsafe {
            self.set_values_under_analysis(self.state.values().into_iter().cloned().collect())
        }
    }

    /// Runs the unifier's configured heuristics on all of the values that have
    /// been registered with the unifier.
    ///
    /// Analysis will produce no results if [`Self::assign_vars`] has not yet
    /// been run. It will also produce degraded results if [`Self::lift`]
    /// has not been run.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if one or more of the heuristics returns an error.
    pub fn infer(&mut self) -> Result<()> {
        let pairs: Vec<(BoxedVal, TypeVariable)> = self.state.pairs_cloned();
        for (value, ty) in pairs {
            self.config.inference_rules.infer(&value, ty, &mut self.state)?;
        }

        Ok(())
    }

    /// This function ensures that all [`expression::TypeExpression::Equal`]
    /// judgements are represented symmetrically in the judgement sets.
    pub fn cohere_equalities(&mut self) {
        let variables = self.state.variables();

        variables.iter().for_each(|tv| {
            // Get the inferences associated with the current variable
            let inferences = self.state.inferences_cloned(*tv);

            // Pull out any of those inferences that assert equality with another type
            // variable
            let equalities: Vec<TypeVariable> = inferences
                .iter()
                .flat_map(|i| {
                    if let TE::Equal { id } = i {
                        vec![*id]
                    } else {
                        vec![]
                    }
                })
                .collect();

            // Construct an equality for the current variable
            let this_equality = TE::Equal { id: *tv };

            // And add it to the inferences for the type variables that were equal to the
            // current variable
            equalities
                .into_iter()
                .for_each(|tv| self.state.infer(tv, this_equality.clone()))
        })
    }

    /// Runs unification on all of the type variables registered in the unifier
    /// to discover the most concrete types for the storage slots in the
    /// contract.
    ///
    /// Analysis will produce no results if [`Self::assign_vars`] has not yet
    /// been run. It will also produce degraded results if [`Self::infer`]
    /// has not been run or if [`Self::cohere_equalities`] has not been run.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the unification process fails.
    pub fn unify(&mut self) -> Result<StorageLayout> {
        let mut layout = StorageLayout::default();
        let all_values = self.state.values();

        let constant_storage_slots: Vec<&BoxedVal> = all_values
            .into_iter()
            .filter(|v| {
                matches!(
                    &v.data,
                    SVD::StorageSlot { key } if matches!(&key.data, SVD::KnownData {..}))
            })
            .collect();

        for slot in constant_storage_slots {
            let ty_var = self.state.var_unchecked(slot);
            let SVD::StorageSlot { key } = &slot.data else {
                Err(Error::InvalidTree {
                    value: slot.clone(),
                    reason: "Failed to destructure supposedly known structure".into()
                }.locate(slot.instruction_pointer))?
            };
            let SVD::KnownData { value } = &key.data else {
                Err(Error::InvalidTree {
                    value: key.clone(),
                    reason: "Failed to destructure supposedly known structure".into()
                }.locate(slot.instruction_pointer))?
            };

            let index: usize = value.into();
            let abi_type = self.resolve_type_for(ty_var)?;

            layout.add(index, abi_type);
        }

        Ok(layout)
    }

    /// Converts the inferences made about `var` into the best possible
    /// [`AbiType`].
    ///
    /// # Errors
    ///
    /// If something goes wrong in the computation of the AbiType.
    #[allow(clippy::len_zero)]
    fn resolve_type_for(&self, var: TypeVariable) -> Result<AbiType> {
        let inferences = self.state.transitive_inferences(var);

        // In this case we know nothing about it
        if inferences.is_empty() {
            return Ok(AbiType::Any);
        }

        // For now we just grab the first so we don't crash (temporary)
        let inference = inferences.into_iter().collect::<Vec<_>>().first().unwrap().clone();

        // TODO [Ara] Rules for combining multiple inferences

        let result = match inference {
            TE::ConcreteType { ty } => ty,
            TE::Equal { .. } => {
                let location = self.state.value_unchecked(var).instruction_pointer;
                Err(Error::InvalidInference {
                    value:  inference.clone(),
                    reason: "Equalities should not exist in the output of `transitive_inferences`"
                        .into(),
                }
                .locate(location))?
            }
            TE::Word { width, signed } => match signed {
                Some(s) if s => AbiType::Int {
                    size: width.unwrap_or(WORD_SIZE) as u16,
                },
                _ => AbiType::UInt {
                    size: width.unwrap_or(WORD_SIZE) as u16,
                },
            },
            TE::Mapping { key, value } => {
                let key_tp = Box::new(self.resolve_type_for(key)?);
                let val_tp = Box::new(self.resolve_type_for(value)?);
                AbiType::Mapping { key_tp, val_tp }
            }
            TE::DynamicArray { element } => {
                let tp = Box::new(self.resolve_type_for(element)?);
                AbiType::DynArray { tp }
            }
            TE::FixedArray {
                element,
                length: size,
            } => {
                let tp = Box::new(self.resolve_type_for(element)?);
                AbiType::Array { size, tp }
            }
        };

        Ok(result)
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
    pub fn state(&self) -> &TypingState {
        &self.state
    }

    /// Mutably gets the state of the unifier.
    ///
    /// # Safety
    ///
    /// This function should only be used to alter the unifier state if you
    /// clearly understand the operations this entails, and the invariants that
    /// might be violated.
    pub unsafe fn state_mut(&mut self) -> &mut TypingState {
        &mut self.state
    }

    /// Gets the values currently being analysed by the unifier.
    ///
    /// Exactly what these are depends heavily on the current state of the
    /// unifier at the time this method is called.
    pub fn values_under_analysis(&self) -> Vec<&BoxedVal> {
        self.state.values()
    }

    /// Gets the values currently being analysed by the unifier.
    ///
    /// Exactly what these are depends heavily on the current state of the
    /// unifier at the time this method is called.
    pub fn values_under_analysis_cloned(&self) -> Vec<BoxedVal> {
        self.state.values().into_iter().cloned().collect()
    }

    /// Sets the values under analysis to `values`.
    ///
    /// # Safety
    ///
    /// This method allows violating the invariants of the unifier. Only use it
    /// if you clearly understand the impacts of doing so, and the invariants
    /// that you may violate.
    ///
    /// In particular, it involves _clearing_ the state, thus invalidating all
    /// type variables and typing judgements.
    pub unsafe fn set_values_under_analysis(&mut self, values: Vec<BoxedVal>) {
        self.state.clear();
        values.into_iter().for_each(|v| _ = self.state.register(v));
    }
}

/// The unifier's configuration, allowing its behaviour to be configured
/// externally.
#[derive(Debug)]
pub struct Config {
    /// The lifting passes that will be run.
    ///
    /// Defaults to [`LiftingPasses::default()`].
    pub sugar_passes: LiftingPasses,

    /// The inference rules that the unifier will use.
    ///
    /// Defaults to [`InferenceRules::default()`].
    pub inference_rules: InferenceRules,
}

/// Creates a default unifier configuration.
impl Default for Config {
    fn default() -> Self {
        let sugar_passes = LiftingPasses::default();
        let inference_rules = InferenceRules::default();
        Self {
            sugar_passes,
            inference_rules,
        }
    }
}

#[cfg(test)]
pub mod test {
    use crate::{
        unifier::{abi::AbiType, expression::TE, Config, Unifier},
        vm::value::{known::KnownWord, Provenance, SymbolicValue, SVD},
    };

    #[test]
    fn unifies_a_single_simple_storage_slot() -> anyhow::Result<()> {
        // `v_2 + v_3`
        let v_2 = SymbolicValue::new_value(0, Provenance::Synthetic);
        let v_3 = SymbolicValue::new_value(1, Provenance::Synthetic);
        let add = SymbolicValue::new(
            2,
            SVD::Add {
                left:  v_2.clone(),
                right: v_3.clone(),
            },
            Provenance::Synthetic,
        );

        // `concat(v_1, c_1)`
        let v_1 = SymbolicValue::new_value(3, Provenance::Synthetic);
        let c_1 = SymbolicValue::new_known_value(4, KnownWord::from(1), Provenance::Synthetic);
        let concat = SymbolicValue::new(
            5,
            SVD::Concat {
                values: vec![v_1.clone(), c_1.clone()],
            },
            Provenance::Synthetic,
        );

        // `sha3(concat(v_1, c_1))`
        let sha3 = SymbolicValue::new(
            5,
            SVD::Sha3 {
                data: concat.clone(),
            },
            Provenance::Synthetic,
        );

        // `s_store(sha3(concat(v_1, c_1)), v_2 + v_3)`
        let store = SymbolicValue::new(
            6,
            SVD::StorageWrite {
                key:   sha3.clone(),
                value: add.clone(),
            },
            Provenance::Synthetic,
        );

        // Create the unifier
        let config = Config::default();
        let mut unifier = Unifier::new(config, util::default_execution_result());

        // Force the values for analysis to be our `store` above.
        unsafe { unifier.set_values_under_analysis(vec![store.clone()]) }

        // First we run the lifting, and check the results
        unifier.lift()?;
        let results = unifier.values_under_analysis_cloned();
        assert_eq!(results.len(), 1);

        let c_1_slot = SymbolicValue::new(
            0,
            SVD::StorageSlot { key: c_1.clone() },
            Provenance::Synthetic,
        );
        let c_1_mapping = SymbolicValue::new(
            0,
            SVD::MappingAccess {
                key:  v_1.clone(),
                slot: c_1_slot.clone(),
            },
            Provenance::Synthetic,
        );
        let store_slot = SymbolicValue::new(
            0,
            SVD::StorageSlot {
                key: c_1_mapping.clone(),
            },
            Provenance::Synthetic,
        );
        let processed_store = SymbolicValue::new(
            0,
            SVD::StorageWrite {
                key:   store_slot.clone(),
                value: add.clone(),
            },
            Provenance::Synthetic,
        );

        assert_eq!(results[0], processed_store);

        // Now we can run type variable assignment and check things
        unifier.assign_vars();
        let values = unifier.values_under_analysis();
        assert_eq!(values.len(), 9);

        // It should contain the lifted values
        assert!(values.contains(&&v_2));
        assert!(values.contains(&&v_3));
        assert!(values.contains(&&add));
        assert!(values.contains(&&v_1));
        assert!(values.contains(&&c_1));
        assert!(values.contains(&&c_1_slot));
        assert!(values.contains(&&c_1_mapping));
        assert!(values.contains(&&store_slot));
        assert!(values.contains(&&processed_store));

        // But not the ones eliminated by that process
        assert!(!values.contains(&&concat));
        assert!(!values.contains(&&sha3));
        assert!(!values.contains(&&store));

        // Next we can actually run the inference process and unify
        unifier.infer()?;
        unifier.cohere_equalities();

        // We can check on the layout to make sure things are correct
        let layout = unifier.unify()?;
        let slots = layout.slots();
        assert_eq!(slots.len(), 1);

        let first_slot = slots.first().unwrap();
        assert_eq!(first_slot.index, 1);
        assert_eq!(
            first_slot.typ,
            AbiType::Mapping {
                key_tp: Box::new(AbiType::Any),
                val_tp: Box::new(AbiType::Any),
            }
        );

        // All done
        Ok(())
    }

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
        let storage_key =
            SymbolicValue::new_known_value(3, KnownWord::from(10), Provenance::Synthetic);
        let storage_slot = SymbolicValue::new(
            3,
            SVD::StorageSlot {
                key: storage_key.clone(),
            },
            Provenance::Synthetic,
        );
        let mapping = SymbolicValue::new(
            4,
            SVD::MappingAccess {
                slot: storage_slot.clone(),
                key:  add.clone(),
            },
            Provenance::Synthetic,
        );
        let var_3 = SymbolicValue::new_value(5, Provenance::Synthetic);

        let values = vec![mapping.clone(), var_3.clone()];

        let config = Config::default();
        let mut unifier = Unifier::new(config, util::default_execution_result());
        unsafe { unifier.set_values_under_analysis(values) };

        unifier.assign_vars();
        let state = unifier.state();

        assert_eq!(state.values().len(), 7);
        assert!(state.var(&var_1).is_some());
        assert!(state.var(&var_2).is_some());
        assert!(state.var(&add).is_some());
        assert!(state.var(&storage_key).is_some());
        assert!(state.var(&storage_slot).is_some());
        assert!(state.var(&mapping).is_some());
        assert!(state.var(&var_3).is_some());
    }

    #[test]
    fn makes_equalities_symmetric() {
        // Create some values
        let var_1 = SymbolicValue::new_value(0, Provenance::Synthetic);
        let var_2 = SymbolicValue::new_value(1, Provenance::Synthetic);

        // Create the unifier
        let config = Config::default();
        let mut unifier = Unifier::new(config, util::default_execution_result());
        let state = unsafe {
            unifier.set_values_under_analysis(vec![var_1.clone(), var_2.clone()]);
            unifier.state_mut()
        };

        let var_1_ty = state.register(var_1);
        let var_2_ty = state.register(var_2);
        state.infer(var_1_ty, TE::eq(var_2_ty));

        // Cohere equalities and check the result
        unifier.cohere_equalities();
        let state = unifier.state();
        let inferences_var_2 = state.inferences(var_2_ty);
        assert_eq!(inferences_var_2.len(), 1);
        assert!(inferences_var_2.contains(&TE::eq(var_1_ty)));
    }

    /// Utilities for these tests
    pub mod util {
        use crate::{
            bytecode,
            error::execution,
            opcode::control::Invalid,
            vm::{instructions::InstructionStream, ExecutionResult},
        };

        pub fn default_execution_result() -> ExecutionResult {
            ExecutionResult {
                instructions: InstructionStream::try_from(bytecode![Invalid].as_slice()).unwrap(),
                states:       Vec::new(),
                errors:       execution::Errors::new(),
            }
        }
    }
}
