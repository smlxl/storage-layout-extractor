//! This module contains the [`Unifier`] and related utilities.

use std::collections::{HashSet, VecDeque};

use self::abi::U256Wrapper;
use crate::{
    constant::WORD_SIZE,
    error::{
        container::Locatable,
        unification::{Error, Errors, Result},
    },
    unifier::{
        abi::AbiType,
        expression::{TypeExpression, WordUse, TE},
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
pub mod unification;

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
    #[must_use]
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

        if errors.is_empty() {
            unsafe { self.set_values_under_analysis(new_values) };
            Ok(())
        } else {
            Err(errors)
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
            self.set_values_under_analysis(self.state.values().into_iter().cloned().collect());
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
        let values = self.state.values().into_iter().cloned().collect::<Vec<_>>();
        for value in values {
            self.config.inference_rules.infer(&value, &mut self.state)?;
        }

        Ok(())
    }

    /// Runs unification on all of the type variables registered in the unifier
    /// to discover the most concrete types for the storage slots in the
    /// contract.
    ///
    /// Analysis will produce no results if [`Self::assign_vars`] has not yet
    /// been run. It will also produce degraded results if [`Self::infer`]
    /// has not been run.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the unification process fails.
    pub fn unify(&mut self) -> Result<StorageLayout> {
        // Actually run unification
        unification::unify(&mut self.state);

        // Create an empty layout
        let mut layout = StorageLayout::default();
        let all_values = self.state.values();

        // Start building the layout
        let constant_storage_slots: Vec<BoxedVal> = all_values
            .into_iter()
            .filter(|v| {
                matches!(
                    &v.data,
                    SVD::StorageSlot { key } if matches!(&key.data, SVD::KnownData {..}))
            })
            .cloned()
            .collect();

        for slot in constant_storage_slots {
            let ty_var = self.state.var_unchecked(&slot);
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
            let (abi_type, defaulted) = self.abi_type_for(ty_var)?;

            layout.add(index, abi_type, defaulted);
        }

        Ok(layout)
    }

    /// Converts the inferences made about `var` into the best possible
    /// [`AbiType`].
    ///
    /// It also returns a boolean, saying whether any defaulting took place
    /// during type conversion.
    ///
    /// # Errors
    ///
    /// If something goes wrong in the computation of the [`AbiType`].
    fn abi_type_for(&mut self, var: TypeVariable) -> Result<(AbiType, bool)> {
        let mut seen_vars = HashSet::new();
        self.abi_type_for_impl(var, &mut seen_vars)
    }

    /// The internal implementation of [`Self::abi_type_for`], allowing the
    /// unifier to present a better interface.
    ///
    /// # Errors
    ///
    /// If something goes wrong in the computation of the [`AbiType`].
    #[allow(clippy::too_many_lines)] // Necessary length, splitting not beneficial
    fn abi_type_for_impl(
        &mut self,
        var: TypeVariable,
        seen_exprs: &mut HashSet<TypeExpression>,
    ) -> Result<(AbiType, bool)> {
        let type_expr = self.type_of(var)?;

        // If we see the same tycon again when iterating, the type is infinite
        if seen_exprs.contains(&type_expr) && type_expr.is_type_constructor() {
            return Ok((AbiType::InfiniteType, false));
        }
        seen_exprs.insert(type_expr.clone());

        let mut defaulted = false;
        let abi_type: AbiType = match type_expr {
            TE::Any => AbiType::Any,
            TE::Word {
                width,
                signed,
                usage,
            } => {
                let signed = signed.unwrap_or_else(|| {
                    defaulted = true;
                    false
                });

                // And we default to the EVM's word size otherwise
                let width = width.unwrap_or_else(|| {
                    defaulted = true;
                    WORD_SIZE
                });

                let size = if let Ok(v) = u16::try_from(width) {
                    v
                } else {
                    let location = self.state.value(var).unwrap().instruction_pointer;
                    Err(Error::OverSizedNumber {
                        value: width as i128,
                        width: 16,
                    }
                    .locate(location))?
                };

                let from_signed = |signed| {
                    if signed {
                        AbiType::Int { size }
                    } else {
                        AbiType::UInt { size }
                    }
                };

                match usage {
                    WordUse::Bool => AbiType::Bool,
                    WordUse::Address => AbiType::Address,
                    WordUse::Selector => AbiType::Selector,
                    WordUse::Function => AbiType::Function,
                    WordUse::None => from_signed(signed),
                    WordUse::Bytes => {
                        if let Ok(length) = u8::try_from(width / 32) {
                            AbiType::Bytes { length }
                        } else {
                            let location = self.state.value(var).unwrap().instruction_pointer;
                            Err(Error::OverSizedNumber {
                                value: (width / 32) as i128,
                                width: 8,
                            })
                            .locate(location)?
                        }
                    }
                    WordUse::Conflict { .. } => {
                        defaulted = true;
                        from_signed(signed)
                    }
                }
            }
            TE::FixedArray { element, length } => {
                let (tp, inner_defaulted) = self.abi_type_for_impl(element, seen_exprs)?;
                defaulted = inner_defaulted;
                AbiType::Array {
                    size: U256Wrapper(length),
                    tp:   Box::new(tp),
                }
            }
            TE::Mapping { key, value } => {
                let (key_tp, key_defaulted) = self.abi_type_for_impl(key, seen_exprs)?;
                let (val_tp, val_defaulted) = self.abi_type_for_impl(value, seen_exprs)?;
                defaulted = key_defaulted || val_defaulted;
                AbiType::Mapping {
                    key_tp: Box::new(key_tp),
                    val_tp: Box::new(val_tp),
                }
            }
            TE::DynamicArray { element } => {
                let (tp, inner_defaulted) = self.abi_type_for_impl(element, seen_exprs)?;
                defaulted = inner_defaulted;
                AbiType::DynArray { tp: Box::new(tp) }
            }
            TE::Equal { id } => {
                let location = self.state.value(var).unwrap().instruction_pointer;
                return Err(Error::InvalidInference {
                    value:  TE::Equal { id },
                    reason: "Equalities cannot be converted into ABI types".into(),
                }
                .locate(location)
                .into());
            }
            TE::Conflict {
                left,
                right,
                reason,
            } => AbiType::ConflictedType {
                left: format!("{left:?}"),
                right: format!("{right:?}"),
                reason,
            },
        };

        Ok((abi_type, defaulted))
    }

    /// Gets the unified type for
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if there is no resolved type for `tv`.
    pub fn type_of(&mut self, tv: TypeVariable) -> Result<TypeExpression> {
        let forest = self.state.result();
        match forest.get_data(&tv).cloned() {
            None => {
                let location = self.state.value_unchecked(tv).instruction_pointer;
                Err(Error::UnificationFailure { var: tv }.locate(location))?
            }
            Some(inferences) => {
                let vec = inferences.iter().cloned().collect::<Vec<_>>();

                match vec.len() {
                    0 => Ok(TE::Any),
                    1 => Ok(vec
                        .first()
                        .unwrap_or_else(|| unreachable!("We know the vec has at least one item"))
                        .clone()),
                    _ => {
                        let location = self.state.value_unchecked(tv).instruction_pointer;
                        Err(Error::UnificationIncomplete {
                            var:        tv,
                            inferences: inferences.iter().cloned().collect(),
                        }
                        .locate(location))?
                    }
                }
            }
        }
    }

    /// Gets the unifier's configuration to allow inspection.
    #[must_use]
    pub fn config(&self) -> &Config {
        &self.config
    }

    /// Gets the execution result over which the unifier is operating.
    #[must_use]
    pub fn execution_result(&self) -> &ExecutionResult {
        &self.execution_result
    }

    /// Gets the state of the unifier.
    #[must_use]
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
    #[must_use]
    pub unsafe fn state_mut(&mut self) -> &mut TypingState {
        &mut self.state
    }

    /// Gets the values currently being analysed by the unifier.
    ///
    /// Exactly what these are depends heavily on the current state of the
    /// unifier at the time this method is called.
    #[must_use]
    pub fn values_under_analysis(&self) -> Vec<&BoxedVal> {
        self.state.values()
    }

    /// Gets the values currently being analysed by the unifier.
    ///
    /// Exactly what these are depends heavily on the current state of the
    /// unifier at the time this method is called.
    #[must_use]
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
        for v in values {
            self.state.register(v);
        }
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
        unifier::{abi::AbiType, Config, Unifier},
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
                val_tp: Box::new(AbiType::UInt { size: 256 }),
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

    /// Utilities for these tests
    pub mod util {
        use crate::{
            bytecode,
            error::execution,
            opcode::control::Invalid,
            vm::{instructions::InstructionStream, ExecutionResult},
        };

        /// Creates a default execution result.
        #[must_use]
        pub fn default_execution_result() -> ExecutionResult {
            ExecutionResult {
                instructions: InstructionStream::try_from(bytecode![Invalid::default()].as_slice())
                    .unwrap_or_else(|_| unreachable!("Cannot actually panic")),
                states:       Vec::new(),
                errors:       execution::Errors::new(),
            }
        }
    }
}
