//! This module contains the [`TypeChecker`] and related utilities that deal
//! with inferring and unifying types for the program.

use std::collections::{HashSet, VecDeque};

use itertools::Itertools;
use state::type_variable::TypeVariable;

use crate::{
    constant::BYTE_SIZE_BITS,
    error::{
        container::Locatable,
        unification::{Error, Errors, Result},
    },
    tc::{
        abi::{AbiType, StructElement},
        expression::{Span, TypeExpression, WordUse, TE},
        lift::LiftingPasses,
        rule::InferenceRules,
        state::TypeCheckerState,
    },
    utility::U256Wrapper,
    vm::{
        value::{RuntimeBoxedVal, TCBoxedVal, TCSVD},
        ExecutionResult,
    },
    watchdog::DynWatchdog,
    StorageLayout,
};

pub mod abi;
pub mod debug;
pub mod expression;
pub mod lift;
pub mod rule;
pub mod state;
pub mod unification;

/// The `TypeChecker` is responsible for the collection of typing evidence for
/// all values in the program, and then combining that evidence to infer types
/// for those values.
#[derive(Debug)]
pub struct TypeChecker {
    /// The configuration of the type checker.
    config: Config,

    /// The internal state for the type checker,
    state: TypeCheckerState,

    /// A watchdog that gets polled at intervals to check whether the analysis
    /// needs to exit.
    watchdog: DynWatchdog,
}

impl TypeChecker {
    /// Constructs a new type checker configured by the provided `config` and
    /// whose execution is monitored by the provided `watchdog`.
    #[must_use]
    pub fn new(config: Config, watchdog: DynWatchdog) -> Self {
        let state = TypeCheckerState::empty();

        // Create the unifier
        Self {
            config,
            state,
            watchdog,
        }
    }

    /// Executes the type checker on the values in the provided
    /// `execution_result`, returning a storage layout where possible.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the engine's execution fails for any reason.
    pub fn run(&mut self, execution_result: ExecutionResult) -> Result<StorageLayout> {
        let transformed_values = self.lift(execution_result)?;
        self.assign_vars(transformed_values)?;
        self.infer()?;
        self.unify()
    }

    /// Executes the lifting passes on all of the available symbolic values in
    /// the `execution_result`, potentially transforming them and returning the
    /// transformed values.
    ///
    /// Executing this method inserts all of the transformed values into the
    /// state of the type checker.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if one or more of the lifting passes returns an error.
    pub fn lift(&mut self, execution_result: ExecutionResult) -> Result<VecDeque<RuntimeBoxedVal>> {
        // Identically structured values tell us the same thing at inference time, so we
        // remove any exact duplicates to make the type checking process faster.
        let mut result_values: VecDeque<_> =
            execution_result.all_values().into_iter().unique().collect();

        let polling_interval = self.watchdog.poll_every();
        let mut new_values = VecDeque::new();
        let mut errors = Errors::new();

        // We do these  by popping from the queue so as to deallocate immediately and
        // prevent peaks in memory residency
        let mut counter = 0;
        while let Some(value) = result_values.pop_front() {
            // If we have been told to stop, stop and return an error.
            if counter % polling_interval == 0 && self.watchdog.should_stop() {
                Err(Error::StoppedByWatchdog).locate(value.instruction_pointer())?;
            }

            // Actually run the lifting passes.
            match self.config.lifting_passes.run(value, &self.state) {
                Ok(v) => new_values.push_back(v),
                Err(e) => errors.add_many_located(e),
            }

            counter += 1;
        }

        if errors.is_empty() {
            Ok(new_values)
        } else {
            Err(errors)
        }
    }

    /// Assigns type variables to all of the provided `values` and their
    /// sub-values, registering them in the type checker state and transforming
    /// them into the value representation used by the type checker.
    ///
    /// This function must be run after any operations (such as
    /// [`Self::lift`]) that mutate the values. If this is not done, then it is
    /// possible that values will be missed in inference and unification.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if killed by the watchdog.
    pub fn assign_vars(&mut self, mut values: VecDeque<RuntimeBoxedVal>) -> Result<()> {
        let polling_interval = self.watchdog.poll_every();

        // We do this by popping so as to allow immediate deallocation on scope loss,
        // and prevent peaks in memory residency
        let mut counter = 0;
        while let Some(value) = values.pop_front() {
            // If we have been told to stop, stop and return an error
            if counter % polling_interval == 0 && self.watchdog.should_stop() {
                Err(Error::StoppedByWatchdog).locate(value.instruction_pointer())?;
            }

            let _ = self.state.register(value);

            counter += 1;
        }

        Ok(())
    }

    /// Runs the type checker's configured inference rules on all of the
    /// values that have been registered in the state.
    ///
    /// Analysis will produce no results if [`Self::assign_vars`] has not yet
    /// been run. It will also produce severely degraded results if
    /// [`Self::lift`] has not been run.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if one or more of the rules returns an error.
    pub fn infer(&mut self) -> Result<()> {
        let values = self.state.values().into_iter().cloned().collect::<Vec<_>>();

        let polling_interval = self.watchdog.poll_every();

        for (counter, value) in values.into_iter().enumerate() {
            // If we have been told to stop, stop and return an error.
            if counter % polling_interval == 0 && self.watchdog.should_stop() {
                Err(Error::StoppedByWatchdog).locate(value.instruction_pointer())?;
            }

            self.config.inference_rules.infer(&value, &mut self.state)?;
        }

        Ok(())
    }

    /// Runs unification on all of the type variables registered in the
    /// type checking state to discover the most concrete types for the storage
    /// slots in the contract.
    ///
    /// Analysis will produce no results if [`Self::assign_vars`] has not yet
    /// been run. It will also produce severely degraded results if
    /// [`Self::infer`] has not been run.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the unification process fails.
    pub fn unify(&mut self) -> Result<StorageLayout> {
        fn is_constant_storage_slot(value: &TCBoxedVal) -> bool {
            matches!(value.data(), TCSVD::StorageSlot { key } if matches!(key.data(), TCSVD::KnownData { .. }))
        }

        // Actually run unification
        unification::unify(&mut self.state, &self.watchdog)?;

        // Create an empty layout
        let mut layout = StorageLayout::default();
        let all_values = self.state.values();

        // Start building the layout
        let constant_storage_slots: Vec<TCBoxedVal> = all_values
            .into_iter()
            .filter(|value| is_constant_storage_slot(value))
            .cloned()
            .collect();

        let polling_interval = self.watchdog.poll_every();

        for (count, slot) in constant_storage_slots.into_iter().enumerate() {
            // If we have been told to stop, stop and return an error
            if count % polling_interval == 0 && self.watchdog.should_stop() {
                Err(Error::StoppedByWatchdog).locate(slot.instruction_pointer())?;
            }

            let ty_var = self.state.var_unchecked(&slot);
            let TCSVD::StorageSlot { key } = slot.data() else {
                Err(Error::InvalidTree {
                    value:  slot.clone(),
                    reason: "Failed to destructure supposedly known structure".into(),
                }
                .locate(slot.instruction_pointer()))?
            };
            let TCSVD::KnownData { value: index } = key.data() else {
                Err(Error::InvalidTree {
                    value:  key.clone(),
                    reason: "Failed to destructure supposedly known structure".into(),
                }
                .locate(slot.instruction_pointer()))?
            };

            // Get one or more types from the storage slot
            match self.abi_type_for(ty_var)? {
                AbiValue::Type(typ) => layout.add(index, 0, typ),
                AbiValue::Packed(types) => types
                    .into_iter()
                    .for_each(|(typ, offset)| layout.add(index, offset, typ)),
            }
        }

        Ok(layout)
    }

    /// Converts the inferences made about `var` into the [`AbiType`] that
    /// most-closely corresponds to the internal type representation.
    ///
    /// # Errors
    ///
    /// If something goes wrong in the computation of the [`AbiType`].
    fn abi_type_for(&mut self, var: TypeVariable) -> Result<AbiValue> {
        let mut seen_vars = HashSet::new();
        self.abi_type_for_impl(var, &mut seen_vars, ParentType::None)
    }

    /// The internal implementation of [`Self::abi_type_for`], allowing the
    /// unifier to present a better interface to clients by hiding the
    /// `seen_exprs` and `parent` parameters that are used to guard against
    /// infinite loops in type resolution.
    ///
    /// # Errors
    ///
    /// If something goes wrong in the computation of the [`AbiType`].
    #[allow(clippy::too_many_lines)] // Necessary length, splitting not beneficial
    fn abi_type_for_impl(
        &mut self,
        var: TypeVariable,
        seen_exprs: &mut HashSet<TypeExpression>,
        parent: ParentType,
    ) -> Result<AbiValue> {
        let type_expr = self.type_of(var)?;

        // If we see the same type constructor again when iterating, the type is
        // infinite so we short-circuit
        if seen_exprs.contains(&type_expr) && type_expr.is_type_constructor() {
            return Ok(AbiType::InfiniteType.into());
        }

        seen_exprs.insert(type_expr.clone());

        // Get the location in case an error needs to be raised
        let location = self.state.value(var).unwrap().instruction_pointer();
        let abi_type: AbiValue = match type_expr {
            TE::Any => AbiType::Any.into(),
            TE::Word { width, usage } => match usage {
                WordUse::Bytes => match width {
                    Some(w) if w % BYTE_SIZE_BITS == 0 => AbiType::Bytes {
                        length: width.map(|w| w / BYTE_SIZE_BITS),
                    }
                    .into(),
                    Some(w) => AbiType::Bits { length: Some(w) }.into(),
                    None => AbiType::Bytes { length: None }.into(),
                },
                WordUse::Numeric => AbiType::Number { size: width }.into(),
                WordUse::UnsignedNumeric => AbiType::UInt { size: width }.into(),
                WordUse::SignedNumeric => AbiType::Int { size: width }.into(),
                WordUse::Bool => {
                    if width != usage.size() {
                        return Err(Error::InvalidInference {
                            value:  type_expr,
                            reason: "Bool inferred with incorrect width".into(),
                        }
                        .locate(location)
                        .into());
                    }
                    AbiType::Bool.into()
                }
                WordUse::Address => {
                    if width != usage.size() {
                        return Err(Error::InvalidInference {
                            value:  type_expr,
                            reason: "Address inferred with incorrect width".into(),
                        }
                        .locate(location)
                        .into());
                    }
                    AbiType::Address.into()
                }
                WordUse::Selector => {
                    if width != usage.size() {
                        return Err(Error::InvalidInference {
                            value:  type_expr,
                            reason: "Selector inferred with incorrect width".into(),
                        }
                        .locate(location)
                        .into());
                    }
                    AbiType::Selector.into()
                }
                WordUse::Function => {
                    if width != usage.size() {
                        return Err(Error::InvalidInference {
                            value:  type_expr,
                            reason: "Function inferred with incorrect width".into(),
                        }
                        .locate(location)
                        .into());
                    }
                    AbiType::Function.into()
                }
            },
            TE::Bytes => AbiType::DynBytes.into(),
            TE::FixedArray { element, length } => {
                let tp = self
                    .abi_type_for_impl(element, seen_exprs, ParentType::Other)?
                    .expect_type("Fixed array element resolved to multiple types");
                AbiType::Array {
                    size: U256Wrapper(length),
                    tp:   Box::new(tp),
                }
                .into()
            }
            TE::Mapping { key, value } => {
                let key_tp = self
                    .abi_type_for_impl(key, seen_exprs, ParentType::Other)?
                    .expect_type("Mapping key resolved to multiple types");
                let val_tp = self
                    .abi_type_for_impl(value, seen_exprs, ParentType::Other)?
                    .expect_type("Mapping value resolved to multiple types");
                AbiType::Mapping {
                    key_type:   Box::new(key_tp),
                    value_type: Box::new(val_tp),
                }
                .into()
            }
            TE::DynamicArray { element } => {
                let tp = self
                    .abi_type_for_impl(element, seen_exprs, ParentType::Other)?
                    .expect_type("Dynamic array element resolved to multiple types");
                AbiType::DynArray { tp: Box::new(tp) }.into()
            }
            TE::Packed { types, is_struct } => {
                let mut pairs = Vec::new();
                for Span { typ, offset, .. } in types {
                    match self.abi_type_for_impl(typ, seen_exprs, ParentType::Packed)? {
                        AbiValue::Packed(xs) => {
                            pairs.extend(xs.into_iter().map(|(ty, ofs)| (ty, ofs + offset)));
                        }
                        AbiValue::Type(ty) => pairs.push((ty.clone(), offset)),
                    }
                }

                if parent == ParentType::Packed {
                    // If it has packed as a parent, we want to return them no matter what.
                    AbiValue::Packed(pairs)
                } else if pairs.is_empty() {
                    // If it is empty, we know nothing
                    AbiType::Any.into()
                } else if pairs.len() == 1 {
                    // If it has length 1, it's not really packed
                    let pair @ (typ, offset) = pairs.first().unwrap();
                    if *offset == 0 {
                        // If the offset is zero the slot is the contained type
                        typ.into()
                    } else {
                        // But if it isn't, it's actually a packed where we don't know its
                        // elements so we have to insert a synthetic
                        // element to make the spacing work
                        AbiValue::Packed(vec![
                            (
                                AbiType::Bytes {
                                    length: Some(offset / BYTE_SIZE_BITS),
                                },
                                0,
                            ),
                            pair.clone(),
                        ])
                    }
                } else if is_struct {
                    // If it is a struct it is a single element, so we turn it into one
                    let elements = pairs
                        .into_iter()
                        .map(|(typ, offset)| StructElement::new(offset, typ))
                        .collect();
                    AbiType::Struct { elements }.into()
                } else {
                    // Otherwise it is a standard packed encoding, so we return a set of
                    // sub-slot types
                    AbiValue::Packed(pairs)
                }
            }
            TE::Equal { id } => {
                return Err(Error::InvalidInference {
                    value:  TE::Equal { id },
                    reason: "Equalities cannot be converted into ABI types".into(),
                }
                .locate(location)
                .into());
            }
            TE::Conflict { conflicts, reasons } => AbiType::ConflictedType {
                reasons,
                conflicts: conflicts.into_iter().map(|c| format!("{c:?}")).collect(),
            }
            .into(),
        };

        Ok(abi_type)
    }

    /// Gets the unified type for the provided `type_variable`.
    ///
    /// This type will _always_ be a single type if the method returns
    /// successfully. This _does not_ mean that it will be a concrete type, as
    /// it may well be (or contain) [`TE::Any`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if there is no resolved type for `tv`.
    #[allow(clippy::missing_panics_doc)] // Panic is guarded
    pub fn type_of(&mut self, type_variable: TypeVariable) -> Result<TypeExpression> {
        let forest = self.state.result();
        match forest.get_data(&type_variable).cloned() {
            None => {
                let location = self.state.value_unchecked(type_variable).instruction_pointer();
                Err(Error::UnificationFailure { var: type_variable }.locate(location))?
            }
            Some(inferences) => {
                let vec = inferences.iter().cloned().collect::<Vec<_>>();

                match vec.len() {
                    0 => Ok(TE::Any),
                    1 => Ok(vec.first().expect("We know the vec has at least one item").clone()),
                    _ => {
                        let location =
                            self.state.value_unchecked(type_variable).instruction_pointer();
                        Err(Error::UnificationIncomplete {
                            var:        type_variable,
                            inferences: inferences.iter().cloned().collect(),
                        }
                        .locate(location))?
                    }
                }
            }
        }
    }

    /// Gets the type checker's configuration to allow inspection.
    #[must_use]
    pub fn config(&self) -> &Config {
        &self.config
    }

    /// Gets the type checking state.
    #[must_use]
    pub fn state(&self) -> &TypeCheckerState {
        &self.state
    }

    /// Gets the type checking state.
    ///
    /// # Safety
    ///
    /// This function should only be used to alter the engine state if you
    /// clearly understand the operations this entails, and the invariants that
    /// might be violated.
    #[must_use]
    pub unsafe fn state_mut(&mut self) -> &mut TypeCheckerState {
        &mut self.state
    }

    /// Gets the values currently being analysed by the type checker.
    ///
    /// Exactly what these are depends heavily on the current state of the
    /// engine at the time this method is called.
    #[must_use]
    pub fn values_under_analysis(&self) -> Vec<&TCBoxedVal> {
        self.state.values()
    }

    /// Gets the values currently being analysed by the type checker.
    ///
    /// Exactly what these are depends heavily on the current state of the
    /// type checker at the time this method is called.
    #[must_use]
    pub fn values_under_analysis_cloned(&self) -> Vec<TCBoxedVal> {
        self.state.values().into_iter().cloned().collect()
    }

    /// Sets the values under analysis to `values`.
    ///
    /// # Safety
    ///
    /// This method allows violating the invariants of the type checker.
    /// Only use it if you clearly understand the impacts of doing so, and
    /// the invariants that you may violate.
    ///
    /// In particular, it involves _clearing_ the state, thus invalidating all
    /// type variables and typing judgements.
    pub unsafe fn set_runtime_values_under_analysis(&mut self, values: Vec<RuntimeBoxedVal>) {
        self.state.clear();
        for v in values {
            let _ = self.state.register(v);
        }
    }
}

/// The type checker's configuration, allowing its behaviour to be configured
/// externally.
#[derive(Debug)]
pub struct Config {
    /// The lifting passes that will be run.
    ///
    /// Defaults to [`LiftingPasses::default()`].
    pub lifting_passes: LiftingPasses,

    /// The inference rules that the type checker will use.
    ///
    /// Defaults to [`InferenceRules::default()`].
    pub inference_rules: InferenceRules,
}

impl Config {
    /// Sets the `lifting_passes` config parameter to `value`.
    #[must_use]
    pub fn with_lifting_passes(mut self, value: LiftingPasses) -> Config {
        self.lifting_passes = value;
        self
    }

    /// Sets the `inference_rules` config parameter to `value`.
    #[must_use]
    pub fn with_inference_rules(mut self, value: InferenceRules) -> Config {
        self.inference_rules = value;
        self
    }
}

/// Creates a default type checker configuration.
impl Default for Config {
    fn default() -> Self {
        let lifting_passes = LiftingPasses::default();
        let inference_rules = InferenceRules::default();
        Self {
            lifting_passes,
            inference_rules,
        }
    }
}

/// A representation of an `AbiType` that occurs at a specified position within
/// a word.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AbiValue {
    /// A single ABI type.
    Type(AbiType),

    /// A set of ABI types with their offsets in bits inside the parent word.
    Packed(Vec<(AbiType, usize)>),
}

impl AbiValue {
    /// Expects that the value is a single type.
    ///
    /// # Panics
    ///
    /// If `self` is not [`Self::Packed`].
    #[must_use]
    pub fn expect_type(self, _: &'static str) -> AbiType {
        match self {
            Self::Type(tp) => tp,
            Self::Packed(tps) => {
                let mut elements = tps
                    .iter()
                    .map(|(tp, off)| StructElement::new(*off, tp.clone()))
                    .collect_vec();

                // Make sure we start at offset 0
                match elements.first() {
                    Some(first) if first.offset != 0 => elements.insert(
                        0,
                        StructElement::new(
                            0,
                            AbiType::Bytes {
                                length: Some(first.offset / BYTE_SIZE_BITS),
                            },
                        ),
                    ),
                    _ => (),
                }

                AbiType::Struct { elements }
            }
        }
    }
}

impl From<AbiType> for AbiValue {
    fn from(value: AbiType) -> Self {
        Self::Type(value)
    }
}

impl From<&AbiType> for AbiValue {
    fn from(value: &AbiType) -> Self {
        Self::Type(value.clone())
    }
}

impl From<Vec<(AbiType, usize)>> for AbiValue {
    fn from(value: Vec<(AbiType, usize)>) -> Self {
        Self::Packed(value)
    }
}

/// An enum used during resolution of ABI types to prevent the insertion of
/// defaulted elements in certain places.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum ParentType {
    /// The parent type for this call was [`TE::Packed`].
    Packed,

    /// The parent type for this call was some other type expression.
    Other,

    /// There was no parent type for the call.
    None,
}

#[cfg(test)]
pub mod test {
    use std::collections::VecDeque;

    use crate::{
        tc::{abi::AbiType, Config, TypeChecker},
        utility::U256W,
        vm::value::{known::KnownWord, Provenance, RSV, RSVD},
        watchdog::LazyWatchdog,
    };

    #[test]
    fn unifies_a_single_simple_storage_slot() -> anyhow::Result<()> {
        // `v_2 + v_3`
        let v_2 = RSV::new_value(0, Provenance::Synthetic);
        let v_3 = RSV::new_value(1, Provenance::Synthetic);
        let add = RSV::new(
            2,
            RSVD::Add {
                left:  v_2.clone(),
                right: v_3.clone(),
            },
            Provenance::Synthetic,
            None,
        );

        // `concat(v_1, c_1)`
        let v_1 = RSV::new_value(3, Provenance::Synthetic);
        let c_1 = RSV::new_known_value(4, KnownWord::from(1), Provenance::Synthetic, None);
        let concat = RSV::new(
            5,
            RSVD::Concat {
                values: vec![v_1.clone(), c_1.clone()],
            },
            Provenance::Synthetic,
            None,
        );

        // `sha3(concat(v_1, c_1))`
        let sha3 = RSV::new(
            5,
            RSVD::Sha3 {
                data: concat.clone(),
            },
            Provenance::Synthetic,
            None,
        );

        // `s_store(sha3(concat(v_1, c_1)), v_2 + v_3)`
        let store = RSV::new(
            6,
            RSVD::StorageWrite {
                key:   sha3.clone(),
                value: add.clone(),
            },
            Provenance::Synthetic,
            None,
        );

        // Create the unifier
        let config = Config::default();
        let mut unifier = TypeChecker::new(config, LazyWatchdog.in_rc());

        // First we run the lifting, and check the results
        let results = unifier.lift(util::execution_result_with_values(vec![store.clone()]))?;
        assert_eq!(results.len(), 1);

        let c_1_slot = RSV::new(
            0,
            RSVD::StorageSlot { key: c_1.clone() },
            Provenance::Synthetic,
            None,
        );
        let c_1_mapping = RSV::new(
            0,
            RSVD::MappingIndex {
                key:        v_1.clone(),
                slot:       c_1_slot.clone(),
                projection: None,
            },
            Provenance::Synthetic,
            None,
        );
        let store_slot = RSV::new(
            0,
            RSVD::StorageSlot {
                key: c_1_mapping.clone(),
            },
            Provenance::Synthetic,
            None,
        );
        let processed_store = RSV::new(
            0,
            RSVD::StorageWrite {
                key:   store_slot.clone(),
                value: add.clone(),
            },
            Provenance::Synthetic,
            None,
        );

        assert_eq!(results[0], processed_store);

        // Now we can run type variable assignment and tc
        unifier.assign_vars(results)?;
        unifier.infer()?;

        // We can check on the layout to make sure things are correct
        let layout = unifier.unify()?;
        let slots = layout.slots();
        assert_eq!(slots.len(), 1);

        let first_slot = slots.first().unwrap();
        assert_eq!(first_slot.index, U256W::from(1));
        assert_eq!(
            first_slot.typ,
            AbiType::Mapping {
                key_type:   Box::new(AbiType::Any),
                value_type: Box::new(AbiType::Number { size: None }),
            }
        );

        // All done
        Ok(())
    }

    #[test]
    fn assigns_type_variables_to_all_sub_expressions() -> anyhow::Result<()> {
        let var_1 = RSV::new_value(0, Provenance::Synthetic);
        let var_2 = RSV::new_value(1, Provenance::Synthetic);
        let add = RSV::new(
            2,
            RSVD::Add {
                left:  var_1.clone(),
                right: var_2.clone(),
            },
            Provenance::Synthetic,
            None,
        );
        let storage_key = RSV::new_known_value(3, KnownWord::from(10), Provenance::Synthetic, None);
        let storage_slot = RSV::new(
            3,
            RSVD::StorageSlot {
                key: storage_key.clone(),
            },
            Provenance::Synthetic,
            None,
        );
        let mapping = RSV::new(
            4,
            RSVD::MappingIndex {
                slot:       storage_slot.clone(),
                key:        add.clone(),
                projection: None,
            },
            Provenance::Synthetic,
            None,
        );
        let var_3 = RSV::new_value(5, Provenance::Synthetic);

        let values = VecDeque::from([mapping.clone(), var_3.clone()]);

        let config = Config::default();
        let mut unifier = TypeChecker::new(config, LazyWatchdog.in_rc());

        unifier.assign_vars(values)?;
        let state = unifier.state();

        assert_eq!(state.values().len(), 7);

        Ok(())
    }

    /// Utilities for these tests
    #[allow(clippy::missing_panics_doc)]
    pub mod util {
        use crate::{
            bytecode,
            disassembly::InstructionStream,
            error::execution,
            opcode::control::Invalid,
            vm::{state::VMState, value::RuntimeBoxedVal, Config, ExecutionResult},
        };

        /// Creates a default execution result.
        #[must_use]
        pub fn default_execution_result() -> ExecutionResult {
            ExecutionResult {
                instructions: InstructionStream::try_from(bytecode![Invalid::default()].as_slice())
                    .expect("Cannot actually panic due to statically-known bytecode"),
                states:       Vec::new(),
                errors:       execution::Errors::new(),
            }
        }

        /// Creates an execution result that puts the provided `values`
        /// somewhere in it for analysis.
        #[must_use]
        pub fn execution_result_with_values(values: Vec<RuntimeBoxedVal>) -> ExecutionResult {
            let mut state_with_values = VMState::new(0, 0, Config::default());
            values.into_iter().for_each(|v| state_with_values.record_value(v));

            ExecutionResult {
                instructions: InstructionStream::try_from(bytecode![Invalid::default()].as_slice())
                    .expect("Cannot actually panic due to statically-known bytecode"),
                states:       vec![state_with_values],
                errors:       execution::Errors::new(),
            }
        }
    }
}
