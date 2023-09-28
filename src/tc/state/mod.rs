//! This module contains the definition of the type checker state and other
//! supporting types.

use std::{
    array,
    collections::{HashMap, HashSet},
};

use type_variable::{TypeVariable, TypeVariableSource};

use crate::{
    tc::{
        expression::{InferenceSet, TypeExpression, TE},
        unification::UnificationForest,
    },
    vm::value::{PackedSpan, Provenance, RuntimeBoxedVal, TCBoxedVal, RSVD, TCSV, TCSVD},
};

pub mod type_variable;

/// The internal state of the type checker, used to track modifications to
/// typing judgements as it runs.
#[derive(Clone, Debug)]
pub struct TypeCheckerState {
    /// A mapping from type variables to the symbolic values used during type
    /// checking.
    expressions: HashMap<TypeVariable, TCBoxedVal>,

    /// A mapping from known slots to the associated type variables.
    stable_types: HashMap<RuntimeBoxedVal, TCBoxedVal>,

    /// A mapping from type variables to their corresponding typing judgements.
    inferences: HashMap<TypeVariable, InferenceSet>,

    /// The results of running unification.
    ///
    /// This may be empty if the process has not yet reached the correct place.
    unification_result: UnificationForest,

    /// A source of fresh type variables.
    tyvar_source: TypeVariableSource,
}

impl TypeCheckerState {
    /// Constructs a new, empty type checker state.
    #[must_use]
    pub fn empty() -> Self {
        let expressions = HashMap::new();
        let stable_types = HashMap::new();
        let inferences = HashMap::new();
        let unification_result = UnificationForest::new();
        let tyvar_source = TypeVariableSource::new();
        Self {
            expressions,
            stable_types,
            inferences,
            unification_result,
            tyvar_source,
        }
    }

    /// Registers a symbolic `value` in the state, returning the associated type
    /// variable for the top-level value.
    ///
    /// This function recurses into the children of `value`, and so registers
    /// both `value` and each child node in the state with an associated type
    /// variable. This means that you do not have easy access to the type
    /// variables of the child nodes.
    ///
    /// # Registration Uniqueness
    ///
    /// Two calls to `register` with the same `value` will implicitly create
    /// _two different registrations_ for that `value` in the state in almost
    /// all cases.
    ///
    /// The only case where this does _not_ happen is for values that contain
    /// one or more of [`RSVD::Value`], [`RSVD::CallData`] and
    /// [`RSVD::StorageSlot`] in their trees. These are considered to have a
    /// unique type throughout a given run of the program to which all
    /// corresponding typing judgements should be ascribed.
    #[must_use]
    pub fn register(&mut self, value: RuntimeBoxedVal) -> TypeVariable {
        let returned_val = self.register_internal(value);
        self.var_unchecked(&returned_val)
    }

    /// Forces the allocation of a new type variable in the state, adding a
    /// default value to be associated with it.
    ///
    /// # Safety
    ///
    /// Use of this function introduces values that did not occur in the
    /// execution of the program, and can violate assumptions about sources of
    /// type variables.
    pub unsafe fn allocate_ty_var(&mut self) -> TypeVariable {
        let new_tv = self.tyvar_source.fresh();
        let value_for_var = TCSV::new(0, TCSVD::new_value(), Provenance::Synthetic, new_tv);

        // Register the result
        self.expressions.entry(new_tv).or_insert(value_for_var);
        self.inferences.entry(new_tv).or_insert(HashSet::new());

        // Return the newly-allocated type variable
        new_tv
    }

    /// Checks if `value` has a stable type.
    ///
    /// A stable type is one that should not change based on occurrence if the
    /// structure of the value is the same. A value is stably typed if it
    /// contains one or more of [`RSVD::Value`], [`RSVD::CallData`] and
    /// [`RSVD::StorageSlot`] in its tree.
    ///
    /// # Quadratic Traversal
    ///
    /// Despite the fact that this function does the same traversal as
    /// [`Self::register_internal`] and hence results in quadratic traversal, in
    /// practice this approach has still benchmarked as being faster than
    /// alternative single-pass approaches.
    ///
    /// Do not change this approach without careful performance analysis.
    #[must_use]
    fn is_stable_typed(value: &RuntimeBoxedVal) -> bool {
        match value.data() {
            RSVD::StorageSlot { .. } | RSVD::Value { .. } | RSVD::CallData { .. } => true,
            _ => value.children().into_iter().any(|c| Self::is_stable_typed(&c)),
        }
    }

    /// The implementation of `register` that instead returns boxed values
    /// internally to make it easier to recursively register nodes in the tree.
    #[allow(clippy::too_many_lines)] // The method would see no benefit from being split up.
    #[allow(clippy::unnecessary_box_returns)] // We always pass these around boxed.
    #[must_use]
    fn register_internal(&mut self, value: RuntimeBoxedVal) -> TCBoxedVal {
        // Storage slots need specialised handling
        let is_stable = Self::is_stable_typed(&value);
        if is_stable {
            if let Some(r) = self.stable_types.get(&value) {
                return r.clone();
            }
        }

        // We need to perform registration recursively to transform the type.
        let instruction_pointer = value.instruction_pointer();
        let provenance = value.provenance();

        let new_data = match (*value).clone().consume().data {
            RSVD::Value { id } => TCSVD::Value { id },
            RSVD::KnownData { value } => TCSVD::KnownData { value },
            RSVD::Add { left, right } => TCSVD::Add {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::Multiply { left, right } => TCSVD::Multiply {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::Subtract { left, right } => TCSVD::Subtract {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::Divide { dividend, divisor } => TCSVD::Divide {
                dividend: self.register_internal(dividend),
                divisor:  self.register_internal(divisor),
            },
            RSVD::SignedDivide { dividend, divisor } => TCSVD::SignedDivide {
                dividend: self.register_internal(dividend),
                divisor:  self.register_internal(divisor),
            },
            RSVD::Modulo { dividend, divisor } => TCSVD::Modulo {
                dividend: self.register_internal(dividend),
                divisor:  self.register_internal(divisor),
            },
            RSVD::SignedModulo { dividend, divisor } => TCSVD::SignedModulo {
                dividend: self.register_internal(dividend),
                divisor:  self.register_internal(divisor),
            },
            RSVD::Exp { value, exponent } => TCSVD::Exp {
                value:    self.register_internal(value),
                exponent: self.register_internal(exponent),
            },
            RSVD::SignExtend { size, value } => TCSVD::SignExtend {
                size:  self.register_internal(size),
                value: self.register_internal(value),
            },
            RSVD::CallWithValue {
                gas,
                address,
                value,
                argument_data,
                ret_offset,
                ret_size,
            } => TCSVD::CallWithValue {
                gas:           self.register_internal(gas),
                address:       self.register_internal(address),
                value:         self.register_internal(value),
                argument_data: self.register_internal(argument_data),
                ret_offset:    self.register_internal(ret_offset),
                ret_size:      self.register_internal(ret_size),
            },
            RSVD::CallWithoutValue {
                gas,
                address,
                argument_data,
                ret_offset,
                ret_size,
            } => TCSVD::CallWithoutValue {
                gas:           self.register_internal(gas),
                address:       self.register_internal(address),
                argument_data: self.register_internal(argument_data),
                ret_offset:    self.register_internal(ret_offset),
                ret_size:      self.register_internal(ret_size),
            },
            RSVD::Sha3 { data } => TCSVD::Sha3 {
                data: self.register_internal(data),
            },
            RSVD::Address => TCSVD::Address,
            RSVD::Balance { address } => TCSVD::Balance {
                address: self.register_internal(address),
            },
            RSVD::Origin => TCSVD::Origin,
            RSVD::Caller => TCSVD::Caller,
            RSVD::CallValue => TCSVD::CallValue,
            RSVD::GasPrice => TCSVD::GasPrice,
            RSVD::ExtCodeHash { address } => TCSVD::ExtCodeHash {
                address: self.register_internal(address),
            },
            RSVD::BlockHash { block_number } => TCSVD::BlockHash {
                block_number: self.register_internal(block_number),
            },
            RSVD::CoinBase => TCSVD::CoinBase,
            RSVD::BlockTimestamp => TCSVD::BlockTimestamp,
            RSVD::BlockNumber => TCSVD::BlockNumber,
            RSVD::Prevrandao => TCSVD::Prevrandao,
            RSVD::GasLimit => TCSVD::GasLimit,
            RSVD::ChainId => TCSVD::ChainId,
            RSVD::SelfBalance => TCSVD::SelfBalance,
            RSVD::BaseFee => TCSVD::BaseFee,
            RSVD::Gas => TCSVD::Gas,
            RSVD::Log { data, topics } => TCSVD::Log {
                data:   self.register_internal(data),
                topics: topics.into_iter().map(|t| self.register_internal(t)).collect(),
            },
            RSVD::Create { value, data } => TCSVD::Create {
                value: self.register_internal(value),
                data:  self.register_internal(data),
            },
            RSVD::Create2 { value, salt, data } => TCSVD::Create2 {
                value: self.register_internal(value),
                salt:  self.register_internal(salt),
                data:  self.register_internal(data),
            },
            RSVD::SelfDestruct { target } => TCSVD::SelfDestruct {
                target: self.register_internal(target),
            },
            RSVD::LessThan { left, right } => TCSVD::LessThan {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::GreaterThan { left, right } => TCSVD::GreaterThan {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::SignedLessThan { left, right } => TCSVD::SignedLessThan {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::SignedGreaterThan { left, right } => TCSVD::SignedGreaterThan {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::Equals { left, right } => TCSVD::Equals {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::IsZero { number } => TCSVD::IsZero {
                number: self.register_internal(number),
            },
            RSVD::And { left, right } => TCSVD::And {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::Or { left, right } => TCSVD::Or {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::Xor { left, right } => TCSVD::Xor {
                left:  self.register_internal(left),
                right: self.register_internal(right),
            },
            RSVD::Not { value } => TCSVD::Not {
                value: self.register_internal(value),
            },
            RSVD::LeftShift { shift, value } => TCSVD::LeftShift {
                shift: self.register_internal(shift),
                value: self.register_internal(value),
            },
            RSVD::RightShift { shift, value } => TCSVD::RightShift {
                shift: self.register_internal(shift),
                value: self.register_internal(value),
            },
            RSVD::ArithmeticRightShift { shift, value } => TCSVD::ArithmeticRightShift {
                shift: self.register_internal(shift),
                value: self.register_internal(value),
            },
            RSVD::CallData { id, offset, size } => TCSVD::CallData {
                id,
                offset: self.register_internal(offset),
                size: self.register_internal(size),
            },
            RSVD::CallDataSize => TCSVD::CallDataSize,
            RSVD::CodeCopy { offset, size } => TCSVD::CodeCopy {
                offset: self.register_internal(offset),
                size:   self.register_internal(size),
            },
            RSVD::ExtCodeSize { address } => TCSVD::ExtCodeSize {
                address: self.register_internal(address),
            },
            RSVD::ExtCodeCopy {
                address,
                offset,
                size,
            } => TCSVD::ExtCodeCopy {
                address: self.register_internal(address),
                offset:  self.register_internal(offset),
                size:    self.register_internal(size),
            },
            RSVD::ReturnData { offset, size } => TCSVD::ReturnData {
                offset: self.register_internal(offset),
                size:   self.register_internal(size),
            },
            RSVD::Return { data } => TCSVD::Return {
                data: self.register_internal(data),
            },
            RSVD::Revert { data } => TCSVD::Revert {
                data: self.register_internal(data),
            },
            RSVD::UnwrittenStorageValue { key } => TCSVD::UnwrittenStorageValue {
                key: self.register_internal(key),
            },
            RSVD::SLoad { key, value } => TCSVD::SLoad {
                key:   self.register_internal(key),
                value: self.register_internal(value),
            },
            RSVD::StorageWrite { key, value } => TCSVD::StorageWrite {
                key:   self.register_internal(key),
                value: self.register_internal(value),
            },
            RSVD::Concat { values } => TCSVD::Concat {
                values: values.into_iter().map(|v| self.register_internal(v)).collect(),
            },
            RSVD::MappingIndex {
                slot,
                key,
                projection,
            } => TCSVD::MappingIndex {
                slot: self.register_internal(slot),
                key: self.register_internal(key),
                projection,
            },
            RSVD::DynamicArrayIndex { slot, index } => TCSVD::DynamicArrayIndex {
                slot:  self.register_internal(slot),
                index: self.register_internal(index),
            },
            RSVD::SubWord {
                value,
                offset,
                size,
            } => TCSVD::SubWord {
                value: self.register_internal(value),
                offset,
                size,
            },
            RSVD::Shifted { offset, value } => TCSVD::Shifted {
                offset,
                value: self.register_internal(value),
            },
            RSVD::Packed { elements } => TCSVD::Packed {
                elements: elements
                    .into_iter()
                    .map(|e| {
                        let new_elem = self.register_internal(e.value);
                        PackedSpan::new(e.offset, e.size, new_elem)
                    })
                    .collect(),
            },
            RSVD::StorageSlot { key } => TCSVD::StorageSlot {
                key: self.register_internal(key),
            },
        };
        let type_var = self.tyvar_source.fresh();
        let new_value = TCSV::new(instruction_pointer, new_data, provenance, type_var);

        // Register the result
        self.expressions.entry(type_var).or_insert(new_value.clone());
        self.inferences.entry(type_var).or_insert(HashSet::new());

        if is_stable {
            self.stable_types.insert(value, new_value.clone());
        }

        // Return the type variable
        new_value
    }

    /// Adds the provided `expression` to the typing expressions for the
    /// provided type `variable`.
    ///
    /// It is valid for a judgement to be added multiple times, as any
    /// duplicates will be trivially unified.
    ///
    /// # Panics
    ///
    /// If `variable` does not exist in the typing state. This is only possible
    /// through use of `unsafe` operations to violate the invariants of the
    /// typing state.
    pub fn infer(
        &mut self,
        variable: impl Into<TypeVariable>,
        expression: impl Into<TypeExpression>,
    ) {
        let variable = variable.into();
        let expression = expression.into();

        // If it is an equality we want to make it symmetric so we add it to both sets
        if let TE::Equal { id } = &expression {
            if id == &variable {
                return;
            }
            self.inferences.get_mut(id).unwrap().insert(TE::eq(variable));
        }

        // This is safe to unwrap as the only source of new type variables is the `add`
        // method above, and so we know it will exist.
        self.inferences.get_mut(&variable).unwrap().insert(expression);
    }

    /// Adds the provided `expression` to the typing expressions for each of the
    /// provided type `variables`.
    ///
    /// # Panics
    ///
    /// If any of the `variables` do not exist in the typing state. This is only
    /// possible through use of `unsafe` operations to violate the invariants of
    /// the typing state.
    pub fn infer_many<const N: usize>(
        &mut self,
        variables: [impl Into<TypeVariable>; N],
        expression: impl Into<TypeExpression>,
    ) {
        let expression = expression.into();
        variables.into_iter().for_each(|v| self.infer(v, expression.clone()));
    }

    /// Adds the provided `expression` to the typing expressions for the
    /// `variable` associated with the provided `value`, returning the
    /// associated type variable.
    ///
    /// If `value` has no associated variable, it is registered in the state.
    pub fn infer_for(
        &mut self,
        value: &TCBoxedVal,
        expression: impl Into<TypeExpression>,
    ) -> TypeVariable {
        let var = value.type_var();
        self.infer(var, expression);
        var
    }

    /// Adds the provided `expression` to the typing expressions for the
    /// `variable` associated with each of the `values`, returning the
    /// associated type variable.
    ///
    /// It is guaranteed that the type variables are returned in the order
    /// corresponding to the `values`.
    ///
    /// If any one `value` has no associated variable, it is registered in the
    /// state.
    #[allow(clippy::missing_panics_doc)] // Panics are guarded
    pub fn infer_for_many<const N: usize>(
        &mut self,
        values: [&TCBoxedVal; N],
        expression: impl Into<TypeExpression>,
    ) -> [TypeVariable; N] {
        let mut iterator = values.into_iter();
        let expression = expression.into();
        array::from_fn(|_| {
            self.infer_for(
                iterator
                    .next()
                    .expect("The number of values should always be the same"),
                expression.clone(),
            )
        })
    }

    /// Gets the typing expressions associated with the provided type
    /// `variable`.
    ///
    /// # Panics
    ///
    /// If `variable` does not have associated inferences. This is only possible
    /// through use of `unsafe` operations to violate the invariants of the
    /// typing state.
    #[must_use]
    pub fn inferences(&self, variable: impl Into<TypeVariable>) -> &InferenceSet {
        let variable = variable.into();
        // This is safe to unwrap as the only source of new type variables is the `add`
        // method above, and so we know it will exist.
        self.inferences.get(&variable).unwrap()
    }

    /// Gets the typing expressions associated with the provided type
    /// `variable`.
    ///
    /// # Panics
    ///
    /// If `variable` does not have associated inferences. This is only possible
    /// through use of `unsafe` operations to violate the invariants of the
    /// typing state.
    #[must_use]
    pub fn inferences_cloned(&self, variable: impl Into<TypeVariable>) -> InferenceSet {
        let variable = variable.into();
        // This is safe to unwrap as the only source of new type variables is the `add`
        // method above, and so we know it will exist.
        self.inferences.get(&variable).unwrap().iter().cloned().collect()
    }

    /// Sets the inferences for `variable` to be `inferences`.
    ///
    /// # Safety
    ///
    /// You must only use this method if you are sure that you no longer want
    /// the inference information that you are replacing.
    pub unsafe fn set_inferences(
        &mut self,
        variable: impl Into<TypeVariable>,
        inferences: InferenceSet,
    ) {
        let variable = variable.into();
        self.inferences.insert(variable, inferences);
    }

    /// Gets the typing expressions associated with the provided type
    /// `variable`.
    ///
    /// # Panics
    ///
    /// If `variable` does not have associated inferences. This is only possible
    /// through use of `unsafe` operations to violate the invariants of the
    /// typing state.
    #[must_use]
    pub fn inferences_mut(&mut self, variable: impl Into<TypeVariable>) -> &mut InferenceSet {
        let variable = variable.into();
        // This is safe to unwrap as the only source of new type variables is the `add`
        // method above, and so we know it will exist.
        self.inferences.get_mut(&variable).unwrap()
    }

    /// Gets the type variable associated with a value, if it exists, returning
    /// [`None`] otherwise.
    #[must_use]
    pub fn var(&self, value: &TCBoxedVal) -> Option<TypeVariable> {
        Some(value.type_var())
    }

    /// Gets the type variable associated with `value`, or panics if the typing
    /// state does not know about `value`.
    ///
    /// To be used when you know that `value` exists in the typing state.
    ///
    /// # Panics
    ///
    /// If `value` does not have an associated variable. This is only possible
    /// through use of `unsafe` operations to violate the invariants of the
    /// typing state.
    #[must_use]
    pub fn var_unchecked(&self, value: &TCBoxedVal) -> TypeVariable {
        value.type_var()
    }

    /// Gets the value associated with a type variable, if it exists, returning
    /// [`None`] otherwise.
    ///
    /// # Sources of Type Variables
    ///
    /// While the typing state is the only source of type variables, it is
    /// possible to [`Self::clear`] the typing state, and hence have type
    /// variables that are no longer valid.
    ///
    /// In the vast majority of cases—as long as you know that you will not be
    /// querying with invalid type variables—you can instead use
    /// [`Self::value_unchecked`].
    #[must_use]
    pub fn value(&self, variable: impl Into<TypeVariable>) -> Option<&TCBoxedVal> {
        let variable = variable.into();
        self.expressions.get(&variable)
    }

    /// Gets the value associated with the type `variable`, or panics if the
    /// typing state has no such `variable`.
    ///
    /// To be used when you know that `value` exists in the typing state.
    ///
    /// # Panics
    ///
    /// If `variable` does not have an associated value. This is only possible
    /// through use of `unsafe` operations to violate the invariants of the
    /// typing state.
    #[must_use]
    pub fn value_unchecked(&self, variable: impl Into<TypeVariable>) -> &TCBoxedVal {
        let variable = variable.into();
        self.value(variable).unwrap()
    }

    /// Gets all of the values that are registered with the unifier state.
    #[must_use]
    pub fn values(&self) -> Vec<&TCBoxedVal> {
        self.expressions.values().collect()
    }

    /// Gets all of the type variables that are registered with the unifier
    /// state.
    #[must_use]
    pub fn variables(&self) -> Vec<TypeVariable> {
        self.inferences.keys().copied().collect()
    }

    /// Gets the pairs of `(type_var, value)` from the state of the unifier.
    #[must_use]
    pub fn pairs(&self) -> Vec<(TypeVariable, &TCBoxedVal)> {
        self.expressions.iter().map(|(t, v)| (*t, v)).collect()
    }

    /// Gets the pairs of `(type_var, value)` from the state of the unifier.
    #[must_use]
    pub fn pairs_cloned(&self) -> Vec<(TypeVariable, TCBoxedVal)> {
        self.expressions.iter().map(|(t, v)| (*t, v.clone())).collect()
    }

    /// Gets the result of running unification.
    ///
    /// As all operations on a [`UnificationForest`] require it being mutable,
    /// we only provide a mutable accessor.
    pub fn result(&mut self) -> &mut UnificationForest {
        &mut self.unification_result
    }

    /// Gets the result of running unification.
    pub fn set_result(&mut self, result: UnificationForest) {
        self.unification_result = result;
    }

    /// Gets the number of type variables that have been allocated in this
    /// state.
    #[must_use]
    pub fn tyvar_count(&self) -> usize {
        self.tyvar_source.allocated_count()
    }

    /// Clears the unifier state entirely.
    ///
    /// # Safety
    ///
    /// This function throws away all of the state for the unifier, which is
    /// rarely what you want. Make sure you understand the implications of doing
    /// so when calling this function.
    pub unsafe fn clear(&mut self) {
        self.expressions.clear();
        self.inferences.clear();
        self.unification_result = UnificationForest::new();
    }
}

impl Default for TypeCheckerState {
    fn default() -> Self {
        Self::empty()
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use crate::{
        tc::{
            expression::{TypeExpression, TE},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV},
    };

    #[test]
    fn can_add_expression_for_type_variable() {
        let mut state = TypeCheckerState::empty();
        let value = RSV::new_value(0, Provenance::Synthetic);
        let type_variable = state.register(value);

        let expression = TypeExpression::bytes(None);
        state.infer(type_variable, expression.clone());

        assert_eq!(
            state.inferences(type_variable),
            &HashSet::from([expression.clone()])
        );
        assert_eq!(
            state.inferences_mut(type_variable),
            &HashSet::from([expression])
        );
    }

    #[test]
    fn can_get_type_variable_for_value() {
        let mut state = TypeCheckerState::empty();
        let value = RSV::new_value(0, Provenance::Synthetic);
        let type_variable = state.register(value.clone());
        let tc_value = state.value_unchecked(type_variable).clone();

        assert_eq!(state.var(&tc_value), Some(type_variable));
    }

    #[test]
    fn can_get_value_for_type_variable() {
        let mut state = TypeCheckerState::empty();
        let value = RSV::new_value(0, Provenance::Synthetic);
        let variable_ty_var = state.register(value.clone());
        let tc_value = state.value_unchecked(variable_ty_var).clone();

        assert_eq!(state.value(variable_ty_var), Some(&tc_value));
    }

    #[test]
    fn can_get_all_values_and_variables() {
        let mut state = TypeCheckerState::empty();
        let value_1 = RSV::new_value(0, Provenance::Synthetic);
        let value_2 = RSV::new_value(0, Provenance::Synthetic);
        let type_variable_1 = state.register(value_1.clone());
        let type_variable_2 = state.register(value_2.clone());
        let tc_value_1 = state.value_unchecked(type_variable_1).clone();
        let tc_value_2 = state.value_unchecked(type_variable_2).clone();

        let values = state.values();
        assert!(values.contains(&&tc_value_1));
        assert!(values.contains(&&tc_value_2));

        let variables = state.variables();
        assert!(variables.contains(&type_variable_1));
        assert!(variables.contains(&type_variable_2));
    }

    #[test]
    fn makes_equalities_symmetric_by_construction() {
        let mut state = TypeCheckerState::empty();
        let value_1 = RSV::new_value(0, Provenance::Synthetic);
        let value_2 = RSV::new_value(0, Provenance::Synthetic);
        let type_variable_1 = state.register(value_1);
        let type_variable_2 = state.register(value_2);

        // Add an equality
        state.infer(type_variable_1, TE::eq(type_variable_2));

        // Check the results
        assert!(state.inferences(type_variable_1).contains(&TE::eq(type_variable_2)));
        assert!(state.inferences(type_variable_2).contains(&TE::eq(type_variable_1)));
    }
}
