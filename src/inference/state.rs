//! This module contains the definition of the inference engine state and other
//! supporting types.

use std::{
    array,
    collections::{HashMap, HashSet},
};

use bimap::BiMap;
use uuid::Uuid;

use crate::{
    inference::{
        expression::{InferenceSet, TypeExpression, TE},
        unification::UnificationForest,
    },
    vm::value::BoxedVal,
};

/// The internal state of the inference engine, used to track modifications to
/// typing judgements as it runs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InferenceState {
    /// A mapping from symbolic values (which may be children of other symbolic
    /// values) to their corresponding type variables.
    ///
    /// This mapping is bijective as there should be a bijection between
    /// and type variables.
    expressions_and_vars: BiMap<BoxedVal, TypeVariable>,

    /// A mapping from type variables to their corresponding typing judgements.
    inferences: HashMap<TypeVariable, InferenceSet>,

    /// The results of running unification.
    ///
    /// This may be empty if the process has not yet reached the correct place.
    unification_result: UnificationForest,
}

impl InferenceState {
    /// Constructs a new, empty inference state.
    #[must_use]
    pub fn empty() -> Self {
        let expressions_and_vars = BiMap::new();
        let inferences = HashMap::new();
        let unification_result = UnificationForest::new();
        Self {
            expressions_and_vars,
            inferences,
            unification_result,
        }
    }

    /// Registers a symbolic `value` in the state, returning the associated type
    /// variable.
    ///
    /// If `value` already exists in the state, then the existing type variable
    /// is returned. If not, a fresh type variable is associated with the value
    /// and returned.
    pub fn register(&mut self, value: BoxedVal) -> TypeVariable {
        if let Some(v) = self.expressions_and_vars.get_by_left(&value) {
            *v
        } else {
            let type_var = TypeVariable::fresh();
            self.expressions_and_vars.insert(value, type_var);
            self.inferences.entry(type_var).or_insert(HashSet::new());
            type_var
        }
    }

    /// Registers a symbolic `values` in the state, returning the associated
    /// type variables in the corresponding order.
    ///
    /// If any one `value` already exists in the state, then the existing type
    /// variable is returned. If not, a fresh type variable is associated
    /// with the value and returned.
    #[must_use]
    pub fn register_many<const N: usize>(&mut self, values: [BoxedVal; N]) -> [TypeVariable; N] {
        let mut iterator = values.into_iter();
        array::from_fn(|_| {
            self.register(
                iterator
                    .next()
                    .expect("The number of values should always be the same"),
            )
        })
    }

    /// Adds the provided `expression` to the typing expressions for the
    /// provided type `variable`.
    ///
    /// It is valid for a judgement to be added multiple times, as any
    /// duplicates will be trivially collapsed.
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
        value: &BoxedVal,
        expression: impl Into<TypeExpression>,
    ) -> TypeVariable {
        let var = self.register(value.clone());
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
    pub fn infer_for_many<const N: usize>(
        &mut self,
        values: [&BoxedVal; N],
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
    pub fn var(&self, value: &BoxedVal) -> Option<TypeVariable> {
        self.expressions_and_vars.get_by_left(value).copied()
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
    pub fn var_unchecked(&self, value: &BoxedVal) -> TypeVariable {
        self.var(value).unwrap()
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
    pub fn value(&self, variable: impl Into<TypeVariable>) -> Option<&BoxedVal> {
        let variable = variable.into();
        self.expressions_and_vars.get_by_right(&variable)
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
    pub fn value_unchecked(&self, variable: impl Into<TypeVariable>) -> &BoxedVal {
        let variable = variable.into();
        self.value(variable).unwrap()
    }

    /// Gets all of the values that are registered with the unifier state.
    #[must_use]
    pub fn values(&self) -> Vec<&BoxedVal> {
        self.expressions_and_vars.left_values().collect()
    }

    /// Gets all of the type variables that are registered with the unifier
    /// state.
    #[must_use]
    pub fn variables(&self) -> Vec<TypeVariable> {
        self.expressions_and_vars.right_values().copied().collect()
    }

    /// Gets the pairs of `(value, type_var)` from the state of the unifier.
    #[must_use]
    pub fn pairs(&self) -> Vec<(&BoxedVal, TypeVariable)> {
        self.expressions_and_vars.iter().map(|(v, t)| (v, *t)).collect()
    }

    /// Gets the pairs of `(value, type_var)` from the state of the unifier.
    #[must_use]
    pub fn pairs_cloned(&self) -> Vec<(BoxedVal, TypeVariable)> {
        self.expressions_and_vars
            .iter()
            .map(|(v, t)| (v.clone(), *t))
            .collect()
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

    /// Clears the unifier state entirely.
    ///
    /// # Safety
    ///
    /// This function throws away all of the state for the unifier, which is
    /// rarely what you want. Make sure you understand the implications of doing
    /// so when calling this function.
    pub unsafe fn clear(&mut self) {
        self.expressions_and_vars.clear();
        self.inferences.clear();
    }
}

impl Default for InferenceState {
    fn default() -> Self {
        Self::empty()
    }
}

/// A type variable represents the possibly-unbound type of an expression.
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypeVariable {
    id: Uuid,
}

impl TypeVariable {
    /// Creates a new, never-before-seen type variable.
    ///
    /// It is intended _only_ to be called from the [`InferenceState::register`]
    /// as there should be no other way to construct a fresh type variable and
    /// it is unsafe to do so.
    #[must_use]
    fn fresh() -> Self {
        let id = Uuid::new_v4();
        Self { id }
    }

    /// Constructs a new, never-before-seen type variable.
    ///
    /// # Safety
    ///
    /// Calling `new` allows violation of the invariant that the
    /// [`InferenceState`] is the only component that can construct new type
    /// variables. If you call this function, you must be _very_ careful to
    /// ensure that none of its results are passed to functions in that state.
    #[must_use]
    pub unsafe fn new() -> Self {
        Self::fresh()
    }
}

impl From<&TypeVariable> for TypeVariable {
    fn from(value: &TypeVariable) -> Self {
        *value
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use crate::{
        inference::{
            expression::{TypeExpression, TE},
            state::{InferenceState, TypeVariable},
        },
        vm::value::{Provenance, SymbolicValue},
    };

    #[test]
    fn can_create_fresh_type_variable() {
        let _ = TypeVariable::fresh();
    }

    #[test]
    fn can_add_expression_for_type_variable() {
        let mut state = InferenceState::empty();
        let value = SymbolicValue::new_value(0, Provenance::Synthetic);
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
        let mut state = InferenceState::empty();
        let value = SymbolicValue::new_value(0, Provenance::Synthetic);
        let type_variable = state.register(value.clone());

        assert_eq!(state.var(&value), Some(type_variable));
    }

    #[test]
    fn can_get_value_for_type_variable() {
        let mut state = InferenceState::empty();
        let value = SymbolicValue::new_value(0, Provenance::Synthetic);
        let variable_ty_var = state.register(value.clone());

        assert_eq!(state.value(variable_ty_var), Some(&value));
    }

    #[test]
    fn can_get_all_values_and_variables() {
        let mut state = InferenceState::empty();
        let value_1 = SymbolicValue::new_value(0, Provenance::Synthetic);
        let value_2 = SymbolicValue::new_value(0, Provenance::Synthetic);
        let type_variable_1 = state.register(value_1.clone());
        let type_variable_2 = state.register(value_2.clone());

        let values = state.values();
        assert!(values.contains(&&value_1));
        assert!(values.contains(&&value_2));

        let variables = state.variables();
        assert!(variables.contains(&type_variable_1));
        assert!(variables.contains(&type_variable_2));
    }

    #[test]
    fn makes_equalities_symmetric_by_construction() {
        let mut state = InferenceState::empty();
        let value_1 = SymbolicValue::new_value(0, Provenance::Synthetic);
        let value_2 = SymbolicValue::new_value(0, Provenance::Synthetic);
        let type_variable_1 = state.register(value_1);
        let type_variable_2 = state.register(value_2);

        // Add an equality
        state.infer(type_variable_1, TE::eq(type_variable_2));

        // Check the results
        assert!(state.inferences(type_variable_1).contains(&TE::eq(type_variable_2)));
        assert!(state.inferences(type_variable_2).contains(&TE::eq(type_variable_1)));
    }
}
