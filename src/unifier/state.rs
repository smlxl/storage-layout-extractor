//! This module contains the definition of the unifier state and other
//! supporting types.

use std::collections::HashMap;

use bimap::BiMap;
use uuid::Uuid;

use crate::{
    unifier::expression::{TypeExprVec, TypeExpression},
    vm::value::BoxedVal,
};

/// The internal state of the unifier, used to track modifications to typing
/// judgements as it runs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnifierState {
    /// A mapping from symbolic values (which may be children of other symbolic
    /// values) to their corresponding type variables.
    ///
    /// This mapping is bijective as there should be a bijection between
    /// and type variables.
    expressions_and_vars: BiMap<BoxedVal, TypeVariable>,

    /// A mapping from type variables to their corresponding typing judgements.
    type_expressions: HashMap<TypeVariable, TypeExprVec>,
}

impl UnifierState {
    /// Constructs a new, empty state for the unifier.
    pub fn new() -> Self {
        let expressions_and_vars = BiMap::new();
        let type_expressions = HashMap::new();
        Self {
            expressions_and_vars,
            type_expressions,
        }
    }

    /// Adds a symbolic `value` to the state, associating a fresh type variable
    /// with it.
    ///
    /// If `value` already exists in the state, then the existing type variable
    /// is returned. If not, a fresh type variable is associated with the value
    /// and returned.
    pub fn add(&mut self, value: BoxedVal) -> TypeVariable {
        match self.expressions_and_vars.get_by_left(&value) {
            Some(v) => *v,
            None => {
                let type_var = TypeVariable::fresh();
                self.expressions_and_vars.insert(value, type_var);
                self.type_expressions.entry(type_var).or_insert(vec![]);
                type_var
            }
        }
    }

    /// Adds the provided `expression` to the typing expressions for the
    /// provided type `variable`.
    ///
    /// It is valid for a judgement to occur multiple times.
    pub fn add_expression(&mut self, variable: &TypeVariable, expression: TypeExpression) {
        // This is safe to unwrap as the only source of new type variables is the `add`
        // method above, and so we know it will exist.
        self.type_expressions.get_mut(variable).unwrap().push(expression);
    }

    /// Gets the typing expressions associated with the provided type
    /// `variable`.
    pub fn expressions(&self, variable: &TypeVariable) -> &TypeExprVec {
        // This is safe to unwrap as the only source of new type variables is the `add`
        // method above, and so we know it will exist.
        self.type_expressions.get(variable).unwrap()
    }

    /// Gets the typing judgements associated with the provided type `variable`.
    pub fn expressions_mut(&mut self, variable: &TypeVariable) -> &mut TypeExprVec {
        // This is safe to unwrap as the only source of new type variables is the `add`
        // method above, and so we know it will exist.
        self.type_expressions.get_mut(variable).unwrap()
    }

    /// Gets the type variable associated with a value, if it exists, returning
    /// [`None`] otherwise.
    pub fn var_for_value(&self, value: &BoxedVal) -> Option<TypeVariable> {
        self.expressions_and_vars.get_by_left(value).cloned()
    }

    /// Gets the value associated with a type variable, if it exists, returning
    /// [`None`] otherwise.
    pub fn value_for_var(&self, variable: &TypeVariable) -> Option<&BoxedVal> {
        self.expressions_and_vars.get_by_right(variable)
    }

    /// Gets all of the values that are registered with the unifier state.
    pub fn values(&self) -> Vec<&BoxedVal> {
        self.expressions_and_vars.left_values().collect()
    }

    /// Gets all of the type variables that are registered with the unifier
    /// state.
    pub fn variables(&self) -> Vec<TypeVariable> {
        self.expressions_and_vars.right_values().copied().collect()
    }
}

impl Default for UnifierState {
    fn default() -> Self {
        Self::new()
    }
}

/// A type variable represents the possibly-unbound type of an expression.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct TypeVariable {
    id: Uuid,
}

impl TypeVariable {
    /// Creates a new, never-before-seen type variable.
    ///
    /// It is intended _only_ to be called from the [`UnifierState::add`] as
    /// there should be no other way to construct a fresh type variable.
    fn fresh() -> Self {
        let id = Uuid::new_v4();
        Self { id }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        unifier::{
            expression::TypeExpression,
            state::{TypeVariable, UnifierState},
        },
        vm::value::{Provenance, SymbolicValue},
    };

    #[test]
    fn can_create_fresh_type_variable() {
        TypeVariable::fresh();
    }

    #[test]
    fn can_add_expression_for_type_variable() {
        let mut state = UnifierState::new();
        let value = SymbolicValue::new_value(0, Provenance::Synthetic);
        let type_variable = state.add(value);

        let expression = TypeExpression::default_word();
        state.add_expression(&type_variable, expression.clone());

        assert_eq!(state.expressions(&type_variable), &vec![expression.clone()]);
        assert_eq!(state.expressions_mut(&type_variable), &vec![expression]);
    }

    #[test]
    fn can_get_type_variable_for_value() {
        let mut state = UnifierState::new();
        let value = SymbolicValue::new_value(0, Provenance::Synthetic);
        let type_variable = state.add(value.clone());

        assert_eq!(state.var_for_value(&value), Some(type_variable));
    }

    #[test]
    fn can_get_value_for_type_variable() {
        let mut state = UnifierState::new();
        let value = SymbolicValue::new_value(0, Provenance::Synthetic);
        let variable_ty_var = state.add(value.clone());

        assert_eq!(state.value_for_var(&variable_ty_var), Some(&value));
    }

    #[test]
    fn can_get_all_values_and_variables() {
        let mut state = UnifierState::new();
        let value_1 = SymbolicValue::new_value(0, Provenance::Synthetic);
        let value_2 = SymbolicValue::new_value(0, Provenance::Synthetic);
        let type_variable_1 = state.add(value_1.clone());
        let type_variable_2 = state.add(value_2.clone());

        let values = state.values();
        assert!(values.contains(&&value_1));
        assert!(values.contains(&&value_2));

        let variables = state.variables();
        assert!(variables.contains(&type_variable_1));
        assert!(variables.contains(&type_variable_2));
    }
}
