//! This module contains the definition of the unifier state and other
//! supporting types.

use std::collections::{HashMap, HashSet, VecDeque};

use bimap::BiMap;
use uuid::Uuid;

use crate::{
    unifier::expression::{InferenceSet, TypeExpression, TE},
    vm::value::BoxedVal,
};

/// The internal state of the unifier, used to track modifications to typing
/// judgements as it runs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypingState {
    /// A mapping from symbolic values (which may be children of other symbolic
    /// values) to their corresponding type variables.
    ///
    /// This mapping is bijective as there should be a bijection between
    /// and type variables.
    expressions_and_vars: BiMap<BoxedVal, TypeVariable>,

    /// A mapping from type variables to their corresponding typing judgements.
    inferences: HashMap<TypeVariable, InferenceSet>,
}

impl TypingState {
    /// Constructs a new, empty state for the unifier.
    pub fn empty() -> Self {
        let expressions_and_vars = BiMap::new();
        let inferences = HashMap::new();
        Self {
            expressions_and_vars,
            inferences,
        }
    }

    /// Registers a symbolic `value` in the state, returning the associated type
    /// variable.
    ///
    /// If `value` already exists in the state, then the existing type variable
    /// is returned. If not, a fresh type variable is associated with the value
    /// and returned.
    pub fn register(&mut self, value: BoxedVal) -> TypeVariable {
        match self.expressions_and_vars.get_by_left(&value) {
            Some(v) => *v,
            None => {
                let type_var = TypeVariable::fresh();
                self.expressions_and_vars.insert(value, type_var);
                self.inferences.entry(type_var).or_insert(HashSet::new());
                type_var
            }
        }
    }

    /// Adds the provided `expression` to the typing expressions for the
    /// provided type `variable`.
    ///
    /// It is valid for a judgement to be added multiple times.
    pub fn infer(&mut self, variable: TypeVariable, expression: impl Into<TypeExpression>) {
        // This is safe to unwrap as the only source of new type variables is the `add`
        // method above, and so we know it will exist.
        self.inferences.get_mut(&variable).unwrap().insert(expression.into());
    }

    /// Gets the typing expressions associated with the provided type
    /// `variable`.
    pub fn inferences(&self, variable: TypeVariable) -> &InferenceSet {
        // This is safe to unwrap as the only source of new type variables is the `add`
        // method above, and so we know it will exist.
        self.inferences.get(&variable).unwrap()
    }

    /// Gets the typing expressions associated with the provided type
    /// `variable`.
    pub fn inferences_cloned(&self, variable: TypeVariable) -> InferenceSet {
        self.inferences.get(&variable).unwrap().iter().cloned().collect()
    }

    /// Gets the typing expressions associated with the provided type
    /// `variable`.
    pub fn inferences_mut(&mut self, variable: TypeVariable) -> &mut InferenceSet {
        // This is safe to unwrap as the only source of new type variables is the `add`
        // method above, and so we know it will exist.
        self.inferences.get_mut(&variable).unwrap()
    }

    /// Gets the transitive closure of inferences made about `variable` by
    /// following equality links.
    pub fn transitive_inferences(&self, variable: TypeVariable) -> InferenceSet {
        let mut inferences = InferenceSet::new();
        let mut seen_tyvars = HashSet::new();
        let mut tyvar_queue = VecDeque::new();

        tyvar_queue.push_back(variable);

        while let Some(tv) = tyvar_queue.pop_front() {
            let tv_inferences = self.inferences(tv);

            // Grab all the equalities from the current set of inferences
            let equalities: Vec<TypeVariable> = tv_inferences
                .iter()
                .flat_map(|inference| {
                    if let TE::Equal { id } = inference {
                        vec![*id]
                    } else {
                        vec![]
                    }
                })
                .collect();
            let non_equalities: Vec<TypeExpression> = tv_inferences
                .iter()
                .filter(|i| !matches!(i, TE::Equal { .. }))
                .cloned()
                .collect();

            inferences.extend(non_equalities);

            // Add to the queue as long as we've not seen it before
            equalities.iter().for_each(|eq| {
                if !seen_tyvars.contains(eq) {
                    tyvar_queue.push_back(*eq);
                }
            });

            // Mark the current type var as seen so we don't process it again
            seen_tyvars.insert(tv);
        }

        inferences
    }

    /// Gets the type variable associated with a value, if it exists, returning
    /// [`None`] otherwise.
    pub fn var(&self, value: &BoxedVal) -> Option<TypeVariable> {
        self.expressions_and_vars.get_by_left(value).cloned()
    }

    /// Gets the type variable associated with `value`, or panics if the typing
    /// state does not know about `value`.
    ///
    /// To be used when you know that `value` exists in the typing state.
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
    pub fn value(&self, variable: TypeVariable) -> Option<&BoxedVal> {
        self.expressions_and_vars.get_by_right(&variable)
    }

    /// Gets the value associated with the type `variable`, or panics if the
    /// typing state has no such `variable`.
    ///
    /// To be used when you know that `value` exists in the typing state.
    pub fn value_unchecked(&self, variable: TypeVariable) -> &BoxedVal {
        self.value(variable).unwrap()
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

    /// Gets the pairs of `(value, type_var)` from the state of the unifier.
    pub fn pairs(&self) -> Vec<(&BoxedVal, TypeVariable)> {
        self.expressions_and_vars.iter().map(|(v, t)| (v, *t)).collect()
    }

    /// Gets the pairs of `(value, type_var)` from the state of the unifier.
    pub fn pairs_cloned(&self) -> Vec<(BoxedVal, TypeVariable)> {
        self.expressions_and_vars
            .iter()
            .map(|(v, t)| (v.clone(), *t))
            .collect()
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

impl Default for TypingState {
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
    /// It is intended _only_ to be called from the [`TypingState::register`] as
    /// there should be no other way to construct a fresh type variable.
    fn fresh() -> Self {
        let id = Uuid::new_v4();
        Self { id }
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use crate::{
        unifier::{
            expression::TypeExpression,
            state::{TypeVariable, TypingState},
        },
        vm::value::{Provenance, SymbolicValue},
    };

    #[test]
    fn can_create_fresh_type_variable() {
        TypeVariable::fresh();
    }

    #[test]
    fn can_add_expression_for_type_variable() {
        let mut state = TypingState::empty();
        let value = SymbolicValue::new_value(0, Provenance::Synthetic);
        let type_variable = state.register(value);

        let expression = TypeExpression::word(None, None);
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
        let mut state = TypingState::empty();
        let value = SymbolicValue::new_value(0, Provenance::Synthetic);
        let type_variable = state.register(value.clone());

        assert_eq!(state.var(&value), Some(type_variable));
    }

    #[test]
    fn can_get_value_for_type_variable() {
        let mut state = TypingState::empty();
        let value = SymbolicValue::new_value(0, Provenance::Synthetic);
        let variable_ty_var = state.register(value.clone());

        assert_eq!(state.value(variable_ty_var), Some(&value));
    }

    #[test]
    fn can_get_all_values_and_variables() {
        let mut state = TypingState::empty();
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
}
