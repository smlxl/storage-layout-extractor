//! This module contains functionality for performing unification of inferences.
//!
//! It is split off from the primary [`super::Unifier`] itself to enable re-use
//! of the functionality elsewhere, and also enable easier testing without
//! needing to spool up the entire unifier.

pub mod data;
use std::collections::{HashSet, VecDeque};

use crate::unifier::{
    expression::{InferenceSet, TypeExpression, TE},
    state::{TypeVariable, TypingState},
    unification::data::DisjointSet,
};

/// The concrete type of the [`DisjointSet`] data structure used for type
/// inference and unification.
pub type UnificationForest = DisjointSet<TypeVariable, InferenceSet>;

/// Performs unification to resolve the most-concrete type for all type
/// variables in the typing `state`, writing the unification result into the
/// state.
///
/// This may result in [`TE::Conflict`]s occurring in the result forest.
pub fn unify(state: &mut TypingState) {
    // First we have to create our forest.
    let mut forest = UnificationForest::new();

    // Populating it first inserts all variables into the forest.
    for var in state.variables() {
        forest.insert(var);
    }

    // And then resolves all equalities by using the union operation to combine
    // possibly-disjoint sets to create inference sets.
    for type_var in state.variables() {
        for type_expr in state.inferences(type_var) {
            match type_expr {
                TypeExpression::Equal { id } => forest.union(&type_var, id),
                _ => forest.add_data(&type_var, HashSet::from([type_expr.clone()])),
            };
        }
    }

    // Then, we loop until we stop making progress.
    loop {
        // Create the set of new equalities.
        let mut all_equalities: HashSet<Equality> = HashSet::new();

        // Create our stop condition.
        let mut made_progress = false;

        for (ty_var, inferences) in forest.sets() {
            // If there are no inferences for this type variable, go to the next one.
            if inferences.is_empty() {
                continue;
            }

            // Get all of the inferences
            let mut inferred_expressions: VecDeque<_> = inferences.into_iter().collect();
            let mut current = inferred_expressions.pop_front().unwrap_or_else(|| {
                unreachable!("We know there is at least one item in the expressions queue")
            });

            // If there is more than one expression, this will execute, and fold over them
            for expression in inferred_expressions {
                made_progress = true;
                let Merge {
                    expression,
                    equalities,
                } = merge(current.clone(), expression);
                current = expression;
                all_equalities.extend(equalities);
            }

            // Finally, we have to update the forest's inferences for each type variable
            forest.set_data(&ty_var, InferenceSet::from([current]));
        }

        // When we get to the end of that loop, we need to compute the unions of
        // the variables with their new associated inferences
        for Equality { left, right } in all_equalities {
            forest.union(&left, &right);
        }

        // If we didn't make any progress at any point, then we end the loop as we are
        // done with unification
        if !made_progress {
            break;
        }
    }

    state.set_result(forest);
}

/// Combines `left` with `right` to produce a new type expression.
///
/// # Panics
///
/// This function will panic if passed a [`TE::Equal`] expression, as its
/// preconditions state that no such equalities should exist by the point of
/// unification.
#[allow(clippy::match_same_arms)] // The ordering of the arms matters
#[allow(clippy::too_many_lines)] // It needs to remain one function
#[must_use]
pub fn merge(left: TE, right: TE) -> Merge {
    // If they are equal there's no combining to do
    if left == right {
        return Merge::expression(left);
    }

    match (&left, &right) {
        // If equalities exist here we have an actual error as it indicates a likely bug in the
        // unifier
        (TE::Equal { .. }, _) => panic!(
            "Equalities should not exist when unifying, but found: {:?}",
            left.clone()
        ),
        (_, TE::Equal { .. }) => panic!(
            "Equalities should not exist when unifying, but found: {:?}",
            right.clone()
        ),

        // Combining a conflict with anything is just the conflict
        (TE::Conflict { .. }, _) => Merge::expression(left),
        (_, TE::Conflict { .. }) => Merge::expression(right),

        // Combining words with words is complex
        (
            TE::Word {
                width: width_l,
                signed: signed_l,
                usage: usage_l,
            },
            TE::Word {
                width: width_r,
                signed: signed_r,
                usage: usage_r,
            },
        ) => {
            // `and_then` and `map` don't work with Result, so we get this monstrosity
            let width = match (width_l, width_r) {
                (Some(l), Some(r)) if l == r => Some(*l),
                (Some(_), Some(_)) => {
                    return Merge::expression(TE::conflict(
                        left,
                        right,
                        "Disagreeing numeric widths",
                    ));
                }
                (Some(l), _) => Some(*l),
                (_, Some(r)) => Some(*r),
                (None, None) => None,
            };

            let signed = match (signed_l, signed_r) {
                (Some(l), Some(r)) if l == r => Some(*l),
                (Some(_), Some(_)) => {
                    return Merge::expression(TE::conflict(
                        left,
                        right,
                        "Disagreeing numeric signedness",
                    ));
                }
                (Some(l), _) => Some(*l),
                (_, Some(r)) => Some(*r),
                (None, None) => None,
            };

            Merge::expression(TE::word(
                width,
                signed,
                usage_l.clone().merge(usage_r.clone()),
            ))
        }

        // To combine a word with a dynamic array we delegate
        (TE::Word { .. }, TE::DynamicArray { .. }) => merge(right, left),

        // They produce a dynamic array as long as the word is not signed
        (TE::DynamicArray { .. }, TE::Word { signed, .. }) => Merge::expression(match signed {
            Some(false) | None => left,
            _ => TE::conflict(left, right, "An array cannot have signed length"),
        }),

        // Dynamic arrays can combine with dynamic arrays
        (TE::DynamicArray { element: element_l }, TE::DynamicArray { element: element_r }) => {
            let equalities = vec![Equality::new(*element_l, *element_r)];
            Merge::new(left, equalities)
        }

        // Fixed arrays can combine with fixed arrays
        (
            TE::FixedArray {
                element: element_l,
                length: length_l,
            },
            TE::FixedArray {
                element: element_r,
                length: length_r,
            },
        ) => {
            if length_l == length_r {
                let equalities = vec![Equality::new(*element_l, *element_r)];
                Merge::new(left, equalities)
            } else {
                Merge::expression(TE::conflict(
                    left,
                    right,
                    "Fixed arrays have different lengths",
                ))
            }
        }

        // Mappings can combine with mappings
        (
            TE::Mapping {
                key: key_l,
                value: value_l,
            },
            TE::Mapping {
                key: key_r,
                value: value_r,
            },
        ) => {
            // If we get here, the `key_l` and `key_r`, and `value_l` and `value_r` types
            // were compatible and their inferences have been updated
            let equalities = vec![
                Equality::new(*key_l, *key_r),
                Equality::new(*value_l, *value_r),
            ];
            Merge::new(left, equalities)
        }

        // Everything can combine with `Any` to produce itself, as Any doesn't add information, so
        // only collapses to `Any` when combined with itself
        (_, TE::Any) => Merge::expression(left),
        (TE::Any, _) => Merge::expression(right),

        // Nothing else can combine and be valid, so we error
        _ => Merge::expression(TE::conflict(left, right, "Incompatible inferences")),
    }
}

/// The result from executing [`merge`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Merge {
    /// The expression that results from combining `left` and `right`, which is
    /// possibly an evidence conflict.
    pub expression: TypeExpression,

    /// Any new equalities to solve that were created as part of combining
    /// `left` and `right`.
    pub equalities: Vec<Equality>,
}

impl Merge {
    /// Creates a new combine result from the provided `expression` and
    /// `equalities`.
    #[must_use]
    pub fn new(expression: TypeExpression, equalities: Vec<Equality>) -> Self {
        Self {
            expression,
            equalities,
        }
    }

    /// Creates a new combine result from the provided `expression`, with no
    /// equalities.
    #[must_use]
    pub fn expression(expression: TypeExpression) -> Self {
        let equalities = Vec::new();
        Self {
            expression,
            equalities,
        }
    }
}

/// A representation of a symmetrical equality between two type variables.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct Equality {
    pub left:  TypeVariable,
    pub right: TypeVariable,
}

impl Equality {
    /// Creates a new equality from `left` and `right`.
    #[must_use]
    pub fn new(left: TypeVariable, right: TypeVariable) -> Self {
        Self { left, right }
    }
}

#[cfg(test)]
mod test {
    use std::panic;

    use ethnum::U256;
    use itertools::Itertools;

    use crate::{
        constant::ADDRESS_WIDTH_BITS,
        unifier::{
            expression::{WordUse, TE},
            state::TypingState,
            unification::{merge, unify},
        },
        vm::value::{Provenance, SV},
    };

    #[test]
    fn panics_when_encountering_equality() {
        // Override the panic hook so we don't see output in tests
        panic::set_hook(Box::new(|_| {}));

        // Set up the state
        let mut state = TypingState::empty();
        let v_1 = SV::new_value(0, Provenance::Synthetic);
        let v_2 = SV::new_value(1, Provenance::Synthetic);
        state.register(v_1);
        let v_2_tv = state.register(v_2);

        // Set up some inferences
        let inference_1 = TE::eq(v_2_tv);
        let inference_2 = TE::default_word();

        // Check it does the right thing
        let result = panic::catch_unwind(|| merge(inference_1.clone(), inference_2.clone()));
        assert!(result.is_err());

        let result = panic::catch_unwind(|| merge(inference_2, inference_1));
        assert!(result.is_err());
    }

    #[test]
    fn can_infer_compatible_unsigned_words() {
        // Set up the state
        let mut state = TypingState::empty();
        let v_1 = SV::new_value(0, Provenance::Synthetic);
        let v_1_tv = state.register(v_1);

        // Set up some inferences
        let inference_1 = TE::unsigned_word(Some(ADDRESS_WIDTH_BITS));
        let inference_2 = TE::default_word();
        let inference_3 = TE::address();
        let inferences = vec![inference_1, inference_2, inference_3];
        let inference_permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that they combine properly, and produce the same result no matter the
        // order
        for permutation in inference_permutations {
            permutation.into_iter().for_each(|i| state.infer(v_1_tv, i.clone()));

            unify(&mut state);
            let result = util::get_inference(v_1_tv, state.result());

            assert!(result.is_some());
            assert_eq!(
                result.unwrap(),
                TE::word(Some(ADDRESS_WIDTH_BITS), Some(false), WordUse::Address)
            );
        }
    }

    #[test]
    fn can_infer_compatible_signed_words() {
        // Set up the state
        let mut state = TypingState::empty();
        let v_1 = SV::new_value(0, Provenance::Synthetic);
        let v_1_tv = state.register(v_1);

        // Set up some inferences
        let inference_1 = TE::signed_word(Some(64));
        let inference_2 = TE::default_word();
        let inference_3 = TE::bool();
        let inferences = vec![inference_1, inference_2, inference_3];
        let inference_permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that they combine properly, and produce the same result no matter the
        // order
        for permutation in inference_permutations {
            permutation.into_iter().for_each(|i| state.infer(v_1_tv, i.clone()));

            unify(&mut state);
            let result = util::get_inference(v_1_tv, state.result());

            assert!(result.is_some());
            assert_eq!(
                result.unwrap(),
                TE::word(Some(64), Some(true), WordUse::Bool)
            );
        }
    }

    #[test]
    fn conflicts_for_incompatible_word_evidence() {
        // Set up the state
        let mut state = TypingState::empty();
        let v_1 = SV::new_value(0, Provenance::Synthetic);
        let v_1_ty = state.register(v_1);

        // Set up some inferences
        let inference_1 = TE::signed_word(Some(64));
        let inference_2 = TE::signed_word(Some(128));
        let inferences = vec![inference_1, inference_2];
        let permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that they combine properly, and produce the same error no matter the
        // order
        for permutation in permutations {
            permutation.into_iter().for_each(|i| state.infer(v_1_ty, i.clone()));

            unify(&mut state);
            let result = util::get_inference(v_1_ty, state.result());

            assert!(result.is_some());
            assert!(matches!(result.unwrap(), TE::Conflict { .. }));
        }
    }

    #[test]
    fn can_infer_unsigned_word_with_dynamic_array() {
        // Set up the state
        let mut state = TypingState::empty();
        let array = SV::new_value(0, Provenance::Synthetic);
        let element = SV::new_value(0, Provenance::Synthetic);
        let array_tv = state.register(array);
        let element_tv = state.register(element);

        // Set up some inferences
        let inference_1 = TE::unsigned_word(Some(64));
        let inference_2 = TE::DynamicArray {
            element: element_tv,
        };
        let inferences = vec![inference_1, inference_2];
        let permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that they combine properly, and produce the same result no matter the
        // order
        for permutation in permutations {
            permutation.into_iter().for_each(|i| state.infer(array_tv, i.clone()));

            unify(&mut state);
            let result = util::get_inference(array_tv, state.result());

            assert!(result.is_some());
            assert_eq!(
                result.unwrap(),
                TE::DynamicArray {
                    element: element_tv,
                }
            );
        }
    }

    #[test]
    fn conflicts_for_signed_word_with_dynamic_array() {
        // Set up the state
        let mut state = TypingState::empty();
        let array = SV::new_value(0, Provenance::Synthetic);
        let element = SV::new_value(0, Provenance::Synthetic);
        let array_tv = state.register(array);
        let element_tv = state.register(element);

        // Set up some inferences
        let inference_1 = TE::signed_word(Some(64));
        let inference_2 = TE::DynamicArray {
            element: element_tv,
        };
        let inferences = vec![inference_1, inference_2];
        let permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that they combine properly, and produce the same result no matter the
        // order
        for permutation in permutations {
            permutation.into_iter().for_each(|i| state.infer(array_tv, i.clone()));

            unify(&mut state);
            let result = util::get_inference(array_tv, state.result());

            assert!(result.is_some());
            assert!(matches!(result.unwrap(), TE::Conflict { .. }));
        }
    }

    #[test]
    fn can_infer_dynamic_arrays_with_compatible_element_types() {
        // Set up the state
        let mut state = TypingState::empty();
        let array = SV::new_value(0, Provenance::Synthetic);
        let elem_1 = SV::new_value(0, Provenance::Synthetic);
        let elem_2 = SV::new_value(0, Provenance::Synthetic);
        let array_tv = state.register(array);
        let elem_1_tv = state.register(elem_1);
        let elem_2_tv = state.register(elem_2);

        // Create some inferences and register them
        let array_inference_1 = TE::DynamicArray { element: elem_1_tv };
        let array_inference_2 = TE::DynamicArray { element: elem_2_tv };
        let elem_inference_1 = TE::default_word();
        let elem_inference_2 = TE::signed_word(Some(64));
        state.infer(elem_1_tv, elem_inference_1);
        state.infer(elem_2_tv, elem_inference_2);
        let inferences = vec![array_inference_1, array_inference_2];
        let permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that we get the same result, and that they combine properly
        for permutation in permutations {
            // Register the array inferences in the state
            permutation.into_iter().for_each(|i| state.infer(array_tv, i.clone()));

            // Check the result is right
            unify(&mut state);
            let result = util::get_inference(array_tv, state.result());

            match result.unwrap() {
                TE::DynamicArray { element } => {
                    assert!(vec![elem_1_tv, elem_2_tv].contains(&element));
                }
                _ => panic!("Bad payload in result"),
            }
        }
    }

    #[test]
    fn conflicts_for_dynamic_arrays_with_incompatible_element_types() {
        // Set up the state
        let mut state = TypingState::empty();
        let array = SV::new_value(0, Provenance::Synthetic);
        let elem_1 = SV::new_value(0, Provenance::Synthetic);
        let elem_2 = SV::new_value(0, Provenance::Synthetic);
        let array_tv = state.register(array);
        let elem_1_tv = state.register(elem_1);
        let elem_2_tv = state.register(elem_2);

        // Create some inferences and register them
        let array_inference_1 = TE::DynamicArray { element: elem_1_tv };
        let array_inference_2 = TE::DynamicArray { element: elem_2_tv };
        let elem_inference_1 = TE::unsigned_word(None);
        let elem_inference_2 = TE::signed_word(Some(64));
        state.infer(elem_1_tv, elem_inference_1);
        state.infer(elem_2_tv, elem_inference_2);
        let inferences = vec![array_inference_1, array_inference_2];
        let permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that we get the same result, and that they combine properly
        for permutation in permutations {
            // Register the array inferences in the state
            permutation.into_iter().for_each(|i| state.infer(array_tv, i.clone()));

            // Check the array is right
            unify(&mut state);
            let result = util::get_inference(array_tv, state.result());

            match result.unwrap() {
                TE::DynamicArray { element } => {
                    assert!(vec![elem_1_tv, elem_2_tv].contains(&element));
                }
                _ => panic!("Bad payload in result"),
            }

            // But its element type should be a conflict
            let result = util::get_inference(elem_1_tv, state.result());
            assert!(matches!(result.unwrap(), TE::Conflict { .. }));
        }
    }

    #[test]
    fn can_infer_fixed_arrays_with_compatible_element_types() {
        // Set up the state
        let mut state = TypingState::empty();
        let array = SV::new_value(0, Provenance::Synthetic);
        let elem_1 = SV::new_value(0, Provenance::Synthetic);
        let elem_2 = SV::new_value(0, Provenance::Synthetic);
        let array_tv = state.register(array);
        let elem_1_tv = state.register(elem_1);
        let elem_2_tv = state.register(elem_2);
        let input_len = U256::from(7u64);

        // Create some inferences and register them
        let array_inference_1 = TE::FixedArray {
            element: elem_1_tv,
            length:  input_len,
        };
        let array_inference_2 = TE::FixedArray {
            element: elem_2_tv,
            length:  input_len,
        };
        let elem_inference_1 = TE::default_word();
        let elem_inference_2 = TE::signed_word(Some(64));
        state.infer(elem_1_tv, elem_inference_1);
        state.infer(elem_2_tv, elem_inference_2);
        let inferences = vec![array_inference_1, array_inference_2];
        let permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that we get the same result, and that they combine properly
        for permutation in permutations {
            // Register the array inferences in the state
            permutation.into_iter().for_each(|i| state.infer(array_tv, i.clone()));

            unify(&mut state);
            let result = util::get_inference(array_tv, state.result());

            // Check the result is right
            match result.unwrap() {
                TE::FixedArray { element, length } if length == input_len => {
                    assert!(vec![elem_1_tv, elem_2_tv].contains(&element));
                }
                _ => panic!("Bad payload in result"),
            }
        }
    }

    #[test]
    fn conflicts_for_fixed_arrays_with_incompatible_element_types() {
        // Set up the state
        let mut state = TypingState::empty();
        let array = SV::new_value(0, Provenance::Synthetic);
        let elem_1 = SV::new_value(0, Provenance::Synthetic);
        let elem_2 = SV::new_value(0, Provenance::Synthetic);
        let array_tv = state.register(array);
        let elem_1_tv = state.register(elem_1);
        let elem_2_tv = state.register(elem_2);
        let input_len = U256::from(7u64);

        // Create some inferences and register them
        let array_inference_1 = TE::FixedArray {
            element: elem_1_tv,
            length:  input_len,
        };
        let array_inference_2 = TE::FixedArray {
            element: elem_2_tv,
            length:  input_len,
        };
        let elem_inference_1 = TE::unsigned_word(None);
        let elem_inference_2 = TE::signed_word(Some(64));
        state.infer(elem_1_tv, elem_inference_1);
        state.infer(elem_2_tv, elem_inference_2);
        let inferences = vec![array_inference_1, array_inference_2];
        let permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that we get the same result, and that they combine properly
        for permutation in permutations {
            // Register the array inferences in the state
            permutation.into_iter().for_each(|i| state.infer(array_tv, i.clone()));

            unify(&mut state);
            let result = util::get_inference(array_tv, state.result());

            // Check the result is right
            match result.unwrap() {
                TE::FixedArray { element, length } if length == input_len => {
                    assert!(vec![elem_1_tv, elem_2_tv].contains(&element));
                }
                _ => panic!("Bad payload in result"),
            }

            let result = util::get_inference(elem_1_tv, state.result());
            assert!(matches!(result.unwrap(), TE::Conflict { .. }));
        }
    }

    #[test]
    fn conflicts_for_fixed_arrays_with_incompatible_lengths() {
        // Set up the state
        let mut state = TypingState::empty();
        let array = SV::new_value(0, Provenance::Synthetic);
        let elem_1 = SV::new_value(0, Provenance::Synthetic);
        let elem_2 = SV::new_value(0, Provenance::Synthetic);
        let array_tv = state.register(array);
        let elem_1_tv = state.register(elem_1);
        let elem_2_tv = state.register(elem_2);

        // Create some inferences and register them
        let array_inference_1 = TE::FixedArray {
            element: elem_1_tv,
            length:  U256::from(7u32),
        };
        let array_inference_2 = TE::FixedArray {
            element: elem_2_tv,
            length:  U256::from(8u32),
        };
        let elem_inference_1 = TE::default_word();
        let elem_inference_2 = TE::signed_word(Some(64));
        state.infer(elem_1_tv, elem_inference_1);
        state.infer(elem_2_tv, elem_inference_2);
        let inferences = vec![array_inference_1, array_inference_2];
        let permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that we get the same result, and that they combine properly
        for permutation in permutations {
            // Register the array inferences in the state
            permutation.into_iter().for_each(|i| state.infer(array_tv, i.clone()));

            unify(&mut state);
            let result = util::get_inference(array_tv, state.result());
            assert!(matches!(result.unwrap(), TE::Conflict { .. }));
        }
    }

    #[test]
    fn can_infer_mappings_with_compatible_types() {
        // Set up the state
        let mut state = TypingState::empty();
        let mapping = SV::new_value(0, Provenance::Synthetic);
        let key_1 = SV::new_value(0, Provenance::Synthetic);
        let value_1 = SV::new_value(0, Provenance::Synthetic);
        let key_2 = SV::new_value(0, Provenance::Synthetic);
        let value_2 = SV::new_value(0, Provenance::Synthetic);
        let mapping_tv = state.register(mapping);
        let key_1_tv = state.register(key_1);
        let value_1_tv = state.register(value_1);
        let key_2_tv = state.register(key_2);
        let value_2_tv = state.register(value_2);

        // Create and register inferences
        state.infer(
            mapping_tv,
            TE::Mapping {
                key:   key_1_tv,
                value: value_1_tv,
            },
        );
        state.infer(
            mapping_tv,
            TE::Mapping {
                key:   key_2_tv,
                value: value_2_tv,
            },
        );
        state.infer(key_1_tv, TE::unsigned_word(None));
        state.infer(key_2_tv, TE::address());
        state.infer(value_1_tv, TE::signed_word(Some(32)));

        // Check that we get a sane result out
        unify(&mut state);
        let result = util::get_inference(mapping_tv, state.result());
        match result.unwrap() {
            TE::Mapping { key, value } => {
                assert!(vec![key_1_tv, key_2_tv].contains(&key));
                assert!(vec![value_1_tv, value_2_tv].contains(&value));
            }
            _ => panic!("Invalid payload"),
        }
    }

    #[test]
    fn errors_for_mappings_with_incompatible_key_types() {
        // Set up the state
        let mut state = TypingState::empty();
        let mapping = SV::new_value(0, Provenance::Synthetic);
        let key_1 = SV::new_value(0, Provenance::Synthetic);
        let value_1 = SV::new_value(0, Provenance::Synthetic);
        let key_2 = SV::new_value(0, Provenance::Synthetic);
        let value_2 = SV::new_value(0, Provenance::Synthetic);
        let mapping_tv = state.register(mapping);
        let key_1_tv = state.register(key_1);
        let value_1_tv = state.register(value_1);
        let key_2_tv = state.register(key_2);
        let value_2_tv = state.register(value_2);

        // Create and register inferences
        state.infer(
            mapping_tv,
            TE::Mapping {
                key:   key_1_tv,
                value: value_1_tv,
            },
        );
        state.infer(
            mapping_tv,
            TE::Mapping {
                key:   key_2_tv,
                value: value_2_tv,
            },
        );
        state.infer(key_1_tv, TE::signed_word(None));
        state.infer(key_2_tv, TE::address());
        state.infer(value_1_tv, TE::signed_word(Some(32)));

        // Check that we get a sane result out
        unify(&mut state);
        let result = util::get_inference(mapping_tv, state.result());
        match result.unwrap() {
            TE::Mapping { key, value } => {
                assert!(vec![key_1_tv, key_2_tv].contains(&key));
                assert!(vec![value_1_tv, value_2_tv].contains(&value));
            }
            _ => panic!("Invalid payload"),
        }

        let result = util::get_inference(key_1_tv, state.result());
        assert!(matches!(result.unwrap(), TE::Conflict { .. }));
    }

    #[test]
    fn errors_for_mappings_with_incompatible_value_types() {
        // Set up the state
        let mut state = TypingState::empty();
        let mapping = SV::new_value(0, Provenance::Synthetic);
        let key_1 = SV::new_value(0, Provenance::Synthetic);
        let value_1 = SV::new_value(0, Provenance::Synthetic);
        let key_2 = SV::new_value(0, Provenance::Synthetic);
        let value_2 = SV::new_value(0, Provenance::Synthetic);
        let mapping_tv = state.register(mapping);
        let key_1_tv = state.register(key_1);
        let value_1_tv = state.register(value_1);
        let key_2_tv = state.register(key_2);
        let value_2_tv = state.register(value_2);

        // Create and register inferences
        state.infer(
            mapping_tv,
            TE::Mapping {
                key:   key_1_tv,
                value: value_1_tv,
            },
        );
        state.infer(
            mapping_tv,
            TE::Mapping {
                key:   key_2_tv,
                value: value_2_tv,
            },
        );
        state.infer(key_1_tv, TE::signed_word(None));
        state.infer(value_1_tv, TE::signed_word(Some(32)));
        state.infer(value_2_tv, TE::address());

        // Check that we get a sane result out
        unify(&mut state);
        let result = util::get_inference(mapping_tv, state.result());
        match result.unwrap() {
            TE::Mapping { key, value } => {
                assert!(vec![key_1_tv, key_2_tv].contains(&key));
                assert!(vec![value_1_tv, value_2_tv].contains(&value));
            }
            _ => panic!("Invalid payload"),
        }

        let result = util::get_inference(value_1_tv, state.result());
        assert!(matches!(result.unwrap(), TE::Conflict { .. }));
    }

    #[test]
    fn can_infer_any_when_alone() {
        // Set up the state
        let mut state = TypingState::empty();
        let value = SV::new_value(0, Provenance::Synthetic);
        let value_tv = state.register(value);

        // Set up some inferences
        state.infer(value_tv, TE::Any);
        state.infer(value_tv, TE::Any);

        // Check the result makes sense
        unify(&mut state);
        let result = util::get_inference(value_tv, state.result());
        assert_eq!(result.unwrap(), TE::Any);
    }

    #[test]
    fn can_infer_other_value_with_any() {
        // Set up the state
        let mut state = TypingState::empty();
        let value = SV::new_value(0, Provenance::Synthetic);
        let value_tv = state.register(value);

        // Set up some inferences
        let inference = TE::signed_word(Some(256));
        state.infer(value_tv, inference.clone());
        state.infer(value_tv, TE::Any);

        // Check the result makes sense
        unify(&mut state);
        let result = util::get_inference(value_tv, state.result());
        assert_eq!(result.unwrap(), inference);
    }

    mod util {
        use crate::unifier::{
            expression::TypeExpression,
            state::TypeVariable,
            unification::UnificationForest,
        };

        /// Gets the first inference in the forest for `tp`, if it exists,
        /// returning `None` otherwise.
        pub fn get_inference(
            tp: TypeVariable,
            data: &mut UnificationForest,
        ) -> Option<TypeExpression> {
            data.get_data(&tp).and_then(|set| {
                let items: Vec<_> = set.iter().collect();
                assert!(items.len() <= 1, "There should only be one inference left");
                items.first().copied().cloned()
            })
        }
    }
}
