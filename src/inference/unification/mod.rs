//! This module contains functionality for performing unification of inferences.
//!
//! It is split off from the primary [`super::InferenceEngine`] itself to enable
//! re-use of the functionality elsewhere, and also enable easier testing
//! without needing to spool up the entire unifier.

pub mod correspondence;
pub mod data;

use std::collections::{HashSet, VecDeque};

use itertools::Itertools;

use crate::{
    error::{
        container::Locatable,
        unification::{Error, Result},
    },
    inference::{
        expression::{InferenceSet, TypeExpression, WordUse, TE},
        state::{InferenceState, TypeVariable},
        unification::{correspondence::Correspondence, data::DisjointSet},
    },
    watchdog::DynWatchdog,
};

/// The concrete type of the [`DisjointSet`] data structure used for type
/// inference and unification.
pub type UnificationForest = DisjointSet<TypeVariable, InferenceSet>;

/// Performs unification to resolve the most-concrete type for all type
/// variables in the typing `state`, writing the unification result into the
/// state.
///
/// This may result in [`TE::Conflict`]s occurring in the result forest.
///
/// # Errors
///
/// Returns [`Err`] if unification is halted by the watchdog.
pub fn unify(state: &mut InferenceState, watchdog: &DynWatchdog) -> Result<()> {
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

    let polling_interval = watchdog.poll_every();
    let mut counter = 0;

    // Then, we loop until we stop making progress.
    loop {
        // Create the set of new equalities.
        let mut all_equalities: HashSet<Equality> = HashSet::new();
        let mut all_judgements: HashSet<Judgement> = HashSet::new();

        // Create our stop condition.
        let mut made_progress = false;

        for (ty_var, inferences) in forest.sets() {
            // If we have been told to stop, stop and return an error.
            if counter % polling_interval == 0 && watchdog.should_stop() {
                let location = state.value_unchecked(ty_var).instruction_pointer();

                Err(Error::StoppedByWatchdog).locate(location)?;
            }

            // If there are no inferences for this type variable, go to the next one.
            if inferences.is_empty() {
                continue;
            }

            // Get all of the inferences
            let mut inferred_expressions: VecDeque<_> = inferences.into_iter().collect();
            let mut current = inferred_expressions
                .pop_front()
                .expect("We know there is at least one item in the expressions queue");

            // If there is more than one expression, this will execute, and fold over them
            for expression in inferred_expressions {
                made_progress = true;
                let Merge {
                    expression,
                    equalities,
                    judgements,
                } = merge(current.clone(), expression);
                current = expression;
                all_equalities.extend(equalities);
                all_judgements.extend(judgements);
            }

            // Finally, we have to update the forest's inferences for each type variable
            forest.set_data(&ty_var, InferenceSet::from([current]));

            counter += 0;
        }

        // When we get to the end of that loop, we need to compute the unions of
        // the variables with their new associated inferences
        for Equality { left, right } in all_equalities {
            forest.union(&left, &right);
        }

        // When we get to the end of that loop, we need to add any new typing judgements
        // to the state to continue computation
        for Judgement { tv, expr } in all_judgements {
            forest.add_data(&tv, InferenceSet::from([expr]));
        }

        // If we didn't make any progress at any point, then we end the loop as we are
        // done with unification
        if !made_progress {
            break;
        }
    }

    state.set_result(forest);

    Ok(())
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

        // Combining a conflict with anything is another conflict that propagates information
        (TE::Conflict { .. }, _) => {
            Merge::expression(left.conflict_with(right, "Conflicts always conflict"))
        }
        (_, TE::Conflict { .. }) => {
            Merge::expression(right.conflict_with(left, "Conflicts always conflict"))
        }

        // Combining words with words is complex
        (
            TE::Word {
                width: width_l,
                usage: usage_l,
            },
            TE::Word {
                width: width_r,
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

            // We need to merge the usages
            let Some(usage) = usage_l.merge(*usage_r) else {
                return Merge::expression(TE::conflict(left, right, "Conflicting word usages"));
            };

            Merge::expression(TE::word(width, usage))
        }

        // To combine a word with a dynamic array we delegate
        (TE::Word { .. }, TE::DynamicArray { .. }) => merge(right, left),

        // They produce a dynamic array as long as the word is not signed
        (TE::DynamicArray { .. }, TE::Word { usage, .. }) => {
            Merge::expression(if usage.is_definitely_signed() {
                TE::conflict(left, right, "Dynamic arrays cannot have signed length")
            } else {
                left
            })
        }

        // Dynamic arrays can combine with dynamic arrays
        (TE::DynamicArray { element: element_l }, TE::DynamicArray { element: element_r }) => {
            let equalities = vec![Equality::new(*element_l, *element_r)];
            Merge::equalities(left, equalities)
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
                Merge::equalities(left, equalities)
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
            Merge::equalities(left, equalities)
        }

        // Packed encodings can combine with packed encodings
        (
            TE::Packed {
                types: types_l,
                is_struct: is_struct_l,
            },
            TE::Packed {
                types: types_r,
                is_struct: is_struct_r,
            },
        ) => {
            let result = Correspondence::new(
                types_l.clone(),
                types_r.clone(),
                *is_struct_l || *is_struct_r,
            )
            .merge();

            match result {
                Some(m) => m,
                None => {
                    Merge::expression(TE::conflict(left, right, "Incompatible packed encodings"))
                }
            }
        }

        // Packed encodings can also combine with words
        (TE::Word { .. }, TE::Packed { .. }) => merge(right, left),
        (TE::Packed { types, .. }, TE::Word { width, usage }) => {
            // If we have no spans, things are just the word
            if types.is_empty() {
                return Merge::expression(right);
            }

            // We can only merge if the word is bytes
            if *usage == WordUse::Bytes {
                // Get the combined size of the packed encoding elements
                let types: Vec<_> = types.iter().sorted_by_key(|span| span.offset).collect();
                let start_point =
                    types.first().expect("Packed encoding had no members").start_bit();
                let end_point = types.last().expect("Packed encoding had no members").end_bit();
                let total_size = end_point - start_point;

                if let Some(w) = width {
                    // If we know the width, total size must fit within it
                    if total_size <= *w {
                        // If it fits we return the packed encoding
                        Merge::expression(left)
                    } else {
                        // If it doesn't fit we have a conflict
                        Merge::expression(TE::conflict(
                            left,
                            right,
                            "Incompatible sizes of packed encoding and bytes",
                        ))
                    }
                } else {
                    // If we do not know the width, we assume it will fit to
                    // propagate evidence for later
                    Merge::expression(left)
                }
            } else {
                Merge::expression(TE::conflict(
                    left,
                    right,
                    "Packed encodings cannot be merged with non-bytes words",
                ))
            }
        }

        // Everything can combine with `Any` to produce itself, as Any doesn't add information, so
        // only collapses to `Any` when combined with itself
        (_, TE::Any) => Merge::expression(left),
        (TE::Any, _) => Merge::expression(right),

        // Nothing else can combine and be valid, so we return a typing conflict
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

    /// Any new typing judgements to be accounted for that are created as part
    /// of combining `left` and `right`.
    pub judgements: Vec<Judgement>,
}

impl Merge {
    /// Creates a new combine result from the provided `expression` and
    /// `equalities`.
    #[must_use]
    pub fn new(
        expression: TypeExpression,
        equalities: Vec<Equality>,
        judgements: Vec<Judgement>,
    ) -> Self {
        Self {
            expression,
            equalities,
            judgements,
        }
    }

    /// Creates a new combine result from the provided `expression`, with no
    /// equalities or judgements.
    #[must_use]
    pub fn expression(expression: TypeExpression) -> Self {
        let equalities = Vec::new();
        let judgements = Vec::new();
        Self::new(expression, equalities, judgements)
    }

    /// Creates a new combine result from the provided `expression` and
    /// `equalities` but without any judgements.
    #[must_use]
    pub fn equalities(expression: TypeExpression, equalities: Vec<Equality>) -> Self {
        let judgements = Vec::new();
        Self::new(expression, equalities, judgements)
    }

    /// Creates a new combine result from the provided `expression` and
    /// `judgements` but without any equalities.
    #[must_use]
    pub fn judgements(expression: TypeExpression, judgements: Vec<Judgement>) -> Self {
        let equalities = Vec::new();
        Self::new(expression, equalities, judgements)
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

/// A new judgement written out during the inference process.
///
/// This is distinct from [`Equality`] simply due to the fact that it is easier
/// to process this way. Fundamentally, `Equality` is just `Judgement(left,
/// TE::eq(right)`, and is
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Judgement {
    /// The type variable to equate with `expr`.
    pub tv: TypeVariable,

    /// The type expression representing the new judgement.
    pub expr: TypeExpression,
}

impl Judgement {
    /// Creates a new judgement saying that the type variable `tv` has the type
    /// given by `expr`.
    #[must_use]
    pub fn new(tv: TypeVariable, expr: TypeExpression) -> Self {
        Self { tv, expr }
    }
}

#[cfg(test)]
mod test {
    use std::panic;

    use ethnum::U256;
    use itertools::Itertools;

    use crate::{
        constant::ADDRESS_WIDTH_BITS,
        inference::{
            expression::{Span, WordUse, TE},
            state::InferenceState,
            unification::{merge, unify},
        },
        vm::value::{Provenance, RSV},
        watchdog::LazyWatchdog,
    };

    #[test]
    fn panics_when_encountering_equality() {
        // Override the panic hook so we don't see output in tests
        panic::set_hook(Box::new(|_| {}));

        // Set up the state
        let mut state = InferenceState::empty();
        let v_1 = RSV::new_value(0, Provenance::Synthetic);
        let v_2 = RSV::new_value(1, Provenance::Synthetic);
        let _ = state.register(v_1);
        let v_2_tv = state.register(v_2);

        // Set up some inferences
        let inference_1 = TE::eq(v_2_tv);
        let inference_2 = TE::bytes(None);

        // Check it does the right thing
        let result = panic::catch_unwind(|| merge(inference_1.clone(), inference_2.clone()));
        assert!(result.is_err());

        let result = panic::catch_unwind(|| merge(inference_2, inference_1));
        assert!(result.is_err());
    }

    #[test]
    fn can_infer_compatible_unsigned_words() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let v_1 = RSV::new_value(0, Provenance::Synthetic);
        let v_1_tv = state.register(v_1);

        // Set up some inferences
        let inference_1 = TE::bytes(Some(ADDRESS_WIDTH_BITS));
        let inference_2 = TE::bytes(None);
        let inference_3 = TE::address();
        let inferences = vec![inference_1, inference_2, inference_3];
        let inference_permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that they combine properly, and produce the same result no matter the
        // order
        for permutation in inference_permutations {
            permutation.into_iter().for_each(|i| state.infer(v_1_tv, i.clone()));

            unify(&mut state, &LazyWatchdog.in_rc())?;
            let result = util::get_inference(v_1_tv, state.result());

            assert!(result.is_some());
            assert_eq!(
                result.unwrap(),
                TE::word(Some(ADDRESS_WIDTH_BITS), WordUse::Address)
            );
        }

        Ok(())
    }

    #[test]
    fn can_infer_compatible_signed_words() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let v_1 = RSV::new_value(0, Provenance::Synthetic);
        let v_1_tv = state.register(v_1);

        // Set up some inferences
        let inference_1 = TE::signed_word(Some(64));
        let inference_2 = TE::bytes(None);
        let inference_3 = TE::signed_word(None);
        let inferences = vec![inference_1, inference_2, inference_3];
        let inference_permutations: Vec<Vec<_>> =
            inferences.iter().permutations(inferences.len()).unique().collect();

        // Check that they combine properly, and produce the same result no matter the
        // order
        for permutation in inference_permutations {
            permutation.into_iter().for_each(|i| state.infer(v_1_tv, i.clone()));

            unify(&mut state, &LazyWatchdog.in_rc())?;
            let result = util::get_inference(v_1_tv, state.result());

            assert!(result.is_some());
            assert_eq!(result.unwrap(), TE::word(Some(64), WordUse::SignedNumeric));
        }

        Ok(())
    }

    #[test]
    fn conflicts_for_incompatible_word_evidence() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let v_1 = RSV::new_value(0, Provenance::Synthetic);
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

            unify(&mut state, &LazyWatchdog.in_rc())?;
            let result = util::get_inference(v_1_ty, state.result());

            assert!(result.is_some());
            assert!(matches!(result.unwrap(), TE::Conflict { .. }));
        }

        Ok(())
    }

    #[test]
    fn can_infer_unsigned_word_with_dynamic_array() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let array = RSV::new_value(0, Provenance::Synthetic);
        let element = RSV::new_value(0, Provenance::Synthetic);
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

            unify(&mut state, &LazyWatchdog.in_rc())?;
            let result = util::get_inference(array_tv, state.result());

            assert!(result.is_some());
            assert_eq!(
                result.unwrap(),
                TE::DynamicArray {
                    element: element_tv,
                }
            );
        }

        Ok(())
    }

    #[test]
    fn conflicts_for_signed_word_with_dynamic_array() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let array = RSV::new_value(0, Provenance::Synthetic);
        let element = RSV::new_value(0, Provenance::Synthetic);
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

            unify(&mut state, &LazyWatchdog.in_rc())?;
            let result = util::get_inference(array_tv, state.result());

            assert!(result.is_some());
            assert!(matches!(result.unwrap(), TE::Conflict { .. }));
        }

        Ok(())
    }

    #[test]
    fn can_infer_dynamic_arrays_with_compatible_element_types() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let array = RSV::new_value(0, Provenance::Synthetic);
        let elem_1 = RSV::new_value(0, Provenance::Synthetic);
        let elem_2 = RSV::new_value(0, Provenance::Synthetic);
        let array_tv = state.register(array);
        let elem_1_tv = state.register(elem_1);
        let elem_2_tv = state.register(elem_2);

        // Create some inferences and register them
        let array_inference_1 = TE::DynamicArray { element: elem_1_tv };
        let array_inference_2 = TE::DynamicArray { element: elem_2_tv };
        let elem_inference_1 = TE::bytes(None);
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
            unify(&mut state, &LazyWatchdog.in_rc())?;
            let result = util::get_inference(array_tv, state.result());

            match result.unwrap() {
                TE::DynamicArray { element } => {
                    assert!(vec![elem_1_tv, elem_2_tv].contains(&element));
                }
                _ => panic!("Bad payload in result"),
            }
        }

        Ok(())
    }

    #[test]
    fn conflicts_for_dynamic_arrays_with_incompatible_element_types() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let array = RSV::new_value(0, Provenance::Synthetic);
        let elem_1 = RSV::new_value(0, Provenance::Synthetic);
        let elem_2 = RSV::new_value(0, Provenance::Synthetic);
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
            unify(&mut state, &LazyWatchdog.in_rc())?;
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

        Ok(())
    }

    #[test]
    fn can_infer_fixed_arrays_with_compatible_element_types() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let array = RSV::new_value(0, Provenance::Synthetic);
        let elem_1 = RSV::new_value(0, Provenance::Synthetic);
        let elem_2 = RSV::new_value(0, Provenance::Synthetic);
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
        let elem_inference_1 = TE::bytes(None);
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

            unify(&mut state, &LazyWatchdog.in_rc())?;
            let result = util::get_inference(array_tv, state.result());

            // Check the result is right
            match result.unwrap() {
                TE::FixedArray { element, length } if length == input_len => {
                    assert!(vec![elem_1_tv, elem_2_tv].contains(&element));
                }
                _ => panic!("Bad payload in result"),
            }
        }

        Ok(())
    }

    #[test]
    fn conflicts_for_fixed_arrays_with_incompatible_element_types() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let array = RSV::new_value(0, Provenance::Synthetic);
        let elem_1 = RSV::new_value(0, Provenance::Synthetic);
        let elem_2 = RSV::new_value(0, Provenance::Synthetic);
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

            unify(&mut state, &LazyWatchdog.in_rc())?;
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

        Ok(())
    }

    #[test]
    fn conflicts_for_fixed_arrays_with_incompatible_lengths() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let array = RSV::new_value(0, Provenance::Synthetic);
        let elem_1 = RSV::new_value(0, Provenance::Synthetic);
        let elem_2 = RSV::new_value(0, Provenance::Synthetic);
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
        let elem_inference_1 = TE::bytes(None);
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

            unify(&mut state, &LazyWatchdog.in_rc())?;
            let result = util::get_inference(array_tv, state.result());
            assert!(matches!(result.unwrap(), TE::Conflict { .. }));
        }

        Ok(())
    }

    #[test]
    fn can_infer_mappings_with_compatible_types() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let mapping = RSV::new_value(0, Provenance::Synthetic);
        let key_1 = RSV::new_value(0, Provenance::Synthetic);
        let value_1 = RSV::new_value(0, Provenance::Synthetic);
        let key_2 = RSV::new_value(0, Provenance::Synthetic);
        let value_2 = RSV::new_value(0, Provenance::Synthetic);
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
        unify(&mut state, &LazyWatchdog.in_rc())?;
        let result = util::get_inference(mapping_tv, state.result());
        match result.unwrap() {
            TE::Mapping { key, value } => {
                assert!(vec![key_1_tv, key_2_tv].contains(&key));
                assert!(vec![value_1_tv, value_2_tv].contains(&value));
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn errors_for_mappings_with_incompatible_key_types() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let mapping = RSV::new_value(0, Provenance::Synthetic);
        let key_1 = RSV::new_value(0, Provenance::Synthetic);
        let value_1 = RSV::new_value(0, Provenance::Synthetic);
        let key_2 = RSV::new_value(0, Provenance::Synthetic);
        let value_2 = RSV::new_value(0, Provenance::Synthetic);
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
        unify(&mut state, &LazyWatchdog.in_rc())?;
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

        Ok(())
    }

    #[test]
    fn errors_for_mappings_with_incompatible_value_types() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let mapping = RSV::new_value(0, Provenance::Synthetic);
        let key_1 = RSV::new_value(0, Provenance::Synthetic);
        let value_1 = RSV::new_value(0, Provenance::Synthetic);
        let key_2 = RSV::new_value(0, Provenance::Synthetic);
        let value_2 = RSV::new_value(0, Provenance::Synthetic);
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
        unify(&mut state, &LazyWatchdog.in_rc())?;
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

        Ok(())
    }

    #[test]
    fn can_infer_any_when_alone() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let value = RSV::new_value(0, Provenance::Synthetic);
        let value_tv = state.register(value);

        // Set up some inferences
        state.infer(value_tv, TE::Any);
        state.infer(value_tv, TE::Any);

        // Check the result makes sense
        unify(&mut state, &LazyWatchdog.in_rc())?;
        let result = util::get_inference(value_tv, state.result());
        assert_eq!(result.unwrap(), TE::Any);

        Ok(())
    }

    #[test]
    fn can_infer_other_value_with_any() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let value = RSV::new_value(0, Provenance::Synthetic);
        let value_tv = state.register(value);

        // Set up some inferences
        let inference = TE::signed_word(Some(256));
        state.infer(value_tv, inference.clone());
        state.infer(value_tv, TE::Any);

        // Check the result makes sense
        unify(&mut state, &LazyWatchdog.in_rc())?;
        let result = util::get_inference(value_tv, state.result());
        assert_eq!(result.unwrap(), inference);

        Ok(())
    }

    #[test]
    #[allow(clippy::similar_names)] // Intentional
    fn can_infer_packed_with_packed() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let elem_1 = RSV::new_value(0, Provenance::Synthetic);
        let elem_2 = RSV::new_value(1, Provenance::Synthetic);
        let elem_3 = RSV::new_value(2, Provenance::Synthetic);
        let elem_4 = RSV::new_value(3, Provenance::Synthetic);
        let packed_1 = RSV::new_value(4, Provenance::Synthetic);
        let packed_2 = RSV::new_value(5, Provenance::Synthetic);

        let [e1_tv, e2_tv, e3_tv, e4_tv, p1_tv, p2_tv] =
            state.register_many([elem_1, elem_2, elem_3, elem_4, packed_1, packed_2]);

        // Set up some inferences
        //
        // `p1_tv = packed(pos(e1_tv, 0, 64), pos(e2_tv, 64, 64))`
        // `p2_tv = packed(pos(e3_tv, 0, 128), pos(e4_tv, 128, 128))`
        // `p1_tv == p2_tv`
        //
        // These are compatible, and should be able to be combined
        state.infer(e1_tv, TE::unsigned_word(Some(64)));
        state.infer(e2_tv, TE::unsigned_word(Some(64)));
        state.infer(
            p1_tv,
            TE::packed_of(vec![Span::new(e1_tv, 0, 64), Span::new(e2_tv, 64, 64)]),
        );
        state.infer(e3_tv, TE::bytes(Some(128)));
        state.infer(e4_tv, TE::unsigned_word(Some(128)));
        state.infer(
            p2_tv,
            TE::packed_of(vec![Span::new(e3_tv, 0, 128), Span::new(e4_tv, 128, 128)]),
        );
        state.infer(p1_tv, TE::eq(p2_tv));

        // Check the result makes sense
        unify(&mut state, &LazyWatchdog.in_rc())?;
        let p1_tv_type = util::get_inference(p1_tv, state.result()).unwrap();
        assert_eq!(
            p1_tv_type,
            TE::packed_of(vec![Span::new(e3_tv, 0, 128), Span::new(e4_tv, 128, 128),])
        );

        let e3_tv_type = util::get_inference(e3_tv, state.result()).unwrap();
        assert_eq!(
            e3_tv_type,
            TE::packed_of(vec![Span::new(e1_tv, 0, 64), Span::new(e2_tv, 64, 64)])
        );

        Ok(())
    }

    #[test]
    #[allow(clippy::similar_names)] // Intentional
    fn conflicts_if_packed_types_are_incompatible() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let elem_1 = RSV::new_value(0, Provenance::Synthetic);
        let elem_2 = RSV::new_value(1, Provenance::Synthetic);
        let elem_3 = RSV::new_value(2, Provenance::Synthetic);
        let elem_4 = RSV::new_value(3, Provenance::Synthetic);
        let packed_1 = RSV::new_value(4, Provenance::Synthetic);
        let packed_2 = RSV::new_value(5, Provenance::Synthetic);

        let [e1_tv, e2_tv, e3_tv, e4_tv, p1_tv, p2_tv] =
            state.register_many([elem_1, elem_2, elem_3, elem_4, packed_1, packed_2]);

        // Set up some inferences
        //
        // `p1_tv = packed(pos(e1_tv, 0, 64), pos(e2_tv, 64, 128))`
        // `p2_tv = packed(pos(e3_tv, 0, 128), pos(e4_tv, 128, 128))`
        // `p1_tv == p2_tv`
        //
        // These are compatible, and should be able to be combined
        state.infer(e1_tv, TE::unsigned_word(Some(64)));
        state.infer(e2_tv, TE::unsigned_word(Some(128)));
        state.infer(
            p1_tv,
            TE::packed_of(vec![Span::new(e1_tv, 0, 64), Span::new(e2_tv, 64, 128)]),
        );
        state.infer(e3_tv, TE::bytes(Some(128)));
        state.infer(e4_tv, TE::unsigned_word(Some(128)));
        state.infer(
            p2_tv,
            TE::packed_of(vec![Span::new(e3_tv, 0, 128), Span::new(e4_tv, 128, 128)]),
        );
        state.infer(p1_tv, TE::eq(p2_tv));

        // Check the result makes sense
        unify(&mut state, &LazyWatchdog.in_rc())?;
        let p1_tv_type = util::get_inference(p1_tv, state.result()).unwrap();
        assert!(matches!(p1_tv_type, TE::Conflict { .. }));

        Ok(())
    }

    #[test]
    #[allow(clippy::similar_names)] // Intentional
    fn can_infer_packed_with_bytes() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let elem_1 = RSV::new_value(0, Provenance::Synthetic);
        let elem_2 = RSV::new_value(1, Provenance::Synthetic);
        let elem_3 = RSV::new_value(2, Provenance::Synthetic);
        let packed_1 = RSV::new_value(3, Provenance::Synthetic);

        let [e1_tv, e2_tv, e3_tv, p1_tv] = state.register_many([elem_1, elem_2, elem_3, packed_1]);

        // Set up some inferences
        //
        // - e1_tv = uint64
        // - e2_tv = int64
        // - e3_tv = bytes16
        // - p1_tv = packed(span(e1_tv, 0, 64), span(e2_tv, 64, 64))
        // - p1_tv == e3_tv
        state.infer(e1_tv, TE::unsigned_word(Some(64)));
        state.infer(e2_tv, TE::signed_word(Some(64)));
        state.infer(e3_tv, TE::bytes(Some(128)));
        state.infer(
            p1_tv,
            TE::packed_of(vec![Span::new(e1_tv, 0, 64), Span::new(e2_tv, 64, 64)]),
        );
        state.infer(p1_tv, TE::eq(e3_tv));

        // Run inference and check the result makes sense
        unify(&mut state, &LazyWatchdog.in_rc())?;

        let p1_tv_type = util::get_inference(p1_tv, state.result()).unwrap();
        assert_eq!(
            p1_tv_type,
            TE::packed_of(vec![Span::new(e1_tv, 0, 64), Span::new(e2_tv, 64, 64),])
        );
        let e3_tv_type = util::get_inference(e3_tv, state.result()).unwrap();
        assert_eq!(e3_tv_type, p1_tv_type);

        Ok(())
    }

    #[test]
    #[allow(clippy::similar_names)] // Intentional
    fn can_infer_packed_with_bytes_with_offset() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let elem_1 = RSV::new_value(0, Provenance::Synthetic);
        let elem_2 = RSV::new_value(1, Provenance::Synthetic);
        let elem_3 = RSV::new_value(2, Provenance::Synthetic);
        let packed_1 = RSV::new_value(3, Provenance::Synthetic);

        let [e1_tv, e2_tv, e3_tv, p1_tv] = state.register_many([elem_1, elem_2, elem_3, packed_1]);

        // Set up some inferences
        //
        // - e1_tv = uint32
        // - e2_tv = int64
        // - e3_tv = bytes16
        // - p1_tv = packed(span(e1_tv, 32, 32), span(e2_tv, 64, 64))
        // - p1_tv == e3_tv
        state.infer(e1_tv, TE::unsigned_word(Some(32)));
        state.infer(e2_tv, TE::signed_word(Some(64)));
        state.infer(e3_tv, TE::bytes(Some(128)));
        state.infer(
            p1_tv,
            TE::packed_of(vec![Span::new(e1_tv, 32, 32), Span::new(e2_tv, 64, 64)]),
        );
        state.infer(p1_tv, TE::eq(e3_tv));

        // Run inference and check the result makes sense
        unify(&mut state, &LazyWatchdog.in_rc())?;

        let p1_tv_type = util::get_inference(p1_tv, state.result()).unwrap();
        assert_eq!(
            p1_tv_type,
            TE::packed_of(vec![Span::new(e1_tv, 32, 32), Span::new(e2_tv, 64, 64),])
        );
        let e3_tv_type = util::get_inference(e3_tv, state.result()).unwrap();
        assert_eq!(e3_tv_type, p1_tv_type);

        Ok(())
    }

    #[test]
    #[allow(clippy::similar_names)] // Intentional
    fn conflicts_if_packed_and_bytes_are_incompatible() -> anyhow::Result<()> {
        // Set up the state
        let mut state = InferenceState::empty();
        let elem_1 = RSV::new_value(0, Provenance::Synthetic);
        let elem_2 = RSV::new_value(1, Provenance::Synthetic);
        let elem_3 = RSV::new_value(2, Provenance::Synthetic);
        let packed_1 = RSV::new_value(3, Provenance::Synthetic);

        let [e1_tv, e2_tv, e3_tv, p1_tv] = state.register_many([elem_1, elem_2, elem_3, packed_1]);

        // Set up some inferences
        //
        // - e1_tv = uint32
        // - e2_tv = int128
        // - e3_tv = bytes16
        // - p1_tv = packed(span(e1_tv, 32, 32), span(e2_tv, 64, 128))
        // - p1_tv == e3_tv
        state.infer(e1_tv, TE::unsigned_word(Some(32)));
        state.infer(e2_tv, TE::signed_word(Some(128)));
        state.infer(e3_tv, TE::bytes(Some(128)));
        state.infer(
            p1_tv,
            TE::packed_of(vec![Span::new(e1_tv, 32, 32), Span::new(e2_tv, 64, 128)]),
        );
        state.infer(p1_tv, TE::eq(e3_tv));

        // Run inference and check the result makes sense
        unify(&mut state, &LazyWatchdog.in_rc())?;

        let p1_tv_type = util::get_inference(p1_tv, state.result()).unwrap();
        assert!(matches!(p1_tv_type, TE::Conflict { .. }));

        Ok(())
    }

    mod util {
        use crate::inference::{
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
