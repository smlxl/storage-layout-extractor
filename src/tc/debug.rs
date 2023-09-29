//! This module contains utilities for debugging the state of the type checker.

use std::collections::{HashSet, VecDeque};

use crate::{
    tc::{
        expression::{InferenceSet, TE},
        state::{type_variable::TypeVariable, TypeCheckerState},
        unification::UnificationForest,
    },
    vm::value::{known::KnownWord, TCBoxedVal, TCSVD},
};

/// Gets the type variable for the storage slot at `index` in `state`.
#[must_use]
pub fn type_for_slot_at(index: usize, state: &TypeCheckerState) -> Option<TypeVariable> {
    let slot: Option<&TCBoxedVal> = state.values().into_iter().find(|v| {
        matches!(
            v.data(),
            TCSVD::StorageSlot { key } if matches!(
                key.data(),
                TCSVD::KnownData {value} if *value == KnownWord::from(index)
            )
        )
    });

    slot.map(|v| state.var_unchecked(v))
}

/// A trait representing types from which you can get the [`InferenceSet`] for a
/// given type variable.
pub trait HasInferences {
    /// Returns the inference set for `tv`.
    fn inferences_for(&mut self, tv: TypeVariable) -> InferenceSet;

    /// Gets the value associated with `tv`, if possible.
    fn value_for(&mut self, tv: TypeVariable) -> Option<TCBoxedVal>;

    /// Gets all of the type variables that the state knows about.
    fn all_type_vars(&mut self) -> Vec<TypeVariable>;
}

impl HasInferences for TypeCheckerState {
    /// Returns the inference set for `tv`.
    fn inferences_for(&mut self, tv: TypeVariable) -> InferenceSet {
        self.inferences(tv).clone()
    }

    /// Gets the value associated with `tv`, where said value exists.
    fn value_for(&mut self, tv: TypeVariable) -> Option<TCBoxedVal> {
        self.value(tv).cloned()
    }

    /// Gets all of the type variables that the type checker state knows about.
    fn all_type_vars(&mut self) -> Vec<TypeVariable> {
        self.variables()
    }
}

impl HasInferences for UnificationForest {
    /// Returns the inference set for `tv`.
    fn inferences_for(&mut self, tv: TypeVariable) -> InferenceSet {
        self.get_data(&tv).cloned().unwrap_or(InferenceSet::new())
    }

    /// Returns [`None`] as the forest has no values associated with its types.
    fn value_for(&mut self, _tv: TypeVariable) -> Option<TCBoxedVal> {
        None
    }

    /// Gets all of the type variables that the unification forest knows about.
    fn all_type_vars(&mut self) -> Vec<TypeVariable> {
        self.values()
    }
}

/// Debug prints the inference tree for each variable in the `state`.
///
/// It also prints the associated value for each type variable alongside the
/// nodes where they are available.
///
/// # Recursion and Cycles
///
/// Note that this is recursive, but will not follow cycles in inferences.
pub fn print_state(state: &mut impl HasInferences) {
    for ty in state.all_type_vars() {
        print_state_tv(ty, state);
    }
}

/// Debug prints the inference tree for an individual type variable in the
/// type checker state.
///
/// It also prints the associated value for each type variable alongside the
/// nodes where they are available.
///
/// # Recursion and Cycles
///
/// Note that this is recursive, but will not follow cycles in inferences.
pub fn print_state_tv(ty: TypeVariable, state: &mut impl HasInferences) {
    print_state_tv_impl(ty, state, 0, &mut HashSet::new());
}

/// The implementation of the debug printer for an individual type
/// variable's inference tree in the type checker state.
///
/// It exists to provide a nicer interface on the output.
fn print_state_tv_impl(
    ty: TypeVariable,
    state: &mut impl HasInferences,
    indent: usize,
    seen: &mut HashSet<TypeVariable>,
) {
    let this_indent = " ".repeat(indent);
    let half_indent_level = indent + 2;
    let half_indent = " ".repeat(half_indent_level);
    let next_indent_level = indent + 4;
    let value = state
        .value_for(ty)
        .map_or("value unavailable".into(), |v| v.to_string());
    println!("{this_indent}↳ {value}");
    println!("{half_indent}: {ty}");
    for inf in state.inferences_for(ty) {
        seen.insert(ty);
        println!("{half_indent}= {inf}");
        match inf {
            TE::Equal { id } => {
                if !seen.contains(&id) {
                    print_state_tv_impl(id, state, next_indent_level, seen);
                }
            }
            TE::Mapping { key, value } => {
                if !seen.contains(&key) {
                    print_state_tv_impl(key, state, next_indent_level, seen);
                }
                if !seen.contains(&value) {
                    print_state_tv_impl(value, state, next_indent_level, seen);
                }
            }
            TE::FixedArray { element, .. } | TE::DynamicArray { element } => {
                if !seen.contains(&element) {
                    print_state_tv_impl(element, state, next_indent_level, seen);
                }
            }
            TE::Packed { types, .. } => types.iter().for_each(|span| {
                if !seen.contains(&span.typ) {
                    print_state_tv_impl(span.typ, state, next_indent_level, seen);
                }
            }),
            _ => (),
        }
    }
}

/// Prints a single level of the inferences for `tv` as contained in the
/// `state`.
///
/// To print the entire state see [`print_state`], and to print the tc
/// tree for a single type variable see [`print_state_tv`].
pub fn print_inferences_for(tv: TypeVariable, state: &mut impl HasInferences) {
    let value = state
        .value_for(tv)
        .map_or("value unavailable".into(), |v| v.to_string());
    println!("↳ {value}");
    println!(": {tv}");
    state.inferences_for(tv).iter().for_each(|expr| {
        println!("  = {expr} ");
    });
}

/// Gets all of the type variables that are recursively children of `ty` and are
/// mentioned in the `state`.
#[must_use]
pub fn collect_vars_in_tree_of(
    ty: TypeVariable,
    state: &mut impl HasInferences,
) -> HashSet<TypeVariable> {
    let mut seen: HashSet<TypeVariable> = HashSet::new();
    let mut tyvar_queue = VecDeque::from([ty]);

    while let Some(tv) = tyvar_queue.pop_front() {
        let inferences = state.inferences_for(tv);
        inferences.iter().for_each(|i| match i {
            TE::Any | TE::Word { .. } | TE::Conflict { .. } | TE::Bytes => (),
            TE::Equal { id } => {
                if !seen.contains(id) {
                    tyvar_queue.push_back(*id);
                }
            }
            TE::FixedArray { element, .. } | TE::DynamicArray { element } => {
                if !seen.contains(element) {
                    tyvar_queue.push_back(*element);
                }
            }
            TE::Mapping { key, value } => {
                if !seen.contains(key) {
                    tyvar_queue.push_back(*key);
                }
                if !seen.contains(value) {
                    tyvar_queue.push_back(*value);
                }
            }
            TE::Packed { types, .. } => types.iter().for_each(|s| {
                if !seen.contains(&s.typ) {
                    tyvar_queue.push_back(s.typ);
                }
            }),
        });

        seen.insert(tv);
    }

    seen
}
