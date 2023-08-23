//! This module contains utilities for debugging the state of the type checker.

use std::collections::HashSet;

use crate::inference::{
    expression::TE,
    state::{InferenceState, TypeVariable},
};

/// Debug prints the inference tree for each variable in the `state`.
///
/// It also prints the associated value for each type variable when it
/// encounters them.
///
/// # Recursion and Cycles
///
/// Note that this is recursive, but will not follow cycles in inferences.
pub fn print_state(state: &InferenceState) {
    for ty in state.variables() {
        print_tv(ty, state);
    }
}

/// Debug prints the inference tree for an individual type variable in the
/// inference state.
///
/// It also prints the associated value for each type variable when it
/// encounters them.
///
/// # Recursion and Cycles
///
/// Note that this is recursive, but will not follow cycles in inferences.
pub fn print_tv(ty: TypeVariable, state: &InferenceState) {
    print_tv_impl(ty, state, 0, &mut HashSet::new());
}

/// The implementation of the debug printer for an individual type
/// variable's inference tree in the inference state.
///
/// It exists to provide a nicer interface on the output.
fn print_tv_impl(
    ty: TypeVariable,
    state: &InferenceState,
    indent: usize,
    seen: &mut HashSet<TypeVariable>,
) {
    let this_indent = " ".repeat(indent);
    let half_indent_level = indent + 2;
    let half_indent = " ".repeat(half_indent_level);
    let next_indent_level = indent + 4;
    let value = state.value_unchecked(ty);
    println!("{this_indent}↳ {value}");
    println!("{half_indent}: {ty}");
    for inf in state.inferences(ty) {
        seen.insert(ty);
        println!("{half_indent}= {inf}");
        match inf {
            TE::Equal { id } => {
                if !seen.contains(id) {
                    print_tv_impl(*id, state, next_indent_level, seen);
                }
            }
            TE::Mapping { key, value } => {
                if !seen.contains(key) {
                    print_tv_impl(*key, state, next_indent_level, seen);
                }
                if !seen.contains(value) {
                    print_tv_impl(*value, state, next_indent_level, seen);
                }
            }
            TE::FixedArray { element, .. } | TE::DynamicArray { element } => {
                if !seen.contains(element) {
                    print_tv_impl(*element, state, next_indent_level, seen);
                }
            }
            TE::Packed { types, .. } => types.iter().for_each(|span| {
                if !seen.contains(&span.typ) {
                    print_tv_impl(span.typ, state, next_indent_level, seen);
                }
            }),
            _ => (),
        }
    }
}
