//! This module contains the [`Unifier`] and related utilities.

pub mod implication_set;
pub mod types;

/// The `Unifier` is responsible for combining the evidence as to the type of a
/// storage variable, in the form of [`ImplicationSet`]s, to discover the most
/// concretely-known type for that variable.
#[derive(Debug)]
pub struct Unifier;
