//! This module contains the [`Unifier`] and related utilities.

pub mod implication;
pub mod types;

/// The `Unifier` is responsible for combining the evidence as to the type of a
/// storage variable, in the form of [`implication::Set`]s, to discover the most
/// concretely-known type for that variable.
#[derive(Debug)]
pub struct Unifier;

// TODO [Ara] Needs to de-duplicate trees as some will be the same.

// TODO [Ara] Precomputed keccaks for the early storage slots to help with
//   recognition of constants. With arrays.
