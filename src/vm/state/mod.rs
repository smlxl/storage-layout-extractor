//! The state representation for the symbolic virtual machine, and utilities for
//! dealing with said representation.

pub mod memory;
pub mod stack;
pub mod storage;

/// The state representation for the [`super::VM`].
#[derive(Debug, Eq, PartialEq)]
pub struct VMState {}

// TODO [Ara] Needs to contain a stack, memory, and the storage.

// TODO [Ara] When a symbolic value is going to disappear it should be added to
//   the `VM`s buffer of them.

// TODO [Ara] State needs to be easily "forked" and should track its fork point.
//   When forked, it causes a state bifurcation.

// TODO [Ara] The addresses may also be symbolic values.

// TODO [Ara] Precomputed keccaks for the early storage slots to help with
//   recognition of constants. With arrays.

// TODO [Ara] Needs to store a mapping from bytecode locations to `Value` UUIDs.
//   Should provide a `new_variable` method.
