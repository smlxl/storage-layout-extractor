//! The state representation for the symbolic virtual machine, and utilities for
//! dealing with said representation.

pub mod memory;
pub mod stack;
pub mod storage;

/// The state representation for the [`super::VM`].
#[derive(Debug, Eq, PartialEq)]
pub struct VMState {}

// TODO [Ara] state needs to be easily "forked" and should track its fork point
// TODO [Ara] Should provide access to the pointer.
// TODO [Ara] when run it needs to be able to take the current metavariable
//   storage or something.
// TODO [Ara] state needs to contain calldata, memory, stack and storage.
// TODO [Ara] All kinds of memory contain metavariables, which identify semantic
//   threads of data usage, rather than a specific variable location

// TODO [Ara] The addresses may also be symbolic values.

// TODO [Ara] Precomputed keccaks for the early storage slots to help with
//   recognition of constants. With arrays.

// TODO [Ara] Needs to store a mapping from bytecode locations to `Value` UUIDs.
//   Should provide a `new_variable` method.
