//! This module deals with the implementation of the symbolic virtual machine.

pub mod instruction_stream;
pub mod state;
pub mod symbolic_value;

/// The virtual machine used to perform symbolic execution of the contract
/// bytecode.
#[derive(Debug)]
pub struct VM {}
