//! This library implements an analysis of [EVM](https://ethereum.org/en/developers/docs/evm/)
//! bytecode that aims to discover the storage layout—namely, what type the
//! variable is for a given slot—of the contract being studied. It is a _best
//! effort_ analysis.
//!
//! Note that this library is not intended to be nor expected to evolve into a
//! full decompiler for EVM bytecode.
//!
//! # How it Works
//!
//! From a very high level, the storage layout discovery process is performed as
//! follows:
//!
//! 1. Bytecode is ingested and turned into an
//!    [`vm::instructions::InstructionStream`]. This is a sequence of
//!    [`opcode::Opcode`]s that is equivalent to the bytecode.
//! 2. The stream of instructions is executed symbolically on a specialised
//!    [`vm::VM`]. This execution is both speculative and total, exploring all
//!    possible code paths that can influence the type of a storage location.
//! 3. For each [`vm::value::SymbolicValue`], the [`vm::VM`] collects an
//!    execution tree that provides evidence as to the type of that variable.
//! 4. The [`unifier::Unifier`] takes those execution trees as evidence, and
//!    performs a process of lifting, heuristic evidence discovery, and
//!    subsequent unification to discover the types in the program.
//! 5. The types that are associated with storage slots are taken and written to
//!    a [`StorageLayout`] that can then be output.

#![warn(clippy::all, clippy::cargo)]

pub mod analyzer;
pub mod constant;
pub mod contract;
pub mod error;
pub mod layout;
pub mod opcode;
pub mod unifier;
pub mod vm;

// Re-exports to provide the library interface.
pub use analyzer::new;
pub use layout::StorageLayout;
