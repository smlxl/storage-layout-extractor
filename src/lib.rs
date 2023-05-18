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
//! 4. The [`unifier::Unifier`] takes those execution trees as evidence,
//!    and combines the implications through the use of
//!    [`unifier::implication::Set`]s to resolve the most concretely-known type
//!    of the symbolic value in a form of usage-based type inference.
//! 5. The types that are associated with storage slots are taken and written to
//!    a [`StorageLayout`] that can then be output.

#![warn(clippy::all, clippy::cargo)]

pub mod constant;
pub mod error;
pub mod opcode;
pub mod unifier;
pub mod vm;

/// The core of the storage layout analysis, the `Analyzer` is responsible for
/// ingesting user data and outputting a storage layout.
pub struct Analyzer;

/// The most-concrete layout discovered for the input contract.
pub struct StorageLayout;
