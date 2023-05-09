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
//! 1. Bytecode is ingested and turned into an [`InstructionStream`]. This is a
//!    sequence of [`Opcode`]s that is equivalent to the bytecode.
//! 2. The stream of instructions is executed symbolically on a specialised
//!    [`VM`]. This execution is both speculative and total, exploring all
//!    possible code paths that can influence the type of a storage location.
//! 3. For each [`Metavariable`], the [`Executor`] collects one or more
//!    [`ExecutionTrace`]s that provide evidence as to the type of the
//!    [`Metavariable`].
//! 4. The [`Unifier`] takes these [`ExecutionTrace`]s as evidence, and combines
//!    the [`Implication`]s through use of [`ImplicationSet`]s to resolve the
//!    most concretely known type of the [`Metavariable`]. This is a form of
//!    usage-based type inference.
//! 5. From there, the [`StorageLayout`] can be output.

extern crate core;

pub mod opcode;
pub mod vm;
