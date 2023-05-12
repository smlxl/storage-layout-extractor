//! This module contains the [`Executor`] and related utilities for symbolically
//! executing, tracing, and manipulating EVM bytecode programs.

/// The [`Executor`] is the component responsible for utilising the [`VM`] to
/// symbolically execute the EVM program.
///
/// It performs collection of evidence for the [`Unifier`] in the form of
/// [`ExecutionTrace`]s.
#[derive(Debug)]
pub struct Executor;

// TODO [Ara] We only ever execute every branch once, so need some way to track
//   this.

// TODO [Ara] What does this actually look like?
//   - Need some way to register a "heuristic trace", which is a sequence of
//     operations performed on a given metavariable.
//   - Need some way to look up these traces for each instruction and start
//     collection. A prefix tree, perhaps.
//   - Metavariables eventually come to touch storage slots, carrying their
//     heuristic execution traces with them.

// TODO [Ara] Trace heuristic map/trie, where each opcode is a "character".

// TODO [Ara] The execution trace itself, being a sequence of opcodes that
//   implies some `ImplicationSet`.
