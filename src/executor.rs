//! This module contains the [`Executor`] and related utilities for symbolically
//! executing, tracing, and manipulating EVM bytecode programs.

/// The [`Executor`] is the component responsible for utilising the [`VM`] to
/// symbolically execute the EVM program.
///
/// It performs collection of evidence for the [`Unifier`] in the form of
/// [`ExecutionTrace`]s.
#[derive(Debug)]
pub struct Executor;
