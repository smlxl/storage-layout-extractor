//! This library implements an analysis of [EVM](https://ethereum.org/en/developers/docs/evm/)
//! bytecode that aims to discover an approximate storage layout for the
//! contract from which the bytecode was compiled. It is _not_ intended to be a
//! full decompiler, and is instead a tool **highly** specialized for performing
//! this discovery process.
//!
//! The analysis it performs is _best effort_, and may produce incorrect
//! results.
//!
//! # How it Works
//!
//! From a very high level, the storage layout discovery process is performed as
//! follows:
//!
//! 1. Bytecode is ingested and disassembled into an
//!    [`disassembly::InstructionStream`] that is amenable to dynamic analysis.
//!    This is a sequence of [`opcode::Opcode`]s that is equivalent to the
//!    bytecode.
//! 2. The stream of instructions is executed symbolically on a specialised
//!    [`vm::VM`] (an EVM implementation). This execution is both
//!    **speculative** and **total**, exploring all possible code paths that can
//!    influence the type attributed to a given storage location.
//! 3. For each value seen in the program during execution, the [`vm::VM`]
//!    builds a [`vm::value::SymbolicValue`] (a little tree structure) that
//!    represents the operations performed to that particular piece of "data".
//! 4. These execution trees are passed to a type inference process implemented
//!    by the [`inference::InferenceEngine`]. This process starts by running
//!    multiple [`inference::lift::Lift`]s, that turn low-level constructs into
//!    more-general high-level ones. The results of this lifting are then passed
//!    to a series of [`inference::rule::InferenceRule`]s that output **type
//!    inference judgements** about the trees they analyse. Finally, thee
//!    inferences are combined through unification to perform whole-program type
//!    inference.
//! 5. The resolved types associated with each [`layout::StorageSlot`] are
//!    turned into a [`StorageLayout`] that describes the type of each storage
//!    slot that was encountered.
//!
//! # Basic Usage
//!
//! For the most basic usage of the library, it is sufficient to construct an
//! `Analyzer` and call the `.analyze` method, passing your contract.
//!
//! ```
//! use storage_layout_analyzer as sla;
//! use storage_layout_analyzer::{
//!     analyzer::{
//!         chain::{version::EthereumVersion, Chain},
//!         contract::Contract,
//!     },
//!     bytecode,
//!     inference,
//!     opcode::{control::*, logic::*, memory::*, Opcode},
//!     vm,
//! };
//!
//! let bytes = bytecode![
//!     CallDataSize,                       // Get a symbolic value
//!     IsZero,                             // Check if the size is zero
//!     PushN::new(1, vec![0x0b]).unwrap(), // Push the jump destination offset onto the stack
//!     JumpI,                              // Jump if the condition is true
//!     PushN::new(1, vec![0x00]).unwrap(), // Value to store
//!     PushN::new(1, vec![0x00]).unwrap(), // Key under which to store it
//!     SStore,                             // Storage
//!     Invalid::default(),                 // Return from this thread with invalid instruction
//!     JumpDest,                           // The destination for the jump
//!     PushN::new(1, vec![0xff]).unwrap(), // The value to store into memory
//!     PushN::new(1, vec![0x00]).unwrap(), // The offset in memory to store it at
//!     MStore,                             // Store to memory
//!     PushN::new(1, vec![0x01]).unwrap(), // The size of the data to return
//!     PushN::new(1, vec![0x00]).unwrap(), // The location in memory to return
//!     Return                              // Return from this thread
//! ];
//!
//! let contract = Contract::new(
//!     bytes,
//!     Chain::Ethereum {
//!         version: EthereumVersion::Shanghai,
//!     },
//! );
//!
//! let layout = sla::new(
//!     contract,
//!     vm::Config::default(),
//!     inference::Config::default(),
//! )
//! .analyze()
//! .unwrap();
//!
//! assert_eq!(layout.slots().len(), 1);
//! ```
//!
//! ## More-Complex Usage
//!
//! While the library provides a high-level interface that automates the vast
//! majority of its execution—from contract ingestion to layout output—it also
//! provides access to its internals. Very little of the library's functionality
//! is kept private, allowing the analysis to be introspected and modified at
//! every stage of the pipeline.
//!
//! The hope is that novel uses for the library's functionality can be found
//! beyond what it is currently envisioned for.
//!
//! To get access to this, take a look at the [`analyzer`] and the various
//! functions that can be called on the analysis state machine. These provide
//! access to all of the internal data, types, and functionality of the library.
//!
//! Note that the access provided means that it is _possible_ to violate the
//! invariants of the library and the process as a whole. Any function that is
//! capable of doing so is marked as `unsafe`, and should be used with the
//! utmost care.

#![warn(clippy::all, clippy::cargo, clippy::pedantic)]
#![allow(clippy::module_name_repetitions)] // Allows for better API naming

pub mod analyzer;
pub mod constant;
pub mod disassembly;
pub mod error;
pub mod inference;
pub mod layout;
pub mod opcode;
pub mod vm;

// Re-exports to provide the library interface.
pub use analyzer::new;
pub use layout::StorageLayout;
