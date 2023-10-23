//! This library implements an analysis of [EVM](https://ethereum.org/en/developers/docs/evm/)
//! bytecode that aims to discover an approximate storage layout for the
//! contract from which the bytecode was compiled. It is _not_ intended to be a
//! full decompiler, and is instead a tool **highly** specialized for performing
//! this discovery process.
//!
//! The analysis it performs is _best effort_, and may produce incorrect
//! results. At the same time, it may also pick up on manual encodings that are
//! not able to be accurately described by Solidity's type system.
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
//!    [`vm::VM`] (an EVM implementation). This execution is a **best-effort**
//!    one, aiming to explore as many code paths as possible while remaining
//!    within tractable bounds. The hope is to gather enough information to
//!    correctly infer the type of a given storage location.
//! 3. For each value seen in the program during execution, the [`vm::VM`]
//!    builds a [`vm::value::SymbolicValue`] (a tree structure) that represents
//!    the operations performed to that particular piece of "data" during
//!    execution. It is these operations that provide evidence toward the type
//!    of the value in question.
//! 4. These execution trees are passed to a type checking process implemented
//!    by the [`tc::TypeChecker`]. This process starts by running multiple
//!    [`tc::lift::Lift`]ing passes. These turn low-level constructs into
//!    more-general high-level ones that are better amenable to type inference.
//!    The results of this lifting are then passed to a series of
//!    [`tc::rule::InferenceRule`]s that output **type judgements** about the
//!    trees they analyse. Finally, the inferences are combined through
//!    unification to perform whole-program type checking.
//! 5. The resolved types associated with each [`layout::StorageSlot`] are
//!    turned into a [`StorageLayout`] that describes the _most concrete_ type
//!    of each storage slot that was encountered. These final types do not
//!    directly correspond to Solidity types, thereby letting downstream tools
//!    implement context-aware processing with as much information as possible.
//!
//! # Basic Usage
//!
//! For the most basic usage of the library, it is sufficient to construct an
//! `Extractor` and call the `.analyze` method, passing your contract.
//!
//! ```
//! use storage_layout_extractor as sle;
//! use storage_layout_extractor::{
//!     bytecode,
//!     extractor::{
//!         chain::{version::EthereumVersion, Chain},
//!         contract::Contract,
//!     },
//!     opcode::{control::*, logic::*, memory::*, Opcode},
//!     tc,
//!     vm,
//!     watchdog::LazyWatchdog,
//! };
//!
//! // This is just a macro that lets us manually write a sequence of opcodes
//! // to be used as bytecode.
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
//! // The library operates on a contract that describes the chain and version
//! // on which it is running. This ensures the most accurate analysis for that
//! // contract.
//! let contract = Contract::new(
//!     bytes,
//!     Chain::Ethereum {
//!         version: EthereumVersion::Shanghai,
//!     },
//! );
//!
//! // The layout is returned from the extractor, and for the purposes of this
//! // example we assume that no errors happen.
//! let layout = sle::new(
//!     contract,
//!     vm::Config::default(),
//!     tc::Config::default(),
//!     LazyWatchdog.in_rc(),
//! )
//! .analyze()
//! .unwrap();
//!
//! // We should only see one slot in this trivial bytecode.
//! assert_eq!(layout.slots().len(), 1);
//! ```
//!
//! # More-Complex Usage
//!
//! While the library provides a high-level interface that automates the vast
//! majority of its execution—from contract ingestion to final output—it also
//! provides comprehensive access to its internals. Very little of the library's
//! functionality is kept private, allowing the analysis to be introspected and
//! modified at every stage of the pipeline.
//!
//! The hope is that novel uses for the library's functionality can be found
//! beyond what it is currently designed for.
//!
//! To get access to this, take a look at the [`extractor`] and the various
//! functions that can be called on the analysis state machine. These provide
//! access to all of the internal data, types, and functionality of the library.
//!
//! Note that the access provided means that it is _possible_ to violate the
//! invariants of the library and the process as a whole. Any function that is
//! capable of doing so is marked as `unsafe`, and should be used with the
//! utmost care.

#![warn(clippy::all, clippy::cargo, clippy::pedantic)]
#![allow(clippy::module_name_repetitions)] // Allows for better API naming

pub mod constant;
pub mod data;
pub mod disassembly;
pub mod error;
pub mod extractor;
pub mod layout;
pub mod opcode;
pub mod tc;
pub mod utility;
pub mod vm;
pub mod watchdog;

// Re-exports to provide the library interface.
pub use extractor::new;
pub use layout::StorageLayout;
