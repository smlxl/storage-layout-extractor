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
//!
//! # Basic Usage
//!
//! For the most basic usage of the library, it is sufficient to construct an
//! `Analyzer` and call the `.analyze` method, passing your contract.
//!
//! ```
//! use storage_layout_analyzer as sla;
//! use storage_layout_analyzer::{
//!     analyzer::chain::{version::EthereumVersion, Chain},
//!     bytecode,
//!     contract::Contract,
//!     opcode::{control::*, logic::*, memory::*, Opcode},
//!     unifier,
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
//! let layout = sla::new(contract, vm::Config::default(), unifier::Config::default())
//!     .analyze()
//!     .unwrap();
//!
//! assert_eq!(layout.slots().len(), 1);
//! ```

#![warn(clippy::all, clippy::cargo, clippy::pedantic)]
#![allow(clippy::module_name_repetitions)] // Allows for better API naming

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
