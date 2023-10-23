//! This crate contains utility types for dealing with the specifics of which
//! chain the contract being analysed is running on. It is intended that the
//! active chain be used to configure disassembly, the execution semantics in
//! the [`crate::vm::VM`], the particulars of the
//! [`crate::tc::lift::LiftingPasses`] to be run, and the exact
//! [`crate::tc::rule::InferenceRules`] that are used.
//!
//! For now we only deal with Ethereum and the latest fork and so the machinery
//! for switching based on the chain configuration is missing. This will be
//! expanded in the future.

pub mod version;

use crate::extractor::chain::version::EthereumVersion;

/// A representation of the chain on which the contract is running.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Chain {
    /// Ethereum main-net.
    Ethereum { version: EthereumVersion },
}
