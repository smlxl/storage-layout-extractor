//! This crate contains utility types for dealing with the specifics of which
//! chain the contract being analysed is running on.
//!
//! For now we only deal with Ethereum and the latest fork, but this will be
//! expanded in the future.

pub mod version;

use crate::analyzer::chain::version::EthereumVersion;

/// A representation of the chain on which the contract is running.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Chain {
    /// Ethereum main-net.
    Ethereum { version: EthereumVersion },
}
