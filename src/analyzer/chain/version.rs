//! This module contains versioning information for the various EVM-compatible
//! blockchains.
//!
//! For now we only support Shanghai on Ethereum main-net, but this will change
//! in the future.

use std::fmt::Debug;

/// A trait for types that can represent a chain version.
pub trait ChainVersion
where
    Self: Sized + Clone + Debug + Eq + PartialEq,
{
    /// Gets the latest version of the chain.
    fn latest() -> Self;
}

/// Ethereum chain versions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EthereumVersion {
    /// The shanghai fork of ethereum.
    Shanghai,
}

impl ChainVersion for EthereumVersion {
    fn latest() -> Self {
        Self::Shanghai
    }
}
