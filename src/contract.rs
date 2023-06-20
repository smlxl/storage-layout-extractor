//! This module contains types useful for dealing with concrete contracts that
//! you want to analyze.

use crate::analyzer::chain::Chain;

/// A representation of a contract that is passed to the library.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Contract {
    bytecode: Vec<u8>,
    chain:    Chain,
}

impl Contract {
    /// Creates a new contract from the provided `bytecode` and `chain`.
    ///
    /// This must be the contract bytecode _without_ the CBOR metadata.
    #[must_use]
    pub fn new(bytecode: Vec<u8>, chain: Chain) -> Self {
        Self { bytecode, chain }
    }

    /// Gets a reference to the bytecode of the contract.
    #[must_use]
    pub fn bytecode(&self) -> &Vec<u8> {
        &self.bytecode
    }

    /// Gets a reference to the chain on which the contract is running.
    #[must_use]
    pub fn chain(&self) -> &Chain {
        &self.chain
    }
}
