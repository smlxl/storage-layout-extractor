//! This module contains types useful for dealing with concrete contracts that
//! you want to analyze.

use crate::extractor::chain::Chain;

/// The contract that is to be analyzed by the library.
///
/// This includes the configuration of the chain on which it is to be executed,
/// and is intended to be immutable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Contract {
    /// The bytecode of the contract.
    bytecode: Vec<u8>,

    /// The chain on which the contract is running.
    chain: Chain,
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
