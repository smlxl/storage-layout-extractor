//! This module contains types useful for dealing with concrete contracts that
//! you want to analyze.

use std::{fs::File, io::Read};

use anyhow::anyhow;
use serde::{Deserialize, Serialize};

use crate::analyzer::chain::Chain;

/// A representation of a contract that is passed to the library.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Contract {
    bytecode: Vec<u8>,
    chain:    Chain,
}

impl Contract {
    // TODO [Anybody] The from-file functionality should eventually be handled by
    //   the CLI. This includes implementing CBOR metadata handling. It exists here
    //   for now to enable experimentation.

    /// Creates a new contract from the file at the provided `path`.
    ///
    /// The file at `path` must be a compiled representation of a Solidity
    /// contract, usually output as JSON, and compiled without the CBOR
    /// metadata.
    ///
    /// If using `forge` you will need to set the following in your
    /// `foundry.toml`:
    ///
    /// ```toml
    /// cbor_metadata = false
    /// bytecode_hash = "none"
    /// ```
    pub fn new_from_file(path: impl Into<String>, chain: Chain) -> anyhow::Result<Self> {
        let path = path.into();
        let mut file = File::open(path).map_err(|_| anyhow!("File not available"))?;
        let mut contents = vec![];
        file.read_to_end(&mut contents)
            .map_err(|_| anyhow!("File could not be read"))?;

        let contract_rep: CompiledContract = serde_json::from_slice(contents.as_slice())
            .map_err(|_| anyhow!("Could not parse compiled contract."))?;

        // Generally unsafe but fine for ASCII.
        let bytecode_string = contract_rep.deployed_bytecode.object;
        let no_0x_prefix = &bytecode_string[2..];

        let bytecode = hex::decode(no_0x_prefix).map_err(|_| anyhow!("Could not decode hex"))?;

        Ok(Self { bytecode, chain })
    }

    /// Creates a new contract from the provided `bytecode` and `chain`.
    ///
    /// This must be the contract bytecode _without_ the CBOR metadata.
    pub fn new(bytecode: Vec<u8>, chain: Chain) -> Self {
        Self { bytecode, chain }
    }

    /// Gets a reference to the bytecode of the contract.
    pub fn bytecode(&self) -> &Vec<u8> {
        &self.bytecode
    }

    /// Gets a reference to the chain on which the contract is running.
    pub fn chain(&self) -> &Chain {
        &self.chain
    }
}

// TODO [Anybody] These are temporary (see above TODO)

/// A wrapper for the parts of the JSON representation of the compiled contract
/// on disk that we care about.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompiledContract {
    deployed_bytecode: DeployedBytecode,
}
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DeployedBytecode {
    object: String,
}
