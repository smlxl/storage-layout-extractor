//! This module contains common testing utilities for testing this library.
#![cfg(test)]

use std::{fs::File, io::Read};

use anyhow::anyhow;
use serde::{Deserialize, Serialize};
use storage_layout_analyzer as sla;
use storage_layout_analyzer::{
    analyzer::{
        chain::{
            version::{ChainVersion, EthereumVersion},
            Chain,
        },
        contract::Contract,
        InitialAnalyzer,
    },
    inference,
    vm,
    watchdog::{DynWatchdog, LazyWatchdog},
};

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

/// Constructs a new analyser to analyze the hex-encoded (with the `0x` prefix)
/// contract bytecode provided in `code` and using the default configurations.
#[allow(unused)] // It is actually
pub fn new_analyzer_from_bytecode(
    code: impl Into<String>,
    watchdog: DynWatchdog,
) -> anyhow::Result<InitialAnalyzer> {
    // Generally unsafe but fine for ASCII so we do it here.
    let bytecode = get_bytecode_from_string(code)?;

    let contract = Contract::new(
        bytecode,
        Chain::Ethereum {
            version: EthereumVersion::latest(),
        },
    );

    let vm_config = vm::Config::default();
    let unifier_config = inference::Config::default();

    Ok(sla::new(contract, vm_config, unifier_config, watchdog))
}

/// Constructs a new analyzer to analyze the contract at the provided `path` and
/// using the default configurations.
#[allow(unused)] // It is actually
pub fn new_analyzer_from_path(path: impl Into<String>) -> anyhow::Result<InitialAnalyzer> {
    let contract = new_contract_from_file(
        path,
        Chain::Ethereum {
            version: EthereumVersion::latest(),
        },
    )?;
    let vm_config = vm::Config::default();
    let unifier_config = inference::Config::default();

    Ok(sla::new(
        contract,
        vm_config,
        unifier_config,
        LazyWatchdog.in_rc(),
    ))
}

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
#[allow(unused)] // It is actually
pub fn new_contract_from_file(path: impl Into<String>, chain: Chain) -> anyhow::Result<Contract> {
    let path = path.into();
    let mut file = File::open(path).map_err(|_| anyhow!("File not available"))?;
    let mut contents = vec![];
    file.read_to_end(&mut contents)
        .map_err(|_| anyhow!("File could not be read"))?;

    let contract_rep: CompiledContract = serde_json::from_slice(contents.as_slice())
        .map_err(|_| anyhow!("Could not parse compiled contract."))?;

    // Generally unsafe but fine for ASCII.
    let bytecode = get_bytecode_from_string(contract_rep.deployed_bytecode.object)?;

    Ok(Contract::new(bytecode, chain))
}

pub fn get_bytecode_from_string(code: impl Into<String>) -> anyhow::Result<Vec<u8>> {
    let bytecode_string = code.into();
    let no_0x_prefix = &bytecode_string[2..];

    let bytecode = hex::decode(no_0x_prefix).map_err(|_| anyhow!("Could not decode hex"))?;
    Ok(bytecode)
}
