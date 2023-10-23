//! This module provides a simple integration test that ensures that we can
//! discover very large slot numbers such as those used in EIP-1967 based
//! contracts.
#![cfg(test)]

use ethnum::U256;
use storage_layout_extractor::{tc::abi::AbiType, watchdog::LazyWatchdog};

mod common;

#[test]
fn correctly_returns_large_slot() -> anyhow::Result<()> {
    // Create the extractor
    let bytecode = "0x608060405234801561001057600080fd5b50600436106100415760003560e01c80635c60da1b14610046578063b06cb8991461006a578063e8e834a91461007e575b600080fd5b61004e610090565b6040516001600160a01b03909116815260200160405180910390f35b61007c6100783660046100bf565b9055565b005b61004e61008c3660046100fb565b5490565b60006100ba7f360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc5490565b905090565b600080604083850312156100d257600080fd5b8235915060208301356001600160a01b03811681146100f057600080fd5b809150509250929050565b60006020828403121561010d57600080fd5b503591905056fea2646970667358221220d65a69a7da4e10e131d4d9d13cf5abd64991e0201c1d86b2c4cb0c4aef279e1764736f6c63430008090033";
    let extractor = common::new_extractor_from_bytecode(bytecode, LazyWatchdog.in_rc())?;

    // Get the final storage layout for the input contract
    let layout = extractor.analyze()?;

    // Inspect it to check that things are correct
    assert_eq!(layout.slot_count(), 1);

    // Check that we see a slot at the huge value
    assert!(layout.has_slot(
        U256::from_str_hex("0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc")?,
        0,
        AbiType::Bytes { length: Some(20) }
    ));

    Ok(())
}
