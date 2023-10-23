//! This module is an integration test that tests the library's analysis
//! capabilities on a very simple, hand-constructed, contract.
#![cfg(test)]

use storage_layout_extractor::tc::abi::AbiType;

mod common;

#[test]
fn analyses_simple_contract() -> anyhow::Result<()> {
    // Create the extractor
    let contract_path = "./asset/SimpleContract.json";
    let extractor = common::new_extractor_from_path(contract_path)?;

    // Get the final storage layout for the input contract
    let layout = extractor.analyze()?;

    // Inspect it to check that things are correct
    assert_eq!(layout.slot_count(), 2);

    // Check that we see the `mapping(bytes16 => mapping(bytes16 => bytes32))`
    assert!(layout.has_slot(
        0,
        0,
        AbiType::Mapping {
            key_type:   Box::new(AbiType::Bytes { length: Some(16) }),
            value_type: Box::new(AbiType::Mapping {
                key_type:   Box::new(AbiType::Bytes { length: Some(16) }),
                value_type: Box::new(AbiType::Bytes { length: Some(32) }),
            }),
        }
    ));

    // `uint64[]` but we infer conflict
    assert!(layout.has_slot(1, 0, AbiType::conflict()));

    Ok(())
}
