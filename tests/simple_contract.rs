//! This module is an integration test that tests the library's analysis
//! capabilities on a very simple, hand-constructed, contract.
#![cfg(test)]

use storage_layout_analyzer::{inference::abi::AbiType, layout::StorageSlot};

mod common;

#[test]
fn analyses_simple_contract() -> anyhow::Result<()> {
    // Create the analyzer
    let contract_path = "./asset/SimpleContract.json";
    let analyzer = common::new_analyzer_from(contract_path)?;

    // Get the final storage layout for the input contract
    let layout = analyzer.analyze()?;

    // Inspect it to check that things are correct
    assert_eq!(layout.slots().len(), 2);

    // Check that we see the `mapping(bytes16 => mapping(bytes16 => bytes32))`
    let expected_mapping = AbiType::Mapping {
        key_tp: Box::new(AbiType::Bytes { length: Some(16) }),
        val_tp: Box::new(AbiType::Mapping {
            key_tp: Box::new(AbiType::Bytes { length: Some(16) }),
            val_tp: Box::new(AbiType::Bytes { length: Some(32) }),
        }),
    };
    let expected_mapping_slot = StorageSlot::new(0, 0, expected_mapping);
    assert!(layout.slots().contains(&expected_mapping_slot));

    // Check that we see the `uint64[]`
    let expected_dyn_array = AbiType::DynArray {
        // Unfortunately we can't currently work out that it's 64 bit as they use a different
        // method to scale the values beyond the supported one
        tp: Box::new(AbiType::UInt { size: None }),
    };
    let expected_array_slot = StorageSlot::new(1, 0, expected_dyn_array);
    assert!(layout.slots().contains(&expected_array_slot));

    Ok(())
}
