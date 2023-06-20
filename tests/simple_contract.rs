//! This module is an integration test that tests the library's analysis
//! capabilities on a very simple, hand-constructed, contract.
#![cfg(test)]

use storage_layout_analyzer::{layout::StorageSlot, unifier::abi::AbiType};

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

    // Check that we see the `mapping(any => mapping(any => any))`
    let expected_mapping = AbiType::Mapping {
        key_tp: Box::new(AbiType::Any),
        val_tp: Box::new(AbiType::Mapping {
            key_tp: Box::new(AbiType::Any),
            val_tp: Box::new(AbiType::Any),
        }),
    };
    let expected_mapping_slot = StorageSlot::new(0, expected_mapping, false);
    assert!(layout.slots().contains(&expected_mapping_slot));

    // Check that we see the `any[]`
    let expected_dyn_array = AbiType::DynArray {
        tp: Box::new(AbiType::Any),
    };
    let expected_array_slot = StorageSlot::new(1, expected_dyn_array, false);
    assert!(layout.slots().contains(&expected_array_slot));

    Ok(())
}
