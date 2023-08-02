//! This module is an integration test that tests the library's analysis
//! capabilities on a hand-constructed contract that uses structs and packed
//! encodings.
#![cfg(test)]

use storage_layout_analyzer::{inference::abi::AbiType, layout::StorageSlot};

mod common;

#[test]
fn analyses_packed_encodings() -> anyhow::Result<()> {
    // Create the analyzer
    let contract_path = "./asset/PackedEncodings.json";
    let analyzer = common::new_analyzer_from(contract_path)?;

    // Get the final storage layout for the input contract
    let layout = analyzer.analyze()?;

    // We should see two 'slots'
    assert_eq!(layout.slots().len(), 2);

    // Check that we see a slot 0 offset 0 containing bytes8
    let expected_bytes_8 = AbiType::Bytes { length: Some(8) };
    let expected_bytes_8_slot = StorageSlot::new(0, 0, expected_bytes_8);
    assert!(layout.slots().contains(&expected_bytes_8_slot));

    // Check that we see a slot 0 offset 64 containing bytes16
    let expected_bytes_16 = AbiType::Bytes { length: Some(16) };
    let expected_bytes_16_slot = StorageSlot::new(0, 64, expected_bytes_16);
    assert!(layout.slots().contains(&expected_bytes_16_slot));

    // All done
    Ok(())
}
