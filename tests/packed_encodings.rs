//! This module is an integration test that tests the library's analysis
//! capabilities on a hand-constructed contract that uses structs and packed
//! encodings.
#![cfg(test)]

use storage_layout_analyzer::tc::abi::AbiType;

mod common;

#[test]
fn analyses_packed_encodings() -> anyhow::Result<()> {
    // Create the analyzer
    let contract_path = "./asset/PackedEncodings.json";
    let analyzer = common::new_analyzer_from_path(contract_path)?;

    // Get the final storage layout for the input contract
    let layout = analyzer.analyze()?;

    // We should see two 'slots'
    assert_eq!(layout.slot_count(), 2);

    // Check that we see a slot 0 offset 0 containing bytes8
    assert!(layout.has_slot(0, 0, AbiType::Bytes { length: Some(8) }));

    // Check that we see a slot 0 offset 64
    assert!(layout.has_slot(0, 64, AbiType::Bytes { length: Some(16) }));

    // All done
    Ok(())
}
