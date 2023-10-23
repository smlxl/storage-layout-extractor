//! This module tests the library's analysis capabilities on the local
//! `BatchEnsLookups` contract`.
#![cfg(test)]

use storage_layout_extractor::watchdog::LazyWatchdog;

mod common;

/// Tests the library on the bytecode of the BatchEnsLookups contract
/// found [locally](../asset/BatchEnsLookups.sol).
#[test]
fn correctly_generates_a_layout() -> anyhow::Result<()> {
    // Create the extractor
    let bytecode = "0x6080604052348015600f57600080fd5b506004361060285760003560e01c8063b709959614602d575b600080fd5b60336035565b005b6028600020604051602001604b91815260200190565b60408051601f198184030190525256fea2646970667358221220645e42249fb219b90bda62dd9e9539000ea399d67aa68ba2a3521720a942364964736f6c634300080f0033";
    let extractor = common::new_extractor_from_bytecode(bytecode, LazyWatchdog.in_rc())?;

    // Get the final storage layout for the input contract
    let layout = extractor.analyze()?;

    // We should see no slots as this contract never uses storage opcodes.
    assert!(layout.is_empty());

    Ok(())
}
