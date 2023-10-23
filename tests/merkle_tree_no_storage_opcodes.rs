//! This module tests the library's analysis capabilities on the local
//! `MerkleTree` contract`.
#![cfg(test)]

use storage_layout_extractor::watchdog::LazyWatchdog;

mod common;

/// Tests the library on the bytecode of the MerkleTree contract
/// found [locally](../asset/MerkleTree.sol).
#[test]
fn correctly_generates_a_layout() -> anyhow::Result<()> {
    // Create the extractor
    let bytecode = "0x6080604052348015600f57600080fd5b506004361060285760003560e01c806388572a5c14602d575b600080fd5b60336035565b005b604080516001808252818301909252600091602080830190803683370190505090506000805b8251811015609d57608c838281518110607457607460a2565b60200260200101518360009182526020526040902090565b91508060968160b8565b915050605b565b505050565b634e487b7160e01b600052603260045260246000fd5b60006001820160d757634e487b7160e01b600052601160045260246000fd5b506001019056fea26469706673582212204208c6f43bc343f0a115564be7291cf69f0cd24036b2d9d1701db9b25bf6cb0264736f6c634300080f0033";
    let extractor = common::new_extractor_from_bytecode(bytecode, LazyWatchdog.in_rc())?;

    // Get the final storage layout for the input contract
    let layout = extractor.analyze()?;

    // We should see no slots as this contract never uses storage opcodes.
    assert!(layout.is_empty());

    Ok(())
}
