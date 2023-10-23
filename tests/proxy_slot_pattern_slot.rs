//! This module tests the library's analysis capabilities on the local following
//! reproduction contract.
//!
//! ```text
//! contract ProxyStorage {
//!     bytes32 private constant _SLOT_PROXY_STORAGE = keccak256(abi.encode("io.synthetix.core-contracts.Proxy"));
//!
//!     struct ProxyStore {
//!         address implementation;
//!     }
//!
//!     function _proxyStore() internal pure returns (ProxyStore storage store) {
//!         bytes32 s = _SLOT_PROXY_STORAGE;
//!         assembly {
//!             store.slot := s
//!         }
//!     }
//! }
//!
//! contract UUPSProxyWithOwner is ProxyStorage {
//!     function _forward() public {
//!         address implementation = _getImplementation();
//!     }
//!
//!     function _getImplementation() internal view virtual returns (address) {
//!         return _proxyStore().implementation;
//!     }
//! }
//! ```
//!
//! This contract exposes a proxy slot at a high hashed address, and we want to
//! be able to discover this slot even in the absence of constant-folded slot
//! keys.
#![cfg(test)]

use ethnum::U256;
use storage_layout_extractor::{tc::abi::AbiType, watchdog::LazyWatchdog};

mod common;

/// Tests the library on the bytecode of the above contract.
#[test]
fn correctly_generates_a_layout() -> anyhow::Result<()> {
    // Create the extractor
    let bytecode = "0x608060405234801561001057600080fd5b506004361061002b5760003560e01c8063a168a4cb14610030575b600080fd5b61003861003a565b005b6000610044610049565b905050565b600061005361007c565b60000160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff16905090565b60008060405160200161008e90610130565b6040516020818303038152906040528051906020012090508091505090565b600082825260208201905092915050565b7f696f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f7860008201527f7900000000000000000000000000000000000000000000000000000000000000602082015250565b600061011a6021836100ad565b9150610125826100be565b604082019050919050565b600060208201905081810360008301526101498161010d565b905091905056fea264697066735822122098cb622ce5bec4bbbb0da40f9fd3727a2edb1a72e38d1fbe5c6396566e6d6cbb64736f6c63430008110033";
    let extractor = common::new_extractor_from_bytecode(bytecode, LazyWatchdog.in_rc())?;

    // Get the final storage layout for the input contract
    let layout = extractor.analyze()?;

    // We should see no slots as this contract never uses storage opcodes.
    assert_eq!(layout.slot_count(), 1);

    // `address`, but we infer `uintUnknown` due to lack of information
    assert!(layout.has_slot(
        U256::from_str_hex("0x5a648c35a2f5512218b4683cf10e03f5b7c9dc7346e1bf77d304ae97f60f592b")?,
        0,
        AbiType::UInt { size: None }
    ));

    Ok(())
}
