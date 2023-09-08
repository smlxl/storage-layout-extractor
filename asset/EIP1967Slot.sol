// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

contract EIP1967Slot {
    // bytes32(uint256(keccak256("eip1967.proxy.implementation")) - 1))
    bytes32 internal constant _IMPLEMENTATION_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;

    constructor() {
        writeSlot(_IMPLEMENTATION_SLOT, 0x6bf5ed59dE0E19999d264746843FF931c0133090);
    }

    function implementation() public view returns (address) {
        return readSlot(_IMPLEMENTATION_SLOT);
    }

    function writeSlot(bytes32 slot, address value) public {
        assembly {
            sstore(slot, value)
        }
    }

    function readSlot(bytes32 slot) public view returns (address r) {
        assembly {
            r := sload(slot)
        }
    }
}
