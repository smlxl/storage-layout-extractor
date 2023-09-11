// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

contract MerkleTree {
    function purchaseMerkleAmount() external {
        bytes32[] memory proof = new bytes32[](1);
        bytes32 computedHash = bytes32(0);
        for (uint256 i = 0; i < proof.length; i++) {
            computedHash = _efficientHash(proof[i], computedHash);
        }
    }

    function _efficientHash(bytes32 a, bytes32 b) private pure returns (bytes32 value) {
        /// @solidity memory-safe-assembly
        assembly {
            mstore(0x00, a)
            mstore(0x20, b)
            value := keccak256(0x00, 0x40)
        }
    }
}
