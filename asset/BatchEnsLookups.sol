// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

contract BatchEnsLookups {
    function resolveAddresses() public pure  {
        keccak256(
            abi.encodePacked(
                sha3HexAddress()
            )
        );
    }

    function sha3HexAddress() private pure returns (bytes32 ret) {
        assembly {
            ret := keccak256(0, 40)
        }
    }
}
