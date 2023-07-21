// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

contract BytecodeExample {

    // This one is only used in a storage slot, so should be indistinguishable
    // from a packed encoding (done so we force it)
    struct StructOne {
        uint64 one;
        uint128 two;
    }

    // This struct is just used directly.
    StructOne internal data;

    function set_data(uint64 one, uint128 two) public {
        data.one = one;
        data.two = two;
    }
}
