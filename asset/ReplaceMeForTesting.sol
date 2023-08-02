// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

contract BytecodeExample {

    // This one is only used in a storage slot, so should be indistinguishable
    // from a packed encoding (done so we force it)
    struct StructOne {
        uint64 one;
        uint128 two;
    }

    // This one we use in a dynamic array as well
    // struct StructTwo {
    //     address addr;
    //     bool isEnabled;
    // }

    // This struct is just used directly.
    StructOne internal data;

    // Here we create a connection between a dynamic array and a storage slot.
    // We should be able to infer a struct type for the slot.
    // StructTwo internal current;
    // StructTwo[] public history;

    function set_data(uint64 one, uint128 two) public {
        data.one = one;
        data.two = two;
    }

    // Updates the current and adds the old one to the history
    // function new_current(address addr, bool isEnabled) public {
    //     history.push(current);
    //     current.addr = addr;
    //     current.isEnabled = isEnabled;
    // }

    // A getter for the current
    // function get_current() public view returns (StructTwo memory) {
    //     return current;
    // }
}
