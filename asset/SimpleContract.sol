// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

contract BytecodeExample {
    mapping(uint128 => mapping(uint128 => uint256)) internal mappings;
    uint64[] internal numbers;

    function add(uint128 key, uint256 value) public {
        mappings[key][key] = value;
    }

    function append(uint64 number) public {
        numbers.push(number);
    }

    function read(uint256 index) public view returns (uint64) {
        return numbers[index];
    }
}
