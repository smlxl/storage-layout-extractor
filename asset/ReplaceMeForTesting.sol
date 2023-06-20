// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

contract BytecodeExample {
    mapping(uint256 => mapping(uint256 => uint256)) internal number;
    uint256[] internal numbers;

    function add(uint256 key, uint256 value) public {
        number[key][key] = value;
    }

    function append(uint256 number) public {
        numbers.push(number);
    }
}
