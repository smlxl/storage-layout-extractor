// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

contract BytecodeExample {
    error CannotDecrement();

    uint256 public number;

    function setNumber(uint256 newNumber) public {
        number = newNumber;
    }

    function increment() public {
        number++;
    }

    function decrement() public {
        if (number == 0) {
            revert CannotDecrement();
        } else {
            number--;
        }
    }
}
