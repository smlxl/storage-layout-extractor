// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;


contract Thing {
    address private _padding;
    mapping(uint256 => address) private _addrs;

    function setPadding(address padding) public {
        _padding = padding;
    }

    function getPadding() public view returns (address) {
        return _padding;
    }

    function setAddr(uint256 key, address addr_) public {
        _addrs[key] = addr_;
    }

    function getAddr(uint256 key) public view returns (address) {
        return _addrs[key];
    }
}
