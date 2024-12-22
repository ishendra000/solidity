// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Storage {
    uint256 private number;

    // Store a number
    function setNumber(uint256 _number) public {
        number = _number;
    }

    // Retrieve the stored number
    function getNumber() public view returns (uint256) {
        return number;
    }
}
