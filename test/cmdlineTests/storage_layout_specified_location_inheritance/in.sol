//SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.27;

contract A {
    uint x;
    uint y;
    int8 z;
}

contract C layout at 42 {
    bool b;
    address addr;
    uint[2] array;
}