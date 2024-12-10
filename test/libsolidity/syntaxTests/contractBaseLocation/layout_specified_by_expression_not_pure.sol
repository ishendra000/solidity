function f(uint x) returns (uint) { return x + 1; }
contract A layout at f(2) {}
// ----
// TypeError 1139: (73-77): The contract base location must be an expression that can be evaluated at compilation time.
// TypeError 6396: (73-77): Only number literals are accepted in the expression specifying the contract base storage location.
