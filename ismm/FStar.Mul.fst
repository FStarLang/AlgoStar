module FStar.Mul

// Compatibility shim: FStar.Mul was removed in F* nightly-2026-04-29.
// The multiplication operator is now op_Star rather than op_Multiply.

let op_Multiply (x y: int) : int = x * y
