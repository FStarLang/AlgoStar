# Quicksort Spec Validation Test

**File:** `CLRS.Ch07.Quicksort.ImplTest.fst`
**Source:** Adapted from [microsoft/intent-formalization](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
**Status:** ✅ Fully verified — zero admits, zero assumes

## What Is Tested

The test calls `quicksort` on the concrete input `[3; 1; 2]` and proves
that the postcondition (`sorted s /\ permutation s0 s`) is:

1. **Satisfiable** — the function can be called with a valid 3-element array.
2. **Precise** — the postcondition uniquely determines the output as `[1; 2; 3]`.

After `quicksort arr 3sz` returns, the test:

- Reveals the opaque `permutation` to expose `FStar.Seq.Properties.permutation`.
- Bridges `BoundedIntegers` typeclass operators (`<=`, `<`) to `Prims` operators
  so Z3 can reason about integer ordering in conjunction with permutation counts.
- Uses `SP.count` normalization to establish element multiplicities.
- Reads all three array elements and asserts `v0 == 1 /\ v1 == 2 /\ v2 == 3`.

## Key Lemmas

### `std_sort3`

Proves: if a sequence is sorted (via `Prims.op_LessThanOrEqual`) and is a
permutation of `[3; 1; 2]`, then it must be `[1; 2; 3]`.

Uses `SP.count` to establish that the permutation has exactly one copy of
each of `{1, 2, 3}` and zero copies of `{0, 4}`. Combined with the sorted
constraint, this uniquely determines the sequence.

### `completeness_sort3`

Bridges `CLRS.Common.SortSpec.sorted` (which uses `Pulse.Lib.BoundedIntegers`
typeclass operators) to the `Prims` operators used by `std_sort3`.

The bridge consists of four assertions:
```fstar
assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
assert (forall (i j:nat). (i < j) == Prims.op_LessThan i j);
assert (forall (x y:int). (x <= y) == Prims.op_LessThanOrEqual x y);
assert (forall (x y:int). (x < y) == Prims.op_LessThan x y);
```

These are provable because `bounded_int_int` and `bounded_int_nat` define
their comparison operators directly as the corresponding `Prims` operators.

## Spec Precision Result

**The quicksort postcondition is fully precise for this test case.**

Given `sorted s /\ permutation [3; 1; 2] s`, the output is uniquely
determined as `[1; 2; 3]`. This is because all three input elements are
distinct, so there is exactly one sorted permutation.

No assumptions or admits were needed. The postcondition is sufficient to
determine the exact output for any input with distinct elements.

## Verification

- **Z3 options:** `--z3rlimit 400 --fuel 8 --ifuel 4`
- **Admits:** 0
- **Assumes:** 0
- **Spec issues found:** None
