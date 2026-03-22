# Merge Sort — Spec Validation Test

## Source

Adapted from [Test.Quicksort.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
in the intent-formalization repository.

## Test Description

`CLRS.Ch02.MergeSort.ImplTest.fst` contains three Pulse test functions:

### `test_merge_sort_3` (main test)

1. Allocates a 3-element array with contents `[3; 1; 2]`
2. Allocates a ghost comparison counter initialized to 0
3. Calls `merge_sort arr 3sz ctr`
4. Proves the output is exactly `[1; 2; 3]` using only the postcondition
5. Asserts `cf <= 7` (at most `ms_cost(3) = merge_sort_ops(3) = 7` comparisons)

### `test_merge_sort_empty` (edge case)

1. Allocates a 0-element array
2. Calls `merge_sort arr 0sz ctr`
3. Asserts `cf == 0` (zero comparisons for empty input)

### `test_merge_sort_single` (edge case)

1. Allocates a 1-element array with contents `[42]`
2. Calls `merge_sort arr 1sz ctr`
3. Asserts `cf == 0` (zero comparisons for single-element input)

## What Is Proven

### Precondition satisfiability

All three tests construct valid call sites, proving that:
- `SZ.v len == Seq.length s0` (length matches)
- `Seq.length s0 <= A.length a` (array fits)

These are the only preconditions of `merge_sort`, and all are trivially
satisfied by the test setups.

### Postcondition precision (completeness)

The postcondition of `merge_sort` provides:
- `sorted s` — the output is sorted
- `permutation s0 s` — the output is a permutation of the input
- `sort_complexity_bounded cf 0 0 n` — comparisons bounded by `ms_cost(n)`

The main test proves that `sorted s ∧ permutation [3;1;2] s` **uniquely determines**
`s = [1;2;3]`. This is done via:

1. **`reveal_opaque`** on the opaque `SS.permutation` to expose
   `SP.permutation int s0 s` to the SMT solver.
2. **`completeness_sort3`** lemma that bridges BoundedIntegers `<=`/`<`
   operators to standard `Prims.op_LessThanOrEqual`/`Prims.op_LessThan` so Z3
   can reason about the ordering.
3. **`std_sort3`** lemma that uses `SP.perm_len` and `assert_norm` on
   `SP.count` to prove that a sorted permutation of `[3;1;2]` must be
   `[1;2;3]`.

After the lemma, each element is read from the array and asserted to match
the expected value:
```
assert (pure (v0 == 1));
assert (pure (v1 == 2));
assert (pure (v2 == 3));
```

### Complexity bound (explicit)

The main test explicitly asserts `cf <= 7`, verifying that the complexity
bound `merge_sort_ops(3) = 7` is concrete and usable from the postcondition.
This was previously impossible because `merge_sort_ops` was hidden behind a
`val` in `Complexity.fsti`; the definitions of `ceil_div2` and
`merge_sort_ops` are now exposed as `let` definitions, allowing Z3 to
normalize `ms_cost(3)` to 7 with sufficient fuel.

The edge-case tests assert `cf == 0`, verifying that:
- Empty input (n=0): `sort_complexity_bounded cf 0 0 0` implies `cf == 0`
  (since `ms_cost(0) = 0`, and `cf >= 0`)
- Single element (n=1): `sort_complexity_bounded cf 0 0 1` implies `cf == 0`
  (since `ms_cost(1) = merge_sort_ops(1) = 0`, and `cf >= 0`)

## Spec Issues Found and Resolved

**Issue:** `merge_sort_ops` was declared as an opaque `val` in
`Complexity.fsti`, preventing clients from computing concrete complexity
bounds like `ms_cost(3) = 7`. The postcondition `sort_complexity_bounded cf 0
0 3` was in the proof context but could not be resolved to `cf <= 7`.

**Resolution:** Exposed `ceil_div2` and `merge_sort_ops` as `let`
definitions in `Complexity.fsti`. All 16 ch02 modules still verify. The test
now explicitly asserts `cf <= 7`.

## Verification

- **Zero admits, zero assumes.**
- Z3 options: `--z3rlimit 400 --fuel 8 --ifuel 4`

## Concrete Execution (C Extraction)

The implementation is extracted to C via KaRaMeL (`make test-c`) and tested
against the same inputs as the proof tests, plus additional stress tests.

**Extraction note:** The `int` comparison operator (`<=`) in `Impl.fst`
uses explicit `Prims.op_LessThanOrEqual` instead of the
`Pulse.Lib.BoundedIntegers` typeclass overload, because KaRaMeL cannot
extract the typeclass dictionary pattern for `bounded_int_int`. The
semantics are identical.

### Test Results

```
=== Merge Sort ===
  PASS: sort [3,1,2] => [1, 2, 3]
  PASS: sort [] (empty)
  PASS: sort [42] => [42]
  PASS: sort [1,2,3,4,5] => [1, 2, 3, 4, 5]
  PASS: sort [5,4,3,2,1] => [1, 2, 3, 4, 5]
  PASS: sort [3,1,3,1,2] => [1, 1, 2, 3, 3]
```

All 6 tests pass. The extracted C code correctly implements merge sort
with the same behavior proven by the formal verification.
