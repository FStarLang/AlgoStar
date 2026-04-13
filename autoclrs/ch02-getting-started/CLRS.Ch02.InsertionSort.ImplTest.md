# Insertion Sort — Spec Validation Test

## Source

Adapted from [Test.Quicksort.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
in the intent-formalization repository.

## Test Description

`CLRS.Ch02.InsertionSort.ImplTest.fst` contains three Pulse test functions:

### `test_insertion_sort_3` (main test)

1. Allocates a 3-element array with contents `[3; 1; 2]`
2. Allocates a ghost comparison counter initialized to 0
3. Calls `insertion_sort arr 3sz ctr`
4. Proves the output is exactly `[1; 2; 3]` using only the postcondition
5. Asserts `cf <= 3` (at most n*(n-1)/2 = 3 comparisons)

### `test_insertion_sort_empty` (edge case)

1. Allocates a 0-element array
2. Calls `insertion_sort arr 0sz ctr`
3. Asserts `cf == 0` (zero comparisons for empty input)

### `test_insertion_sort_single` (edge case)

1. Allocates a 1-element array with contents `[42]`
2. Calls `insertion_sort arr 1sz ctr`
3. Asserts `cf == 0` (zero comparisons for single-element input)

## What Is Proven

### Precondition satisfiability

All three tests construct valid call sites, proving that:
- `SZ.v len == Seq.length s0` (length matches)
- `Seq.length s0 <= A.length a` (array fits)

These are the only preconditions of `insertion_sort`, and all are trivially
satisfied by the test setups.

### Postcondition precision (completeness)

The postcondition of `insertion_sort` provides:
- `sorted s` — the output is sorted
- `permutation s0 s` — the output is a permutation of the input
- `complexity_bounded cf 0 n` — at most n*(n-1)/2 comparisons

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

The main test explicitly asserts `cf <= 3`, verifying that the complexity
bound `n*(n-1)/2 = 3*2/2 = 3` is concrete and usable from the postcondition.

The edge-case tests assert `cf == 0`, verifying that:
- Empty input (n=0): `complexity_bounded cf 0 0` implies `cf == 0`
  (since 0*(0-1)/2 = 0, and `cf >= 0`)
- Single element (n=1): `complexity_bounded cf 0 1` implies `cf == 0`
  (since 1*(1-1)/2 = 0, and `cf >= 0`)

## Spec Issues Found

**None.** The specification in `CLRS.Ch02.InsertionSort.Impl.fsti` is fully
precise:

- The precondition is satisfiable and minimal (no unnecessary restrictions).
- The postcondition (`sorted ∧ permutation`) uniquely determines the output
  for any given input (up to equal elements).
- The complexity bound is tight for the worst case and concretely evaluable.
- Edge cases (len=0, len=1) are correctly handled with zero comparisons.

## Verification

- **Zero admits, zero assumes.**
- Z3 options: `--z3rlimit 400 --fuel 8 --ifuel 4`

## Concrete Execution (C Extraction)

The implementation is extracted to C via KaRaMeL (`make test-c`) and tested
against the same inputs as the proof tests, plus additional stress tests.

**Extraction note:** The `int` comparison operators (`>`, `<=`) in
`Impl.fst` use explicit `Prims.op_GreaterThan` / `Prims.op_LessThanOrEqual`
instead of the `Pulse.Lib.BoundedIntegers` typeclass overloads, because
KaRaMeL cannot extract the typeclass dictionary pattern for
`bounded_int_int`. The semantics are identical (the typeclass instance for
`int` delegates directly to these Prims operators).

### Test Results

```
--- Insertion Sort tests ---
  PASS: sort [3,1,2] => [1,2,3]
  PASS: sort [] (empty)
  PASS: sort [42] (single)
```

All 3 tests pass. The extracted C code correctly implements insertion sort
with the same behavior proven by the formal verification.
