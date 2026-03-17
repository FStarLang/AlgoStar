# Merge Sort — Spec Validation Test

## Source

Adapted from [Test.Quicksort.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
in the intent-formalization repository.

## Test Description

`CLRS.Ch02.MergeSort.ImplTest.fst` contains a single Pulse test function
`test_merge_sort_3` that:

1. Allocates a 3-element array with contents `[3; 1; 2]`
2. Allocates a ghost comparison counter initialized to 0
3. Calls `merge_sort arr 3sz ctr`
4. Proves the output is exactly `[1; 2; 3]` using only the postcondition

## What Is Proven

### Precondition satisfiability

The test constructs a valid call site, proving that:
- `SZ.v 3sz == Seq.length s0` (length matches)
- `Seq.length s0 <= A.length a` (array fits)

These are the only preconditions of `merge_sort`, and both are trivially
satisfied by the test setup.

### Postcondition precision (completeness)

The postcondition of `merge_sort` provides:
- `sorted s` — the output is sorted
- `permutation s0 s` — the output is a permutation of the input
- `sort_complexity_bounded cf 0 0 3` — comparisons bounded by `ms_cost(3)`

The test proves that `sorted s ∧ permutation [3;1;2] s` **uniquely determines**
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

### Complexity bound

The postcondition also provides `sort_complexity_bounded cf 0 0 3`, which means
`cf <= ms_cost(3) = merge_sort_ops(3) = 7` (at most 7 comparisons for a
3-element input). This bound is available in the proof context.

## Spec Issues Found

**None.** The specification in `CLRS.Ch02.MergeSort.Impl.fsti` is fully
precise:

- The precondition is satisfiable and minimal (no unnecessary restrictions).
- The postcondition (`sorted ∧ permutation`) uniquely determines the output
  for any given input (up to equal elements).
- The complexity bound is correct for the O(n log n) recurrence.

## Verification

- **Zero admits, zero assumes.**
- Z3 options: `--z3rlimit 400 --fuel 8 --ifuel 4`
