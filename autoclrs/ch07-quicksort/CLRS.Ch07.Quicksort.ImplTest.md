# Quicksort Spec Validation Test

**File:** `CLRS.Ch07.Quicksort.ImplTest.fst`
**Source:** Adapted from [microsoft/intent-formalization](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
**Status:** ✅ Fully verified — zero admits, zero assumes

## What Is Tested

Three API variants are tested, all on the concrete input `[3; 1; 2]`:

### `test_quicksort_3` — Basic `quicksort`

Calls `quicksort` and proves the postcondition (`sorted s /\ permutation s0 s`)
is satisfiable and fully precise: the output is uniquely determined as `[1; 2; 3]`.

### `test_quicksort_with_complexity` — `quicksort_with_complexity`

Calls `quicksort_with_complexity` with a ghost counter starting at 0 and verifies:
- **Sorted output:** `sorted s`
- **Permutation:** `permutation s0 s`
- **Complexity bound:** `complexity_bounded_quadratic cf 0 3` — at most 3
  comparisons for a 3-element array (n(n-1)/2 = 3·2/2 = 3)
- **Completeness:** output is uniquely `[1; 2; 3]`

### `test_quicksort_bounded` — `quicksort_bounded`

Calls `quicksort_bounded` on the sub-range `a[0..3)` with ghost bounds
`lb=1, rb=3` and verifies:
- **Sorted output:** `sorted s`
- **Permutation:** `permutation s0 s`
- **Bounds preservation:** `between_bounds s 1 3` — all output elements
  remain within `[1, 3]` (strengthened postcondition from Impl.fsti)
- **Completeness:** output is uniquely `[1; 2; 3]`

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

## Spec Precision Result

**The quicksort postcondition is fully precise for this test case.**

Given `sorted s /\ permutation [3; 1; 2] s`, the output is uniquely
determined as `[1; 2; 3]`. This is because all three input elements are
distinct, so there is exactly one sorted permutation.

**The complexity bound is validated:** `quicksort_with_complexity` exposes
`complexity_bounded_quadratic cf 0 3`, confirming at most 3 comparisons.

**Bounds preservation is validated:** `quicksort_bounded` now exposes
`between_bounds s lb rb` in its postcondition (spec strengthened from
original), confirming output elements stay within caller-provided bounds.

## Spec Strengthening (2026-03-17)

The `quicksort_bounded` postcondition was strengthened to expose
`between_bounds s lb rb`. This property was already proven internally
(in `pure_post_quicksort`) but was not exposed in the `Impl.fsti`
interface. The strengthening:

1. Added `between_bounds s lb rb` to `quicksort_bounded` postcondition
   in `CLRS.Ch07.Quicksort.Impl.fsti`
2. No proof changes needed in `Impl.fst` — the property was already
   established by the internal `clrs_quicksort` function
3. Added `test_quicksort_bounded` to validate the strengthened spec

This enables callers of `quicksort_bounded` to directly assert that
output elements remain within the provided bounds, without needing
a separate permutation-preserves-bounds lemma.

## Verification

- **Z3 options:** `--z3rlimit 400 --fuel 8 --ifuel 4`
- **Admits:** 0
- **Assumes:** 0
- **Spec issues found:** `quicksort_bounded` was missing `between_bounds` — now fixed
