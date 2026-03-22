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

## C Extraction and Concrete Execution (2026-03-22)

### Extraction Pipeline

The verified Pulse code was extracted to C via karamel (krml) and executed:

1. **F\* → .krml:** `ImplTest`, `Quicksort.Impl`, and `Partition.Impl` modules
   extracted using `--codegen krml`
2. **krml → C:** Translated via karamel with `-library CLRS.Ch07.Partition.Impl`
   (workaround for a karamel `remove_unused_parameters` crash when all three
   modules are processed together)
3. **Partition in C:** Hand-written `CLRS_Ch07_Partition_Impl.c` provides the
   Lomuto partition, matching krml's erased signature exactly
4. **Compiled:** With `krmllib` runtime (prims.c for checked integer arithmetic)
5. **Executed:** All tests pass

### Test Results

```
=== Extracted test functions (crash = fail) ===
  PASS: test_quicksort_3 completed
  PASS: test_quicksort_with_complexity completed
  PASS: test_quicksort_bounded completed

=== Concrete verification ===
  PASS: quicksort [3,1,2] -> arr[0]==1
  PASS: quicksort [3,1,2] -> arr[1]==2
  PASS: quicksort [3,1,2] -> arr[2]==3
  PASS: quicksort_bounded [3,1,2] -> arr[0]==1
  PASS: quicksort_bounded [3,1,2] -> arr[1]==2
  PASS: quicksort_bounded [3,1,2] -> arr[2]==3
  PASS: quicksort [1..5] -> sorted
  PASS: quicksort [5..1] -> sorted
  PASS: quicksort [42] -> [42]
  PASS: quicksort [3,1,2,1,3] -> [1,1,2,3,3]

13/13 tests passed
```

### Extraction Notes

- **Ghost erasure:** All ghost operations (GR.alloc/free, assertions,
  reveal_opaque, complexity counters) correctly erased by krml
- **Type mapping:** F\*'s `int` maps to `krml_checked_int_t` (= `int32_t`)
  with runtime overflow checking via krmllib
- **Vec operations:** `V.alloc`/`V.free` extract to `KRML_HOST_CALLOC`/`KRML_HOST_FREE`
- **Erased parameters:** Ghost bounds (`lb`, `rb`), ghost sequences (`#s0`),
  and ghost counters (`ctr`, `#c0`) all erased to `(void *)0U`
- **Build command:** `make test-c` in ch07-quicksort directory
