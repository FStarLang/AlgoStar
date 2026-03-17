# Partition Spec Validation Test

**File:** `CLRS.Ch07.Partition.ImplTest.fst`
**Status:** ✅ Fully verified — zero admits, zero assumes

## What Is Tested

The test calls `clrs_partition_wrapper_with_ticks` on the concrete input
`[3; 1; 2]` with bounds `lb=1, rb=3` and proves that the postcondition is:

1. **Satisfiable** — the function can be called with a valid 3-element array,
   ghost bounds, and ghost counter.
2. **Meaningful** — the postcondition constraints (bounds, strict ordering,
   permutation, exact complexity) are all verified in-line.

After the partition call returns, the test verifies:

- **Pivot index in range:** `0 <= p < 3`
- **Sub-array lengths consistent:** `|s1| == p`, `|s_pivot| == 1`, `|s2| == 2 - p`
- **Pivot value in bounds:** `1 <= pivot <= 3`
- **Left partition bounded:** `between_bounds s1 1 pivot` (all elements ≤ pivot)
- **Right partition strict:** `strictly_larger_than s2 pivot` (all elements > pivot)
- **Exact complexity:** `complexity_exact_linear cf 0 2` (exactly 2 comparisons)
- **Permutation preserved:** the concatenation `s1 ++ s_pivot ++ s2` is a
  permutation of the input `[3; 1; 2]`
- **Length preservation:** `|s1| + 1 + |s2| == 3`

## Key Lemma

### `partition_permutation_valid`

Proves that given the postcondition constraints (bounds, strict ordering,
permutation), the total length `|s1| + 1 + |s2| == 3` is preserved. This
follows directly from `SP.perm_len`.

## Spec Precision Result

**The partition postcondition is intentionally relational.**

The `Impl.fsti` postcondition does not prescribe which element becomes the
pivot. The Lomuto implementation always uses the last element (pivot = `a[hi-1]`
= 2 for input `[3; 1; 2]`), but this choice is NOT exposed in the spec.

This means the postcondition admits three possible partitions for `[3; 1; 2]`:

| Pivot | p | s1 | s_pivot | s2 | Valid? |
|-------|---|-----|---------|------|--------|
| 1 | 0 | `[]` | `[1]` | `[3;2]` or `[2;3]` | ✅ |
| 2 | 1 | `[1]` | `[2]` | `[3]` | ✅ |
| 3 | 2 | `[1;2]` or `[2;1]` | `[3]` | `[]` | ✅ |

The actual Lomuto partition produces `p=1, pivot=2, s1=[1], s2=[3]`, but
the spec is agnostic to pivot strategy. **This is by design** — the `Impl.fsti`
should be usable with any partition strategy (Lomuto, Hoare, randomized).

### Consequence for Callers

The partition spec is precise enough for its intended use in quicksort:
- All left elements are ≤ pivot, all right elements are > pivot
- The split preserves the multiset
- Complexity is exactly `n - 1` comparisons

This is exactly what `quicksort_bounded` needs to recurse correctly. The
relational nature does NOT weaken the quicksort postcondition, which only
guarantees `sorted s /\ permutation s0 s` — a fully precise result.

## Verification

- **Z3 options:** `--z3rlimit 400 --fuel 8 --ifuel 4`
- **Admits:** 0
- **Assumes:** 0
- **Spec issues found:** None (relational postcondition is intentional)
