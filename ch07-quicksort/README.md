# CLRS Chapter 7: Quicksort Implementation in Pulse

This directory contains a verified implementation of the Quicksort algorithm from CLRS (Cormen, Leiserson, Rivest, Stein) in Pulse, the concurrent separation logic DSL embedded in F*.

## File Structure

The implementation follows the canonical rubric structure:

### Partition (`CLRS.Ch07.Partition.*`)

| File | Role |
|------|------|
| `CLRS.Ch07.Partition.Spec.fst` | Pure predicates: `clrs_partition_pred`, `between_bounds`, `complexity_exact_linear` |
| `CLRS.Ch07.Partition.Lemmas.fsti` | Interface for partition lemmas |
| `CLRS.Ch07.Partition.Lemmas.fst` | Proofs: `permutation_swap`, `transfer_larger_slice`, `transfer_smaller_slice` |
| `CLRS.Ch07.Partition.Complexity.fsti` | Interface for partition complexity |
| `CLRS.Ch07.Partition.Complexity.fst` | Partition performs exactly n−1 comparisons |
| `CLRS.Ch07.Partition.Impl.fsti` | Interface: `clrs_partition_wrapper_with_ticks` |
| `CLRS.Ch07.Partition.Impl.fst` | Pulse impl: `tick`, `swap`, `clrs_partition_with_ticks`, wrapper |

### Quicksort (`CLRS.Ch07.Quicksort.*`)

| File | Role |
|------|------|
| `CLRS.Ch07.Quicksort.Spec.fst` | Pure specs: `seq_min`/`seq_max`, `complexity_bounded_quadratic`, `pure_pre/post_quicksort` |
| `CLRS.Ch07.Quicksort.Lemmas.fsti` | Interface for quicksort lemmas |
| `CLRS.Ch07.Quicksort.Lemmas.fst` | Proofs: `lemma_sorted_append`, `append_permutations_3`, `lemma_quicksort_complexity_bound` |
| `CLRS.Ch07.Quicksort.Complexity.fsti` | Interface for complexity analysis |
| `CLRS.Ch07.Quicksort.Complexity.fst` | Worst-case recurrence T(n) = n(n−1)/2, convexity, monotonicity |
| `CLRS.Ch07.Quicksort.Impl.fsti` | Public API: `quicksort`, `quicksort_with_complexity`, `quicksort_bounded` |
| `CLRS.Ch07.Quicksort.Impl.fst` | Pulse impl: recursive quicksort with ghost proof function |

## Implementation

### CLRS Partition Algorithm (§7.1)

```
PARTITION(A, lo, hi):
  pivot = A[hi-1]
  i = lo - 1
  for j = lo to hi-2:
    if A[j] <= pivot:
      i = i + 1
      swap A[i] and A[j]
  swap A[i+1] and A[hi-1]
  return i + 1
```

Implemented as `clrs_partition_with_ticks` with specification that:
- Elements A[lo..p) are ≤ pivot
- A[p] == pivot
- Elements A[p+1..hi) are > pivot
- Result is a permutation of input
- Exactly hi−lo−1 comparisons (ghost tick counted)

### CLRS Quicksort Algorithm (§7.1)

```
QUICKSORT(A, lo, hi):
  if lo < hi:
    p = PARTITION(A, lo, hi)
    QUICKSORT(A, lo, p)
    QUICKSORT(A, p+1, hi)
```

Implemented as `clrs_quicksort_with_ticks` with specification that:
- Output is sorted
- Output is a permutation of input
- Elements remain within original bounds
- Worst-case O(n²) complexity: ≤ n(n−1)/2 comparisons

## Building

```bash
cd ch07-quicksort
make
```

## Verification

All proofs are mechanically checked by F* and Pulse. **NO admits. NO assumes.**

All 15 source files verify at default rlimits with zero retries.
