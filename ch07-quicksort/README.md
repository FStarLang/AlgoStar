# CLRS Chapter 7: Quicksort Implementation in Pulse

This directory contains a verified implementation of the Quicksort algorithm from CLRS (Cormen, Leiserson, Rivest, Stein) in Pulse, the concurrent separation logic DSL embedded in F*.

## Implementation

The implementation in `CLRS.Ch07.Quicksort.fst` provides:

### 1. CLRS Partition Algorithm

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

Implemented as `clrs_partition` with specification that:
- Elements A[lo..p) are ≤ pivot
- A[p] == pivot  
- Elements A[p+1..hi) are > pivot
- Result is a permutation of input

### 2. CLRS Quicksort Algorithm

```
QUICKSORT(A, lo, hi):
  if lo < hi:
    p = PARTITION(A, lo, hi)
    QUICKSORT(A, lo, p)
    QUICKSORT(A, p+1, hi)
```

Implemented as `clrs_quicksort` with specification that:
- Output is sorted
- Output is a permutation of input
- Elements remain within original bounds

### 3. Key Features

- **Functional Correctness**: Full specifications proving:
  - `sorted`: Output sequence is sorted
  - `permutation`: Output is a permutation of input
  - `between_bounds`: Elements stay within min/max bounds

- **Separation Logic**: Uses Pulse's separation logic to track:
  - Array ownership via `pts_to_range`
  - Mutable reference ownership  
  - Ghost state for specifications

- **Verified Properties**:
  - Partition correctness predicate
  - Permutation preservation through swaps
  - Combining sorted sub-arrays

## Structure

The implementation follows the pattern from `/home/nswamy/workspace/pulse/share/pulse/examples/Quicksort.Base.fst` but adapted for the CLRS partition scheme:

1. **Core Definitions** (lines 1-170):
   - Sequence predicates: `sorted`, `between_bounds`, `larger_than`, `smaller_than`
   - Permutation reasoning with SMT patterns
   - Array access helpers using `pts_to_range`

2. **Swap Operation** (lines 200-220):
   - Swaps two array elements
   - Proves result is a permutation

3. **CLRS Partition** (lines 225-290):
   - Implements CLRS partition with loop invariant
   - Proves partition predicate
   - Uses `live` for reference ownership

4. **Partition Wrapper** (lines 295-365):
   - Splits ownership for recursive calls
   - Provides separate ownership of left, pivot, and right regions
   - Transfers bound properties to sub-regions

5. **Quicksort** (lines 448-480):
   - Recursive implementation
   - Ghost proof function to combine sorted regions
   - Handles base case (lo >= hi)

## Building

```bash
cd /home/nswamy/workspace/clrs/ch07-quicksort
make
```

The Makefile uses the Pulse build system via:
```makefile
PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk
```

## Status

✅ **CLRS partition algorithm** - Fully implemented and verified
✅ **CLRS quicksort algorithm** - Fully implemented and verified  
✅ **Partition correctness** - Elements ≤ pivot on left, > pivot on right
✅ **Sorted output** - Proven sorted via `sorted` predicate
✅ **Permutation preservation** - Proven via `permutation` predicate
✅ **Builds successfully** - All code typechecks with F* and Pulse

⚠️ One `admit()` in optional `quicksort` wrapper (conversion between `pts_to` and `pts_to_range`)

The core algorithms `clrs_partition` and `clrs_quicksort` are **fully verified** without admits.

## Key Differences from Pulse Quicksort.Base

1. **Partition scheme**: CLRS uses last element as pivot with single-pass partition, vs three-way partition in Base
2. **Return type**: CLRS returns single pivot index, vs (left, right, pivot_value) triple
3. **Predicate**: Simplified `clrs_partition_pred` for two-region partition

## Verification

All proofs are mechanically checked by F* and Pulse except for the top-level API wrapper which has one `admit()` for the pts_to conversion (not essential for the core algorithms).

The implementation demonstrates:
- Stateful programming in Pulse
- Separation logic specifications
- Loop invariants with existential quantification  
- Permission tracking through mutable references
- Ghost state for functional specifications
- Permutation reasoning
