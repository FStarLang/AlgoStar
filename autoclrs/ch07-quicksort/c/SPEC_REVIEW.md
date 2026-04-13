# Ch07 Quicksort C Code — Specification Review

## Overview

This document compares the C code specifications (in `partition.c` and `quicksort.c`)
against the Pulse implementation interfaces (`CLRS.Ch07.Partition.Impl.fsti` and
`CLRS.Ch07.Quicksort.Impl.fsti`). We identify gaps and plan fixes.

The C code uses `Int32.t` and `SizeT.t` while the Pulse specs use `Prims.int` and `nat`.
Bridge lemmas in `CLRS.Ch07.Quicksort.C.BridgeLemmas` handle this representation change.

## Files

| File | Role |
|------|------|
| `partition.c` | Standalone Lomuto partition (no bounds tracking) |
| `quicksort.c` | Partition with bounds + recursive quicksort + top-level wrapper |
| `Partition.fst` | Generated Pulse from `partition.c` |
| `Quicksort.fst` | Generated Pulse from `quicksort.c` |
| `CLRS.Ch07.Quicksort.C.BridgeLemmas.fst/fsti` | Bridge lemmas between c2pulse and Pulse specs |

---

## Partition Spec Comparison

### Impl.fsti (`clrs_partition_wrapper_with_ticks`)

| # | Property | Status in C |
|---|----------|-------------|
| 1 | Pivot index in range: `lo <= p /\ p < hi` | ✅ Both partition.c and quicksort.c |
| 2 | Left ≤ pivot: `between_bounds s1 lb (pivot)` | ✅ quicksort.c (has lb/rb); partial in partition.c (no bounds) |
| 3 | Right > pivot: `strictly_larger_than s2 (pivot)` | ✅ Both files |
| 4 | Pivot bounds: `lb <= pivot <= rb` | ✅ quicksort.c |
| 5 | Bounds preservation: `between_bounds` on all sub-sequences | ✅ quicksort.c |
| 6 | Permutation: `permutation s0 (append s1 (append s_pivot s2))` | ❌ Only no-fabrication (weaker) |
| 7 | Frame preservation | ✅ Both files |
| 8 | Complexity: `complexity_exact_linear` | N/A (removed per instructions) |

### Gap Analysis — Partition

**Gap 6: Permutation vs No-fabrication**

The C code proves no-fabrication:
```
∀k∈[lo,hi). ∃j∈[lo,hi). a[k] == old(a[j])
```
This says every output element existed in the input. Combined with the fact
that partition only performs swaps on a fixed-size range, this implies
permutation. However, no-fabrication alone is strictly weaker than
permutation (it doesn't prevent duplication).

**Plan**: The no-fabrication property (∀k.∃j. a[k]=old(a[j])) and even
a "no-destruction" property (∀j.∃k. old(a[j])=a[k]) are INSUFFICIENT
to prove permutation. Counterexample: s1=[1,1,2], s2=[1,2,2] satisfies
both properties but is not a permutation (the existential witnesses can
reuse indices, proving only range inclusion not multiset equality).

Full permutation requires either:
- Tracking a ghost bijection from output to input positions, or
- Maintaining a count-based multiset invariant, or
- Tracking permutation of the ghost sequence through each swap

None of these are naturally expressible in c2pulse annotations without
ghost state support. A "no-destruction" invariant (reverse direction:
∀j.∃k. old(a[j])=a[k]) was attempted but causes Z3 timeouts — the
additional quantifier alternation makes the swap body proof too expensive.

Note: no-fabrication + no-destruction would still not suffice for
permutation (counterexample: s1=[1,1,2], s2=[1,2,2] satisfies both
but is not a permutation — the existential witnesses can reuse indices).

The full permutation proof remains in the Pulse implementation
(`CLRS.Ch07.Quicksort.Impl.fst`), which uses ghost sequences and
`pts_to_range` ownership splitting.

---

## Quicksort Spec Comparison

### Impl.fsti (`quicksort`)

| # | Property | Status in C |
|---|----------|-------------|
| 1 | Sorted output: `sorted s` | ✅ Adjacent-pair sorted (bridge lemma converts) |
| 2 | Permutation: `permutation s0 s` | ❌ Missing entirely |

### Impl.fsti (`quicksort_bounded`)

| # | Property | Status in C (`quicksort_rec`) |
|---|----------|-------------------------------|
| 1 | Sorted output: `sorted s` | ✅ Adjacent-pair sorted |
| 2 | Permutation: `permutation s0 s` | ❌ Missing |
| 3 | Bounds preservation: `between_bounds s lb rb` | ✅ Present |
| 4 | Frame preservation | ✅ Present |

### Gap Analysis — Quicksort

**Gap 2: Permutation**

The fundamental challenge is compositional. `quicksort_rec` calls `partition`
then two recursive calls. After `partition`, we have no-fabrication facts
about the post-partition state. After `sort_left` modifies positions `[lo,p)`,
the partition's no-fabrication facts (which reference `array_read` in the
post-partition state) are no longer available — the array state has changed.

In the Pulse implementation, this is handled by splitting ownership via
`pts_to_range`, so each sub-range is independently tracked. The c2pulse
model uses a monolithic array, making compositional reasoning harder.

**Options considered**:

1. **Add no-fabrication + no-destruction to quicksort_rec**: Requires chaining
   existentials across intermediate states. Not feasible without ghost state
   to capture intermediate array snapshots.

2. **Use `_include_pulse` for ghost permutation tracking**: Define a ghost
   sequence capturing the initial array state and maintain
   `permutation(ghost_initial, current)` as an invariant. This is theoretically
   possible but requires c2pulse features (ghost references, existential
   binding in invariants) that may not be available.

3. **Accept the gap**: Document that the C code proves sorted + bounds + frame
   but not permutation. The full permutation proof remains in the Pulse
   implementation. The C code's no-fabrication for partition provides a
   weaker guarantee.

**Decision**: The C code proves all properties EXCEPT permutation.
Permutation requires ghost state (ghost sequences or ghost bijections)
that c2pulse does not natively support. Adding a no-destruction invariant
was attempted but causes Z3 timeouts. The full permutation proof
remains in the Pulse implementation.

---

## Checklist

- [x] No `_include_pulse` with computationally relevant code
- [x] No complexity-related specifications in C code
- [x] Partition: pivot index in range
- [x] Partition: left ≤ pivot ordering
- [x] Partition: right > pivot ordering (strictly_larger_than)
- [x] Partition: pivot bounds (lb, rb)
- [x] Partition: between_bounds preservation
- [x] Partition: frame preservation
- [x] Partition: no-fabrication
- [ ] Partition: no-destruction — ATTEMPTED, causes Z3 timeouts
- [ ] Partition: full permutation — GAP (requires ghost state; see analysis above)
- [x] Quicksort: sorted output (adjacent-pair, bridged to all-pairs)
- [x] Quicksort: bounds preservation
- [x] Quicksort: frame preservation
- [ ] Quicksort: permutation — GAP (requires ghost state for compositional proof)
- [x] Bridge: adjacent_sorted_implies_sorted
- [x] Bridge: c_bounds_implies_between_bounds
- [x] Bridge: swap_extract_permutation
- [x] Bridge: unchanged_extract_eq
- [x] Bridge: subrange_sorted_implies_sorted

---

## Work Plan

1. ✅ Document spec gaps (this file)
2. ✅ Attempted no-destruction invariant — Z3 timeouts, reverted
3. ✅ Analyzed no-fab + no-destr → permutation: NOT provable (counterexample found)
4. ✅ Verified all code builds correctly
5. Commit
