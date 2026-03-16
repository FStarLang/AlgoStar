# Chapter 06: Heapsort — Rubric Compliance

**Date:** 2025-07-17
**Last Updated:** 2026-03-04

---

## Current File Inventory

| File | Lines | Description |
|------|-------|-------------|
| `CLRS.Ch06.Heap.Spec.fst` | ~65 | Pure F★ specification: heap index functions, max-heap predicates, sorted/permutation predicates, swap_seq. |
| `CLRS.Ch06.Heap.Lemmas.fsti` | ~155 | Interface file with signatures for all correctness lemmas. |
| `CLRS.Ch06.Heap.Lemmas.fst` | ~380 | Correctness lemmas: index properties, heap predicate maintenance, swap lemmas, sift-down, extract-max, permutation-preserves-sorted. |
| `CLRS.Ch06.Heap.Impl.fsti` | ~105 | Public Pulse interface for max_heapify, build_max_heap, heapsort. |
| `CLRS.Ch06.Heap.Impl.fst` | ~290 | Pulse implementations of MAX-HEAPIFY, BUILD-MAX-HEAP, HEAPSORT with full correctness proofs (sorted + permutation). Ghost-tick instrumentation for max_heapify cost tracking. |
| `CLRS.Ch06.Heap.Complexity.fsti` | ~85 | Interface for complexity definitions and theorems (log2_floor, build_heap_ops, heapsort_ops, etc.). |
| `CLRS.Ch06.Heap.Complexity.fst` | 468 | Pure F★ complexity analysis: O(n) BUILD-MAX-HEAP (Theorem 6.3), O(n lg n) HEAPSORT (§6.4), heapsort-beats-quadratic for n ≥ 11. |
| `CLRS.Ch06.Heap.CostBound.fsti` | ~35 | Interface for max_heapify_bound definitions and monotonicity/recursion lemmas. |
| `CLRS.Ch06.Heap.CostBound.fst` | ~75 | Helper module connecting max_heapify's ghost-tick cost to the Complexity module. |

---

## Algorithms Covered (CLRS References)

| Algorithm | CLRS Section | Status |
|-----------|-------------|--------|
| PARENT / LEFT / RIGHT | §6.1 | ✅ `parent_idx`, `left_idx`, `right_idx` (0-based adaptation) |
| Max-heap property | §6.1, Definition | ✅ `heap_down_at`, `is_max_heap`, `almost_heaps_from`, `heaps_from` |
| MAX-HEAPIFY | §6.2 | ✅ `max_heapify` (recursive Pulse fn with ghost-tick cost bound) |
| BUILD-MAX-HEAP | §6.3 | ✅ `build_max_heap` (standalone Pulse fn) |
| HEAPSORT | §6.4 | ✅ `heapsort` (two-phase: build + extract-max loop) |
| Theorem 6.3 (BUILD-MAX-HEAP is O(n)) | §6.3 | ✅ `build_heap_ops_linear`: `build_heap_ops(n) ≤ 4n` |
| Theorem 6.4 (HEAPSORT is O(n lg n)) | §6.4 | ✅ `heapsort_ops_simplified`: `heapsort_ops(n) ≤ 6n(1 + ⌊log₂ n⌋)` |
| HEAP-INCREASE-KEY | §6.5 | ❌ Not implemented |
| HEAP-MAXIMUM | §6.5 | ❌ Not implemented |
| HEAP-EXTRACT-MAX | §6.5 | ❌ Not implemented (extract-max loop exists but not as standalone priority-queue op) |
| MAX-HEAP-INSERT | §6.5 | ❌ Not implemented |

---

## Rubric Compliance Matrix

The canonical rubric (RUBRIC.md) requires the following file structure per algorithm:

| Rubric Artifact | MAX-HEAPIFY | BUILD-MAX-HEAP | HEAPSORT |
|----------------|:-----------:|:--------------:|:--------:|
| **ChXX.AlgoName.Spec.fst** — Pure specification | ✅ `Heap.Spec.fst` | ✅ `Heap.Spec.fst` | ✅ `Heap.Spec.fst` |
| **ChXX.AlgoName.Lemmas.fst** — Correctness lemmas | ✅ `Heap.Lemmas.fst` | ✅ `Heap.Lemmas.fst` | ✅ `Heap.Lemmas.fst` |
| **ChXX.AlgoName.Lemmas.fsti** — Lemma interface | ✅ `Heap.Lemmas.fsti` | ✅ `Heap.Lemmas.fsti` | ✅ `Heap.Lemmas.fsti` |
| **ChXX.AlgoName.Complexity.fst** — Complexity proofs | ✅ `Heap.Complexity.fst` + `Heap.CostBound.fst` | ✅ `Heap.Complexity.fst` | ✅ `Heap.Complexity.fst` |
| **ChXX.AlgoName.Complexity.fsti** — Complexity interface | ✅ `Heap.Complexity.fsti` + `Heap.CostBound.fsti` | ✅ `Heap.Complexity.fsti` | ✅ `Heap.Complexity.fsti` |
| **ChXX.AlgoName.Impl.fst** — Pulse implementation | ✅ `Heap.Impl.fst` | ✅ `Heap.Impl.fst` | ✅ `Heap.Impl.fst` |
| **ChXX.AlgoName.Impl.fsti** — Impl interface | ✅ `Heap.Impl.fsti` | ✅ `Heap.Impl.fsti` | ✅ `Heap.Impl.fsti` |

### Legend

- ✅ Fully compliant — exists as a separate file matching the rubric convention
- 🔶 Partially compliant — the content exists but is co-located in a monolithic file rather than split per the rubric
- ❌ Missing — artifact does not exist

---

## Detailed Action Items

### \[SPLIT\] — Extract spec, lemmas, and impl into rubric-compliant files ✅ DONE

The monolithic `CLRS.Ch06.Heap.fst` has been split into rubric-compliant modules:

- **S1. ✅ Created `CLRS.Ch06.Heap.Spec.fst`** — Pure specification module with heap index functions, predicates, sorted/permutation, swap_seq.
- **S2. ✅ Created `CLRS.Ch06.Heap.Lemmas.fst`** — All correctness lemmas extracted and verified.
- **S3. ✅ Created `CLRS.Ch06.Heap.Impl.fst`** — Pulse implementations (max_heapify, build_max_heap, heapsort).

### \[ADD\_INTERFACE\] — Create .fsti files ✅ DONE

- **I1. ✅ Created `CLRS.Ch06.Heap.Lemmas.fsti`** — Exports all key lemma signatures.
- **I2. ✅ Created `CLRS.Ch06.Heap.Complexity.fsti`** — Exports complexity definitions and theorem signatures.
- **I3. ✅ Created `CLRS.Ch06.Heap.Impl.fsti`** — Exports Pulse function signatures for max_heapify, build_max_heap, heapsort.
- **I4. ✅ Created `CLRS.Ch06.Heap.CostBound.fsti`** — Exports max_heapify_bound definitions and lemma signatures.

### \[RENAME\] — Naming improvements

| # | Current Name | Proposed Name | File | Line | Rationale |
|---|-------------|---------------|------|------|-----------|
| R1 | `bad` param in `bad_is_child_of_parent` | `child` | `Heap.Lemmas.fst` | — | "bad" is informal; `child` is descriptive |

### \[CREATE\] — New files / functionality

| # | Target | Description | Priority |
|---|--------|-------------|----------|
| C1 | `CLRS.Ch06.PriorityQueue.Spec.fst` | CLRS §6.5 priority-queue operations: HEAP-MAXIMUM, HEAP-EXTRACT-MAX, HEAP-INCREASE-KEY, MAX-HEAP-INSERT — pure specifications | Low |
| C2 | `CLRS.Ch06.PriorityQueue.Impl.fst` | Pulse implementations of §6.5 operations, reusing `max_heapify` and `build_max_heap` | Low |

### \[ADD\_INTERFACE\] — Additional interface needs (from CostBound) ✅ DONE

| # | Target | Description |
|---|--------|-------------|
| I4 | ✅ `CLRS.Ch06.Heap.CostBound.fsti` | Exports `max_heapify_bound`, `max_heapify_bound_left`, `max_heapify_bound_right`, `max_heapify_bound_root`, `max_heapify_bound_monotone` |

---

## Quality Checks

### Admits / Assumes

| Check | Status |
|-------|--------|
| Zero `admit()` calls across all 9 files | ✅ Verified |
| Zero `assume` calls across all 9 files | ✅ Verified |
| No `sorry`, `Pervasives.undefined`, or other proof holes | ✅ Verified |

### Z3 Resource Limits

| File | Max z3rlimit | Locations | Assessment |
|------|-------------|-----------|------------|
| `Heap.Impl.fst` | 80 | `heapsort` | Elevated — optimization target |
| `Heap.Impl.fst` | 50 | `build_max_heap` | Moderate — acceptable |
| `Heap.Impl.fst` | 40 | `max_heapify` | Moderate — acceptable |
| `Heap.Lemmas.fst` | 200 | `perm_prefix_bounded_aux`, `perm_prefix_bounded_aux_upto` | High — optimization target |
| `Heap.Lemmas.fst` | 80 | `perm_preserves_sorted_suffix`, `perm_preserves_sorted_suffix_upto` | Moderate — acceptable |
| `Heap.Complexity.fst` | 300 | `build_heap_ops_le_root_bound_small` (fuel 20) | High — for small-n normalization |
| `Heap.Complexity.fst` | 40 | `scaled_floor_sum_bound` region | Moderate — acceptable |
| `Heap.CostBound.fst` | 20 | `max_heapify_bound_right` | Low — good |

No `z3seed`, `retry`, or `quake` options — no signs of proof fragility.

### Fuel / iFuel

| Location | fuel/ifuel | Notes |
|----------|-----------|-------|
| Most lemmas in `Heap.Lemmas.fst` | 1/1 | Tightly controlled ✅ |
| `perm_prefix_bounded_aux` | 2/2 | Necessary for count/index reasoning across modules |
| `Heap.Complexity.fst` | default | Relies on default fuel; acceptable for pure math |

### Ghost-Tick Instrumentation

| Algorithm | Ghost ticks? | Cost bound proven? |
|-----------|:------------:|:------------------:|
| `max_heapify` (in `Heap.Impl.fst`) | ✅ `tick2 ctr` per recursive call | ✅ `cf - c0 <= max_heapify_bound(heap_size, idx)` |
| `build_max_heap` (in `Heap.Impl.fst`) | 🔶 Allocates `ctr` and passes to `max_heapify`, but does not assert aggregate bound | ❌ No aggregate `build_heap_ops` bound in Pulse |
| `heapsort` (in `Heap.Impl.fst`) | 🔶 Allocates `ctr_extract` for extract phase, but does not assert aggregate bound | ❌ No aggregate `heapsort_ops` bound in Pulse |

The Complexity module proves bounds in isolation (pure math). `max_heapify` connects its ghost counter to `max_heapify_bound`. However, `build_max_heap` and `heapsort` do **not** aggregate these per-call bounds into the O(n) / O(n lg n) totals in their postconditions.

### CLRS Fidelity

| Aspect | Rating | Notes |
|--------|--------|-------|
| Index convention (0-based vs 1-based) | ✅ Correct | Standard 0-based translation |
| MAX-HEAPIFY logic | ✅ Faithful | Recursive sift-down, finds largest among {i, left, right} |
| BUILD-MAX-HEAP | ✅ Faithful | Bottom-up loop from ⌊n/2⌋ downto 1; now standalone fn |
| HEAPSORT two-phase structure | ✅ Faithful | Build-heap then extract-max loop |
| Loop invariants | ✅ Match CLRS | Build-heap: §6.3 invariant; extract-max: Exercise 6.4-2 invariant |
| §6.5 priority queue | ❌ Missing | HEAP-MAXIMUM, EXTRACT-MAX, INCREASE-KEY, INSERT not implemented |

### Specification Strength

| Function | Postcondition | Rating |
|----------|--------------|--------|
| `max_heapify` | `heaps_from s' heap_size start`, `permutation s s'`, elements outside heap unchanged, length preserved, `cf - c0 <= max_heapify_bound(...)` | **Strong** |
| `build_max_heap` | `is_max_heap s n`, `permutation s0 s`, length preserved | **Strong** |
| `heapsort` | `sorted_upto s (SZ.v n)`, `permutation s0 s`, elements beyond `n` preserved | **Strong** |

### Documentation

| Check | Status | Notes |
|-------|--------|-------|
| Module-level header comment | ✅ | All modules have descriptive headers |
| CLRS section references | ✅ | §6.1–6.4, Theorem 6.3, Exercise 6.4-2 cited |
| `start` ghost parameter documented | ✅ | Comment in `Heap.Impl.fst` |
| `SZ.fits` precondition documented | ✅ | Comment in `Heap.Impl.fst` |
| Ghost-tick `ctr` parameter documented | ✅ | Comment in `Heap.Impl.fst` |
| Inline proof sketches | ✅ | Key proofs have detailed comments |

### Summary

| Dimension | Rating | Notes |
|-----------|--------|-------|
| CLRS Fidelity | ⭐⭐⭐⭐⭐ | All §6.1–6.4 algorithms faithfully implemented |
| Specification Strength | ⭐⭐⭐⭐⭐ | sorted + permutation + heap-property + cost bound |
| Complexity Results | ⭐⭐⭐⭐ | Complete pure-math bounds; max_heapify has ghost ticks; build/heapsort aggregation gap |
| Rubric File Structure | ⭐⭐⭐⭐⭐ | Fully split into Spec/Lemmas/Impl with .fsti interfaces |
| Code Quality | ⭐⭐⭐⭐ | Well-organized with section headers; zero dead code |
| Proof Quality | ⭐⭐⭐⭐⭐ | Zero admits, moderate z3rlimits, no flaky proofs |
| Documentation | ⭐⭐⭐⭐½ | Thorough headers and inline comments; all key design decisions documented |

### Priority Summary

| Priority | Action Items |
|----------|-------------|
| **High** | ✅ S1–S3: Split `Heap.fst` into Spec/Lemmas/Impl per rubric |
| **High** | ✅ I1–I4: Create `.fsti` interface files |
| **Medium** | Aggregate ghost-tick bounds in `build_max_heap` and `heapsort` postconditions |
| **Low** | R1: Rename `bad` → `child` in `bad_is_child_of_parent` |
| **Low** | C1–C2: Implement §6.5 priority-queue operations |
