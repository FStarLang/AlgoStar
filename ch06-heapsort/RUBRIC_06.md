# Chapter 06: Heapsort — Rubric Compliance

**Date:** 2025-07-17

---

## Current File Inventory

| File | Lines | Description |
|------|-------|-------------|
| `CLRS.Ch06.Heap.fst` | 780 | Pulse implementation of MAX-HEAPIFY, BUILD-MAX-HEAP, HEAPSORT with full correctness proofs (sorted + permutation). Includes ghost-tick instrumentation for max_heapify cost tracking. |
| `CLRS.Ch06.Heap.Complexity.fst` | 468 | Pure F★ complexity analysis: O(n) BUILD-MAX-HEAP (Theorem 6.3), O(n lg n) HEAPSORT (§6.4), heapsort-beats-quadratic for n ≥ 11. |
| `CLRS.Ch06.Heap.CostBound.fst` | 83 | Helper module connecting max_heapify's ghost-tick cost to the Complexity module. Defines `max_heapify_bound` and monotonicity/recursion lemmas. |

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
| **ChXX.AlgoName.Spec.fst** — Pure specification | 🔶 Inlined in `Heap.fst` (lines 86–103: `heap_down_at`, `is_max_heap`, etc.) | 🔶 Inlined in `Heap.fst` (same predicates) | 🔶 Inlined in `Heap.fst` (lines 121–133: `sorted`, `permutation`) |
| **ChXX.AlgoName.Lemmas.fst** — Correctness lemmas | 🔶 Inlined in `Heap.fst` (lines 107–340: sift-down lemmas, swap lemmas) | 🔶 Inlined in `Heap.fst` (line 484: `heaps_from_zero`) | 🔶 Inlined in `Heap.fst` (lines 554–683: `root_ge_element`, `extract_almost_heaps`, etc.) |
| **ChXX.AlgoName.Lemmas.fsti** — Lemma interface | ❌ Missing | ❌ Missing | ❌ Missing |
| **ChXX.AlgoName.Complexity.fst** — Complexity proofs | ✅ `Heap.Complexity.fst` + `Heap.CostBound.fst` | ✅ `Heap.Complexity.fst` (`build_heap_ops_linear`) | ✅ `Heap.Complexity.fst` (`heapsort_ops_simplified`, etc.) |
| **ChXX.AlgoName.Complexity.fsti** — Complexity interface | ❌ Missing | ❌ Missing | ❌ Missing |
| **ChXX.AlgoName.Impl.fst** — Pulse implementation | 🔶 In `Heap.fst` (lines 362–475: `max_heapify`) | 🔶 In `Heap.fst` (lines 490–546: `build_max_heap`) | 🔶 In `Heap.fst` (lines 695–779: `heapsort`) |
| **ChXX.AlgoName.Impl.fsti** — Impl interface | ❌ Missing | ❌ Missing | ❌ Missing |

### Legend

- ✅ Fully compliant — exists as a separate file matching the rubric convention
- 🔶 Partially compliant — the content exists but is co-located in a monolithic file rather than split per the rubric
- ❌ Missing — artifact does not exist

---

## Detailed Action Items

### \[SPLIT\] — Extract spec, lemmas, and impl into rubric-compliant files

Currently all spec definitions, lemmas, and Pulse implementations live in the single `CLRS.Ch06.Heap.fst` (780 lines). The rubric requires separate files per concern.

**S1. Create `CLRS.Ch06.Heap.Spec.fst`** — Pure specification module
- Move `parent_idx`, `left_idx`, `right_idx` (lines 61–63)
- Move `heap_down_at`, `is_max_heap`, `almost_heaps_from`, `heaps_from` (lines 86–103)
- Move `sorted`, `suffix_sorted`, `prefix_le_suffix` (lines 121–130)
- Move `permutation` and its opaque wrapper (lines 132–133)
- Move `swap_seq` and its properties (lines 160–187)

**S2. Create `CLRS.Ch06.Heap.Lemmas.fst`** — Correctness lemmas
- Move `heaps_from_to_almost`, `almost_to_full` (lines 107–117)
- Move `permutation_same_length`, `permutation_refl`, `compose_permutations` (lines 135–156)
- Move `swap_preserves_heap_down_other`, `swap_heap_down_at_parent`, `swap_heap_down_at_grandparent` (lines 193–276)
- Move `sift_down_swap_lemma_from`, `grandparent_after_swap_from` (lines 280–340)
- Move `root_ge_element`, `extract_almost_heaps`, `extract_extends_sorted` (lines 554–604)
- Move `perm_preserves_sorted_suffix`, `slice_suffix_eq`, `index_mem_intro` (lines 609–683)
- Move `parent_idx_lt`, `bad_is_child_of_parent`, `left_idx_inj`, `right_idx_inj`, `left_neq_right`, `left_idx_parent`, `right_idx_parent` (lines 66–79)

**S3. Create `CLRS.Ch06.Heap.Impl.fst`** — Pulse implementations only
- Keep `max_heapify` (lines 362–475), `build_max_heap` (lines 490–546), `heapsort` (lines 695–779)
- Keep ghost-tick helpers `incr_nat`, `tick`, `tick2` (lines 39–56)
- Import from Spec and Lemmas modules

### \[ADD\_INTERFACE\] — Create .fsti files

**I1. Create `CLRS.Ch06.Heap.Lemmas.fsti`**
- Export signatures for key lemmas:
  - `val sift_down_swap_lemma_from`: the main sift-down correctness lemma
  - `val root_ge_element`: root-is-max lemma
  - `val extract_almost_heaps`: extract step preserves almost-heap
  - `val extract_extends_sorted`: extract step extends sorted suffix
  - `val perm_preserves_sorted_suffix`: permutation preserves sorted suffix
  - `val swap_is_permutation`: swap produces a permutation
  - `val grandparent_after_swap_from`: grandparent bounds after swap

**I2. Create `CLRS.Ch06.Heap.Complexity.fsti`**
- Export signatures for:
  - `val build_heap_ops_linear`: BUILD-MAX-HEAP O(n) bound
  - `val heapsort_ops_simplified`: HEAPSORT O(n lg n) bound
  - `val heapsort_practical_bound`: tighter 2n·log₂n + 4n bound
  - `val heapsort_asymptotic`: 3n·log₂n bound for n ≥ 16
  - `val heapsort_better_than_quadratic`: beats O(n²) for n ≥ 11
  - Expose type definitions: `log2_floor`, `build_heap_ops`, `heapsort_ops`, `extract_max_ops`, `nodes_at_height`

**I3. Create `CLRS.Ch06.Heap.Impl.fsti`**
- Export signatures for:
  - `val max_heapify`: with full pre/postcondition (lines 362–395)
  - `val build_max_heap`: with pre/postcondition (lines 490–511)
  - `val heapsort`: with pre/postcondition (lines 695–714)

### \[RENAME\] — Naming improvements

| # | Current Name | Proposed Name | File | Line | Rationale |
|---|-------------|---------------|------|------|-----------|
| R1 | `bad` param in `bad_is_child_of_parent` | `child` | `Heap.fst` | 68 | "bad" is informal; `child` is descriptive |
| R2 | `CLRS.Ch06.Heap.fst` (module name) | `CLRS.Ch06.Heap.Impl.fst` | — | — | Rubric: impl code goes in `.Impl.fst` |

### \[CREATE\] — New files / functionality

| # | Target | Description | Priority |
|---|--------|-------------|----------|
| C1 | `CLRS.Ch06.PriorityQueue.Spec.fst` | CLRS §6.5 priority-queue operations: HEAP-MAXIMUM, HEAP-EXTRACT-MAX, HEAP-INCREASE-KEY, MAX-HEAP-INSERT — pure specifications | Low |
| C2 | `CLRS.Ch06.PriorityQueue.Impl.fst` | Pulse implementations of §6.5 operations, reusing `max_heapify` and `build_max_heap` | Low |

### \[ADD\_INTERFACE\] — Additional interface needs (from CostBound)

| # | Target | Description |
|---|--------|-------------|
| I4 | `CLRS.Ch06.Heap.CostBound.fsti` | Export `max_heapify_bound`, `max_heapify_bound_left`, `max_heapify_bound_right`, `max_heapify_bound_root`, `max_heapify_bound_monotone` |

---

## Quality Checks

### Admits / Assumes

| Check | Status |
|-------|--------|
| Zero `admit()` calls across all 3 files | ✅ Verified |
| Zero `assume` calls across all 3 files | ✅ Verified |
| No `sorry`, `Pervasives.undefined`, or other proof holes | ✅ Verified |

### Z3 Resource Limits

| File | Max z3rlimit | Locations | Assessment |
|------|-------------|-----------|------------|
| `Heap.fst` | 50 | `perm_preserves_sorted_suffix` (line 628), `heapsort` (line 693), `build_max_heap` (line 488) | Moderate — acceptable |
| `Heap.fst` | 40 | `max_heapify` (line 360) | Moderate — acceptable |
| `Heap.Complexity.fst` | 40 | `scaled_floor_sum_bound` region (line 164) | Moderate — acceptable |
| `Heap.CostBound.fst` | 20 | `max_heapify_bound_right` (line 63) | Low — good |

No extreme z3rlimits (all ≤ 50). No `z3seed`, `retry`, or `quake` options — no signs of proof fragility.

### Fuel / iFuel

| Location | fuel/ifuel | Notes |
|----------|-----------|-------|
| Most lemmas in `Heap.fst` | 1/1 | Tightly controlled ✅ |
| `perm_preserves_sorted_suffix` | 2/2 | Necessary for nested counting argument; slightly fragile |
| `Heap.Complexity.fst` | default | Relies on default fuel; acceptable for pure math |

### Ghost-Tick Instrumentation

| Algorithm | Ghost ticks? | Cost bound proven? |
|-----------|:------------:|:------------------:|
| `max_heapify` | ✅ `tick2 ctr` per recursive call | ✅ `cf - c0 <= max_heapify_bound(heap_size, idx)` |
| `build_max_heap` | 🔶 Allocates `ctr` and passes to `max_heapify`, but does not assert aggregate bound | ❌ No aggregate `build_heap_ops` bound in Pulse |
| `heapsort` | 🔶 Allocates `ctr_extract` for extract phase, but does not assert aggregate bound | ❌ No aggregate `heapsort_ops` bound in Pulse |

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
| `heapsort` | `sorted s`, `permutation s0 s`, length preserved | **Strong** |

### Documentation

| Check | Status | Notes |
|-------|--------|-------|
| Module-level header comment | ✅ | `Heap.fst` lines 1–17; `Complexity.fst` lines 1–9; `CostBound.fst` lines 1–5 |
| CLRS section references | ✅ | §6.1–6.4, Theorem 6.3, Exercise 6.4-2 cited |
| `start` ghost parameter documented | ✅ | Comment at lines 342–358 of `Heap.fst` |
| `SZ.fits` precondition documented | ✅ | Comment at lines 354–358 of `Heap.fst` |
| Ghost-tick `ctr` parameter documented | ✅ | Comment at lines 356–358 of `Heap.fst` |
| Inline proof sketches | ✅ | `perm_preserves_sorted_suffix` has detailed sketch |
| Inaccurate PriorityQueue reference | ✅ Fixed | Line 10 no longer references Pulse.Lib.PriorityQueue |

### Summary

| Dimension | Rating | Notes |
|-----------|--------|-------|
| CLRS Fidelity | ⭐⭐⭐⭐⭐ | All §6.1–6.4 algorithms faithfully implemented |
| Specification Strength | ⭐⭐⭐⭐⭐ | sorted + permutation + heap-property + cost bound |
| Complexity Results | ⭐⭐⭐⭐ | Complete pure-math bounds; max_heapify has ghost ticks; build/heapsort aggregation gap |
| Rubric File Structure | ⭐⭐ | All content exists but in monolithic `Heap.fst`; no .fsti files; no Spec/Lemmas/Impl split |
| Code Quality | ⭐⭐⭐⭐ | Well-organized with section headers; zero dead code |
| Proof Quality | ⭐⭐⭐⭐⭐ | Zero admits, moderate z3rlimits, no flaky proofs |
| Documentation | ⭐⭐⭐⭐½ | Thorough headers and inline comments; all key design decisions documented |

### Priority Summary

| Priority | Action Items |
|----------|-------------|
| **High** | S1–S3: Split `Heap.fst` into Spec/Lemmas/Impl per rubric |
| **High** | I1–I4: Create `.fsti` interface files |
| **Medium** | Aggregate ghost-tick bounds in `build_max_heap` and `heapsort` postconditions |
| **Low** | R1: Rename `bad` → `child` in `bad_is_child_of_parent` |
| **Low** | C1–C2: Implement §6.5 priority-queue operations |
