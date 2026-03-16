# Chapter 02: Getting Started — Rubric Compliance

**Date:** 2026-03-16 (updated from 2025-07-17)
**Source files:** `ch02-getting-started/`
**Rubric:** `audit/RUBRIC.md` (canonical naming: `CLRS.ChXX.AlgoName.{Spec,Lemmas,Complexity,Impl}.{fst,fsti}`)

---

## Current File Inventory

| File | Role | Rubric Category | Pulse/F\* | Status |
|------|------|-----------------|-----------|--------|
| `CLRS.Ch02.InsertionSort.Spec.fst` | Pure spec: `complexity_bounded` | Spec ✅ | Pure F\* | ✅ |
| `CLRS.Ch02.InsertionSort.Lemmas.fsti` | Lemma signatures | Lemmas ✅ | Pure F\* | ✅ |
| `CLRS.Ch02.InsertionSort.Lemmas.fst` | Lemma proofs | Lemmas ✅ | Pure F\* | ✅ |
| `CLRS.Ch02.InsertionSort.Impl.fsti` | Public interface for `insertion_sort` | Impl ✅ | Pulse | ✅ |
| `CLRS.Ch02.InsertionSort.Impl.fst` | Pulse implementation | Impl ✅ | Pulse | ✅ |
| `CLRS.Ch02.MergeSort.Spec.fst` | Pure spec: `seq_merge`, `all_ge`, `ms_cost`, complexity predicates | Spec ✅ | Pure F\* | ✅ |
| `CLRS.Ch02.MergeSort.Lemmas.fsti` | Lemma signatures | Lemmas ✅ | Pure F\* | ✅ |
| `CLRS.Ch02.MergeSort.Lemmas.fst` | Lemma proofs | Lemmas ✅ | Pure F\* | ✅ |
| `CLRS.Ch02.MergeSort.Complexity.fsti` | Complexity interface | Complexity ✅ | Pure F\* | ✅ |
| `CLRS.Ch02.MergeSort.Complexity.fst` | O(n log n) bound proof | Complexity ✅ | Pure F\* | ✅ |
| `CLRS.Ch02.MergeSort.Impl.fsti` | Public interface for `merge` and `merge_sort` | Impl ✅ | Pulse | ✅ |
| `CLRS.Ch02.MergeSort.Impl.fst` | Pulse implementation | Impl ✅ | Pulse | ✅ |

---

## Algorithms Covered

| # | Algorithm | CLRS Section | CLRS Name | Module |
|---|-----------|-------------|-----------|--------|
| 1 | Insertion Sort | §2.1, p. 18 | INSERTION-SORT | `CLRS.Ch02.InsertionSort` |
| 2 | Merge | §2.3.1, p. 31 | MERGE | `CLRS.Ch02.MergeSort` (fn `merge`) |
| 3 | Merge Sort | §2.3.1, p. 34 | MERGE-SORT | `CLRS.Ch02.MergeSort` (fn `merge_sort`, `merge_sort_aux`) |

---

## Rubric Compliance Matrix

### Insertion Sort (`CLRS.Ch02.InsertionSort`)

| Rubric File | Status | Notes |
|-------------|--------|-------|
| `Spec.fst` | ✅ Complete | `complexity_bounded` definition |
| `Lemmas.fst` | ✅ Complete | 3 lemmas: prefix_le_key, combine_sorted_regions, triangle_step |
| `Lemmas.fsti` | ✅ Complete | Signatures for all 3 lemmas |
| `Impl.fst` | ✅ Complete | Pulse `insertion_sort` with correctness + complexity |
| `Impl.fsti` | ✅ Complete | Public interface with full postcondition |

No `Complexity.fst` / `.fsti` — complexity is trivial (single predicate in `Spec.fst` + one arithmetic lemma in `Lemmas.fst`). The shared `CLRS.Common.Complexity` provides the `tick` infrastructure.

### Merge Sort (`CLRS.Ch02.MergeSort`)

| Rubric File | Status | Notes |
|-------------|--------|-------|
| `Spec.fst` | ✅ Complete | `seq_merge`, `all_ge`, `ms_cost`, complexity predicates |
| `Lemmas.fst` | ✅ Complete | 10+ lemmas: merge properties, suffix stepping, cost splitting |
| `Lemmas.fsti` | ✅ Complete | Signatures for all public lemmas |
| `Complexity.fst` | ✅ Complete | Recurrence, O(n log n) bound, monotonicity, split |
| `Complexity.fsti` | ✅ Complete | Public interface for all complexity definitions/lemmas |
| `Impl.fst` | ✅ Complete | Pulse `merge`, `merge_sort_aux`, `merge_sort`, `copy_range` |
| `Impl.fsti` | ✅ Complete | Public interface for `merge` and `merge_sort` |

---

## Quality Checks

### Admits / Assumes Count

| File | `admit` | `assume` | `sorry` |
|------|---------|----------|---------|
| All ch02 files | 0 | 0 | 0 |

### Postcondition Coverage

| Function | Sorted | Permutation | Length | Complexity | Overall |
|----------|--------|-------------|--------|------------|---------|
| `insertion_sort` | ✅ | ✅ | ✅ | ✅ n(n−1)/2 | **Strong** |
| `merge` | ✅ | ✅ | ✅ | ✅ hi−lo | **Strong** |
| `merge_sort` | ✅ | ✅ | ✅ | ✅ ms_cost(n) | **Strong** |

### Profiling (2026-03-16, serial build ~2m07s)

| File | Time | Peak z3rlimit | Peak fuel |
|------|------|---------------|-----------|
| InsertionSort.Spec.fst | ~7s | defaults | defaults |
| InsertionSort.Lemmas.fst | ~7s | defaults | defaults |
| InsertionSort.Impl.fst | **~29s** | 20 | 1 |
| MergeSort.Complexity.fst | ~3s | 20 | 1 |
| MergeSort.Spec.fst | ~3s | defaults | defaults |
| MergeSort.Lemmas.fst | ~18s | 50 | 3 |
| MergeSort.Impl.fst | **~64s** | 40 | 2 |

### Cross-Cutting

- `tick`/`incr_nat` are provided by `CLRS.Common.Complexity.fst` (ghost `GR.ref nat`). No duplication.
- All while loops have explicit `decreases` clauses.

---

## Remaining Improvement Opportunities

1. **Reduce InsertionSort.Impl.fst verification time** (~120s): the inner loop invariant has 10+ conjuncts; splitting into a helper lemma or adding intermediate assertions could help.
2. **Reduce MergeSort.Impl.fst merge z3rlimit** (currently 100): the merge loop with suffix tracking drives SMT cost.
3. **Reduce MergeSort.Lemmas.fst fuel** (`seq_merge_count` uses fuel 3).
4. **Tighten complexity constant**: 4n⌈log₂ n⌉ + 4n → n⌈log₂ n⌉ + n.
5. **Prove best-case complexity** for InsertionSort (Ω(n) on sorted input).
6. **Bound memory usage** for MergeSort merge (O(n) auxiliary space).
