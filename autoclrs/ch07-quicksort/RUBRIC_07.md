# Chapter 07: Quicksort — Rubric Compliance

**Date:** 2025-07-18 (updated 2026-03-04)
**Source files:** 13 files across Partition.* and Quicksort.* modules
**Canonical rubric:** `RUBRIC.md`

---

## Current File Inventory

| File | Role | Notes |
|------|------|-------|
| `CLRS.Ch07.Partition.Lemmas.fsti` | Shared definitions + lemma interface | `nat_smaller`, `seq_swap`, `larger_than`, `smaller_than`, `between_bounds`, `complexity_exact_linear` + lemma sigs |
| `CLRS.Ch07.Partition.Lemmas.fst` | Lemma proofs | `seq_swap_commute`, `permutation_swap`, bounds transfer |
| `CLRS.Ch07.Partition.Complexity.fsti` | Complexity interface | Partition is Θ(n−1) |
| `CLRS.Ch07.Partition.Complexity.fst` | Complexity proof | `partition_comparisons_linear` |
| `CLRS.Ch07.Partition.Impl.fsti` | Impl interface (#lang-pulse) | `clrs_partition_wrapper_with_ticks` |
| `CLRS.Ch07.Partition.Impl.fst` | Pulse implementation | `tick`, `swap`, `clrs_partition_with_ticks`, wrapper, `clrs_partition_pred` |
| `CLRS.Ch07.Quicksort.Lemmas.fsti` | Shared definitions + lemma interface | `seq_min`, `seq_max`, `complexity_bounded_quadratic` + lemma sigs |
| `CLRS.Ch07.Quicksort.Lemmas.fst` | Lemma proofs | `lemma_sorted_append`, `append_permutations_3`, complexity bound |
| `CLRS.Ch07.Quicksort.Complexity.fsti` | Complexity interface | `worst_case_comparisons`, `sum_of_parts_bound`, etc. |
| `CLRS.Ch07.Quicksort.Complexity.fst` | Complexity proofs | Recurrence T(n)=n(n−1)/2, convexity, monotonicity |
| `CLRS.Ch07.Quicksort.Impl.fsti` | Impl interface (#lang-pulse) | `quicksort`, `quicksort_with_complexity`, `quicksort_bounded` |
| `CLRS.Ch07.Quicksort.Impl.fst` | Pulse implementation | `quicksort_proof`, recursive sort, top-level API, `pure_pre/post_quicksort` |
| `README.md` | Documentation | |
| `Makefile` | Build | |

------|------:|------|-------|
| `CLRS.Ch07.Partition.Spec.fst` | 44 | Pure predicates | `clrs_partition_pred`, `between_bounds`, `complexity_exact_linear` |
| `CLRS.Ch07.Partition.Lemmas.fsti` | 39 | Lemma interface | `permutation_swap`, `transfer_larger_slice`, `transfer_smaller_slice` |
| `CLRS.Ch07.Partition.Lemmas.fst` | 57 | Lemma proofs | `seq_swap_commute`, `permutation_swap`, bounds transfer |
| `CLRS.Ch07.Partition.Complexity.fsti` | 14 | Complexity interface | Partition is Θ(n−1) |
| `CLRS.Ch07.Partition.Complexity.fst` | 19 | Complexity proof | `partition_comparisons_linear` |
| `CLRS.Ch07.Partition.Impl.fsti` | 50 | Impl interface (#lang-pulse) | `clrs_partition_wrapper_with_ticks` |
| `CLRS.Ch07.Partition.Impl.fst` | 230 | Pulse implementation | `tick`, `swap`, `clrs_partition_with_ticks`, wrapper |
| `CLRS.Ch07.Quicksort.Spec.fst` | 56 | Pure predicates | `seq_min/max`, `complexity_bounded_quadratic`, pre/post |
| `CLRS.Ch07.Quicksort.Lemmas.fsti` | 62 | Lemma interface | All quicksort lemma signatures |
| `CLRS.Ch07.Quicksort.Lemmas.fst` | 101 | Lemma proofs | `lemma_sorted_append`, `append_permutations_3`, complexity bound |
| `CLRS.Ch07.Quicksort.Complexity.fsti` | 32 | Complexity interface | `worst_case_comparisons`, `sum_of_parts_bound`, etc. |
| `CLRS.Ch07.Quicksort.Complexity.fst` | 97 | Complexity proofs | Recurrence T(n)=n(n−1)/2, convexity, monotonicity |
| `CLRS.Ch07.Quicksort.Impl.fsti` | 56 | Impl interface (#lang-pulse) | `quicksort`, `quicksort_with_complexity`, `quicksort_bounded` |
| `CLRS.Ch07.Quicksort.Impl.fst` | 202 | Pulse implementation | `quicksort_proof`, recursive sort, top-level API |
| `README.md` | — | Documentation | |
| `Makefile` | — | Build | |

---

## Algorithms Covered (CLRS References)

| CLRS Algorithm | Section | Status | Implementation |
|----------------|---------|--------|----------------|
| PARTITION (Lomuto) | §7.1 | ✅ Implemented | `clrs_partition_with_ticks` (line 214) |
| QUICKSORT | §7.1 | ✅ Implemented | `clrs_quicksort_with_ticks` (line 505) |
| RANDOMIZED-PARTITION | §7.3 | ❌ Missing | — |
| RANDOMIZED-QUICKSORT | §7.3 | ❌ Missing | — |
| Worst-case analysis T(n) = n(n−1)/2 | §7.2 | ✅ Proved | `Quicksort.Complexity.fst` + inline in `Quicksort.fst` |
| Expected O(n lg n) analysis | §7.4.2, Thm 7.4 | ❌ Missing | — |

---

## Rubric Compliance Matrix

The canonical rubric requires these files per algorithm:

### Partition (`CLRS.Ch07.Partition.*`)

| Required File | Status | Current Location |
|---------------|--------|------------------|
| `CLRS.Ch07.Partition.Lemmas.fsti` | ✅ Done | Shared definitions (`between_bounds`, `seq_swap`, etc.) + lemma interface |
| `CLRS.Ch07.Partition.Lemmas.fst` | ✅ Done | `seq_swap_commute`, `permutation_swap` [SMTPat], `transfer_larger_slice`, `transfer_smaller_slice` |
| `CLRS.Ch07.Partition.Complexity.fst` | ✅ Done | `partition_comparisons_linear`: exactly n−1 comparisons |
| `CLRS.Ch07.Partition.Complexity.fsti` | ✅ Done | Interface for partition complexity |
| `CLRS.Ch07.Partition.Impl.fst` | ✅ Done | `tick`, `swap`, `clrs_partition_with_ticks`, wrapper, `clrs_partition_pred` |
| `CLRS.Ch07.Partition.Impl.fsti` | ✅ Done | `#lang-pulse` interface exposing `clrs_partition_wrapper_with_ticks` |

### Quicksort (`CLRS.Ch07.Quicksort.*`)

| Required File | Status | Current Location |
|---------------|--------|------------------|
| `CLRS.Ch07.Quicksort.Lemmas.fsti` | ✅ Done | Shared definitions (`seq_min`, `seq_max`, `complexity_bounded_quadratic`) + lemma interface |
| `CLRS.Ch07.Quicksort.Lemmas.fst` | ✅ Done | `lemma_sorted_append`, `append_permutations_3`, `lemma_quicksort_complexity_bound`, bounds lemmas |
| `CLRS.Ch07.Quicksort.Complexity.fst` | ✅ Done | `worst_case_comparisons`, `worst_case_bound`, `sum_of_parts_bound`, `partition_split_bounded`, `worst_case_monotonic` |
| `CLRS.Ch07.Quicksort.Complexity.fsti` | ✅ Done | Interface with val signatures for all complexity functions |
| `CLRS.Ch07.Quicksort.Impl.fst` | ✅ Done | `quicksort_proof`, `clrs_quicksort_with_ticks`, `clrs_quicksort`, `quicksort_with_complexity`, `quicksort`, `quicksort_bounded`, `pure_pre/post_quicksort` |
| `CLRS.Ch07.Quicksort.Impl.fsti` | ✅ Done | `#lang-pulse` interface exposing `quicksort`, `quicksort_with_complexity`, `quicksort_bounded` |

### Summary

| Rubric Slot | Partition | Quicksort |
|-------------|-----------|-----------|
| `Lemmas.fst` | ✅ | ✅ |
| `Lemmas.fsti` | ✅ (includes shared defs) | ✅ (includes shared defs) |
| `Complexity.fst` | ✅ | ✅ |
| `Complexity.fsti` | ✅ | ✅ |
| `Impl.fst` | ✅ | ✅ |
| `Impl.fsti` | ✅ | ✅ |

**Overall: 12/12 rubric slots fully compliant (100%).** Spec modules folded into Lemmas.fsti (shared defs) and Impl.fst (internal predicates).

---

## Detailed Action Items

All action items from the original rubric have been completed:

| # | Action | Status |
|---|--------|--------|
| 1 | [SPLIT] Extract partition specs | ✅ Done (folded into Lemmas.fsti + Impl.fst) |
| 2 | [SPLIT] Extract `CLRS.Ch07.Partition.Lemmas.fst` | ✅ Done |
| 3 | [ADD_INTERFACE] Create `CLRS.Ch07.Partition.Lemmas.fsti` | ✅ Done |
| 4 | [SPLIT] Extract `CLRS.Ch07.Partition.Impl.fst` | ✅ Done |
| 5 | [ADD_INTERFACE] Create `CLRS.Ch07.Partition.Impl.fsti` | ✅ Done (`#lang-pulse`) |
| 6 | [CREATE] `CLRS.Ch07.Partition.Complexity.fst` | ✅ Done |
| 7 | [ADD_INTERFACE] `CLRS.Ch07.Partition.Complexity.fsti` | ✅ Done |
| 8 | [SPLIT] Extract quicksort specs | ✅ Done (folded into Lemmas.fsti + Impl.fst) |
| 9 | [SPLIT] Extract `CLRS.Ch07.Quicksort.Lemmas.fst` | ✅ Done |
| 10 | [ADD_INTERFACE] Create `CLRS.Ch07.Quicksort.Lemmas.fsti` | ✅ Done |
| 11 | [ADD_INTERFACE] Create `CLRS.Ch07.Quicksort.Complexity.fsti` | ✅ Done |
| 12 | [RENAME] `Quicksort.fst` → `Quicksort.Impl.fst` | ✅ Done |
| 13 | [ADD_INTERFACE] Create `CLRS.Ch07.Quicksort.Impl.fsti` | ✅ Done (`#lang-pulse`) |

Note: `quicksort_proof` (ghost fn) is in `Quicksort.Impl.fst` rather than `Quicksort.Lemmas.fst`
because it uses Pulse's `ghost fn` syntax and separation logic operations (`pts_to_range_join`).

### [CREATE] `CLRS.Ch07.RandomizedPartition.Impl.fst` (deferred — §7.3)

Implement RANDOMIZED-PARTITION and RANDOMIZED-QUICKSORT from §7.3. Requires a random-number source (ghost/erased random oracle).

### [CREATE] Expected-case complexity proof (deferred — §7.4.2)

Prove Theorem 7.4: expected running time of RANDOMIZED-QUICKSORT is O(n lg n). Requires probability formalization and indicator random variables.

---

## Quality Checks

### Admits / Assumes

| File | Count | Details |
|------|------:|---------|
| `CLRS.Ch07.Partition.Lemmas.fst` | 0 | ✅ Admit-free, assume-free |
| `CLRS.Ch07.Partition.Complexity.fst` | 0 | ✅ Admit-free, assume-free |
| `CLRS.Ch07.Partition.Impl.fst` | 0 | ✅ Admit-free, assume-free |
| `CLRS.Ch07.Quicksort.Lemmas.fst` | 0 | ✅ Admit-free, assume-free |
| `CLRS.Ch07.Quicksort.Complexity.fst` | 0 | ✅ Admit-free, assume-free |
| `CLRS.Ch07.Quicksort.Impl.fst` | 0 | ✅ Admit-free, assume-free |

### Proof Stability

| File | `#push-options` blocks | `--retry` usage | `--z3rlimit_factor` | Status |
|------|:----------------------:|:---------------:|:-------------------:|--------|
| All files | 0 | None | None | ✅ Stable |

All 13 source files verify at default rlimits with zero retries.

### Imports / Dependencies

| Check | Status | Details |
|-------|--------|---------|
| Uses `CLRS.Common.SortSpec` | ✅ | Imported in Spec and Lemmas modules |
| No duplicate `sorted` def | ✅ | Imported from `SortSpec` |
| No duplicate `permutation` def | ✅ | Imported from `SortSpec` |
| Clean module dependencies | ✅ | Partition.Lemmas → Partition.Impl; Quicksort.Lemmas → Quicksort.Impl |
| No orphaned modules | ✅ | Old monolithic `Quicksort.fst` removed |

### Functional Correctness Properties

| Property | Partition | Quicksort |
|----------|-----------|-----------|
| Permutation preservation | ✅ `permutation s0 s` | ✅ `permutation s0 s` |
| Partition correctness (≤ pivot / > pivot) | ✅ | N/A |
| Pivot placement | ✅ `Seq.index s (p - lo) == pivot` | N/A |
| Sorted output | N/A | ✅ `sorted s` |
| Bounds preservation | ✅ `between_bounds s lb rb` | ✅ `between_bounds s lb rb` |
| Complexity bound | ✅ `complexity_exact_linear` — exactly n−1 comparisons | ✅ `complexity_bounded_quadratic` — ≤ n(n−1)/2 |

### Top-Level API Completeness

| API Function | Sorted | Permutation | Complexity | Bounds |
|-------------|:------:|:-----------:|:----------:|:------:|
| `quicksort` | ✅ | ✅ | ❌ Not exposed | ❌ Hidden |
| `quicksort_with_complexity` | ✅ | ✅ | ✅ Quadratic | ❌ Hidden |
| `quicksort_bounded` | ✅ | ✅ | ❌ Not exposed | ✅ Caller-provided |

### Documentation

| Check | Status | Details |
|-------|--------|---------|
| Module headers accurate | ✅ | All files have accurate headers |
| README up-to-date | ✅ | Updated with full file inventory and structure |
| Inline CLRS mapping comments | ✅ | SNIPPET markers present for key signatures |
| Complexity module documented | ✅ | `Quicksort.Complexity.fst` listed in README |
