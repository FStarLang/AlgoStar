# Chapter 07: Quicksort — Rubric Compliance

**Date:** 2025-07-18
**Source files audited:** `CLRS.Ch07.Quicksort.fst` (660 lines), `CLRS.Ch07.Quicksort.Complexity.fst` (97 lines)
**Canonical rubric:** `RUBRIC.md`

---

## Current File Inventory

| File | Lines | Role | Notes |
|------|------:|------|-------|
| `CLRS.Ch07.Quicksort.fst` | 660 | Monolithic: pure specs, lemmas, Pulse impl, inline complexity | Contains everything — partition + quicksort |
| `CLRS.Ch07.Quicksort.Complexity.fst` | 97 | Standalone worst-case complexity proofs | Pure F*, no Pulse; not imported by `Quicksort.fst` |
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
| `CLRS.Ch07.Partition.Spec.fst` | ❌ Missing | Pure predicates are inline in `Quicksort.fst`: `clrs_partition_pred` (line 201), `complexity_exact_linear` (line 114), `between_bounds` (line 58) |
| `CLRS.Ch07.Partition.Lemmas.fst` | ❌ Missing | Helper lemmas inline in `Quicksort.fst`: `permutation_swap` (line 171), `seq_swap_commute` (line 160), `transfer_larger_slice` (line 300), `transfer_smaller_slice` (line 316) |
| `CLRS.Ch07.Partition.Lemmas.fsti` | ❌ Missing | No interface file exists |
| `CLRS.Ch07.Partition.Complexity.fst` | 🔶 Partial | Partition complexity is proved inline (`complexity_exact_linear` at line 248) but not in a separate file |
| `CLRS.Ch07.Partition.Complexity.fsti` | ❌ Missing | No interface file exists |
| `CLRS.Ch07.Partition.Impl.fst` | 🔶 Partial | `clrs_partition_with_ticks` (line 214) and `clrs_partition_wrapper_with_ticks` (line 334) exist in `Quicksort.fst`, not a separate file |
| `CLRS.Ch07.Partition.Impl.fsti` | ❌ Missing | No interface file exists |

### Quicksort (`CLRS.Ch07.Quicksort.*`)

| Required File | Status | Current Location |
|---------------|--------|------------------|
| `CLRS.Ch07.Quicksort.Spec.fst` | ❌ Missing | Pure pre/postconditions inline in `Quicksort.fst`: `pure_pre_quicksort` (line 427), `pure_post_quicksort` (line 435), `complexity_bounded_quadratic` (line 118) |
| `CLRS.Ch07.Quicksort.Lemmas.fst` | ❌ Missing | Proof helpers inline in `Quicksort.fst`: `quicksort_proof` (line 446), `append_permutations_3` (line 390), `lemma_sorted_append` (line 403), `lemma_quicksort_complexity_bound` (line 484) |
| `CLRS.Ch07.Quicksort.Lemmas.fsti` | ❌ Missing | No interface file exists |
| `CLRS.Ch07.Quicksort.Complexity.fst` | ✅ Exists | Standalone file with `worst_case_comparisons`, `worst_case_bound`, `sum_of_parts_bound`, `partition_split_bounded`, `worst_case_monotonic` |
| `CLRS.Ch07.Quicksort.Complexity.fsti` | ❌ Missing | No interface file exists |
| `CLRS.Ch07.Quicksort.Impl.fst` | 🔶 Partial | Pulse implementations exist in monolithic `Quicksort.fst`: `clrs_quicksort_with_ticks` (line 505), `clrs_quicksort` (line 567), `quicksort` (line 615), `quicksort_with_complexity` (line 585), `quicksort_bounded` (line 640) |
| `CLRS.Ch07.Quicksort.Impl.fsti` | ❌ Missing | No interface file exists |

### Summary

| Rubric Slot | Partition | Quicksort |
|-------------|-----------|-----------|
| `Spec.fst` | ❌ | ❌ |
| `Lemmas.fst` | ❌ | ❌ |
| `Lemmas.fsti` | ❌ | ❌ |
| `Complexity.fst` | ❌ | ✅ |
| `Complexity.fsti` | ❌ | ❌ |
| `Impl.fst` | ❌ | 🔶 (monolithic) |
| `Impl.fsti` | ❌ | ❌ |

**Overall: 1/14 rubric slots fully compliant (7%), 2/14 partially compliant (14%).**

---

## Detailed Action Items

### [SPLIT] Extract `CLRS.Ch07.Partition.Spec.fst` from `Quicksort.fst`

Move these pure definitions to a new `CLRS.Ch07.Partition.Spec.fst`:

| Definition | Current Location | Type |
|------------|-----------------|------|
| `clrs_partition_pred` | `Quicksort.fst:201` | Predicate |
| `complexity_exact_linear` | `Quicksort.fst:114` | Predicate |
| `larger_than` | `Quicksort.fst:53` | Predicate |
| `smaller_than` | `Quicksort.fst:56` | Predicate |
| `between_bounds` | `Quicksort.fst:58` | Predicate |

### [SPLIT] Extract `CLRS.Ch07.Partition.Lemmas.fst` from `Quicksort.fst`

Move these lemmas:

| Function | Current Location | Purpose |
|----------|-----------------|---------|
| `seq_swap_commute` | `Quicksort.fst:160` | Swap commutativity |
| `permutation_swap` | `Quicksort.fst:171` | Swap preserves permutation |
| `transfer_larger_slice` | `Quicksort.fst:300` | Bounds transfer for slices |
| `transfer_smaller_slice` | `Quicksort.fst:316` | Bounds transfer for slices |

### [ADD_INTERFACE] Create `CLRS.Ch07.Partition.Lemmas.fsti`

Expose signatures for:
- `val permutation_swap : s:Seq.seq int -> i:nat_smaller (Seq.length s) -> j:nat_smaller (Seq.length s) -> Lemma (permutation s (seq_swap s i j))`
- `val transfer_larger_slice : ...`
- `val transfer_smaller_slice : ...`

### [SPLIT] Extract `CLRS.Ch07.Partition.Impl.fst` from `Quicksort.fst`

Move these Pulse functions:

| Function | Current Location | Lines | Purpose |
|----------|-----------------|-------|---------|
| `tick` | `Quicksort.fst:42` | 42–48 | Ghost tick increment |
| `swap` | `Quicksort.fst:180` | 180–196 | Array swap with permutation proof |
| `op_Array_Access` | `Quicksort.fst:124` | 124–138 | Array read via `pts_to_range` |
| `op_Array_Assignment` | `Quicksort.fst:140` | 140–156 | Array write via `pts_to_range` |
| `clrs_partition_with_ticks` | `Quicksort.fst:214` | 214–296 | Core CLRS PARTITION |
| `clrs_partition_wrapper_with_ticks` | `Quicksort.fst:334` | 334–386 | Partition + range splitting |

### [ADD_INTERFACE] Create `CLRS.Ch07.Partition.Impl.fsti`

Expose the main partition signature (lines 213–250 of `Quicksort.fst`) as a `val`.

### [CREATE] `CLRS.Ch07.Partition.Complexity.fst`

Extract partition-specific complexity from inline proofs. The partition performs exactly `hi - lo - 1` comparisons (proved at line 248). Create a standalone file with:
- `val partition_comparison_count : n:nat{n > 0} -> Lemma (partition compares exactly n-1 elements)`

### [ADD_INTERFACE] Create `CLRS.Ch07.Partition.Complexity.fsti`

Interface for partition complexity.

### [SPLIT] Extract `CLRS.Ch07.Quicksort.Spec.fst` from `Quicksort.fst`

Move these pure spec definitions:

| Definition | Current Location | Type |
|------------|-----------------|------|
| `pure_pre_quicksort` | `Quicksort.fst:427` | Unfold let (precondition) |
| `pure_post_quicksort` | `Quicksort.fst:435` | Unfold let (postcondition) |
| `complexity_bounded_quadratic` | `Quicksort.fst:118` | Predicate |
| `seq_min` | `Quicksort.fst:63` | Ghost function |
| `seq_max` | `Quicksort.fst:70` | Ghost function |

### [SPLIT] Extract `CLRS.Ch07.Quicksort.Lemmas.fst` from `Quicksort.fst`

Move these proof helpers:

| Function | Current Location | Purpose |
|----------|-----------------|---------|
| `lemma_seq_min_is_min` | `Quicksort.fst:77` | Min bound correctness |
| `lemma_seq_max_is_max` | `Quicksort.fst:83` | Max bound correctness |
| `lemma_between_bounds_from_min_max` | `Quicksort.fst:89` | Bounds derivation |
| `lemma_min_le_max` | `Quicksort.fst:105` | Min ≤ Max |
| `append_permutations_3` | `Quicksort.fst:390` | 3-way permutation composition |
| `append_permutations_3_squash` | `Quicksort.fst:398` | Squash variant for ghost ctx |
| `lemma_sorted_append` | `Quicksort.fst:403` | Sorted concatenation |
| `lemma_sorted_append_squash` | `Quicksort.fst:414` | Squash variant for ghost ctx |
| `lemma_quicksort_complexity_bound` | `Quicksort.fst:484` | Recursive complexity bound |
| `quicksort_proof` | `Quicksort.fst:446` | Ghost proof combining sub-results |

### [ADD_INTERFACE] Create `CLRS.Ch07.Quicksort.Lemmas.fsti`

Expose signatures for key lemmas above.

### [ADD_INTERFACE] Create `CLRS.Ch07.Quicksort.Complexity.fsti`

Expose signatures for existing `Quicksort.Complexity.fst` functions:
- `val worst_case_comparisons : nat -> nat`
- `val worst_case_bound : n:nat -> Lemma (2 * worst_case_comparisons n == n * (n-1))`
- `val sum_of_parts_bound : a:nat -> b:nat -> Lemma (worst_case_comparisons a + worst_case_comparisons b <= worst_case_comparisons (a+b))`
- `val partition_split_bounded : n:nat{n>1} -> k:nat{k<n} -> Lemma (...)`
- `val worst_case_monotonic : m:nat -> n:nat{m<=n} -> Lemma (...)`
- `val quicksort_worst_case_theorem : n:nat -> Lemma (2 * worst_case_comparisons n == n*(n-1))`
- `val quicksort_worst_case_quadratic : n:nat -> Lemma (worst_case_comparisons n <= n*n)`

### [RENAME] `CLRS.Ch07.Quicksort.fst` → `CLRS.Ch07.Quicksort.Impl.fst`

After extracting Spec/Lemmas, the remaining file should be renamed to `Impl.fst` and contain only:
- `clrs_quicksort_with_ticks` (recursive Pulse impl)
- `clrs_quicksort` (internal wrapper)
- `quicksort_with_complexity` (complexity-exposing API)
- `quicksort` (top-level API)
- `quicksort_bounded` (sub-range API)

### [ADD_INTERFACE] Create `CLRS.Ch07.Quicksort.Impl.fsti`

Public API signatures:

```fstar
val quicksort (a: A.array int) (len: SZ.t) (#s0: Ghost.erased (Seq.seq int))
  : stt unit
    (requires A.pts_to a s0 ** pure (Seq.length s0 == A.length a /\ A.length a == SZ.v len /\ SZ.v len > 0))
    (ensures fun _ -> exists* s. A.pts_to a s ** pure (sorted s /\ permutation s0 s))

val quicksort_with_complexity (a: A.array int) (len: SZ.t) (#s0: ...) (ctr: GR.ref nat) (#c0: ...)
  : stt unit ... (ensures ... complexity_bounded_quadratic cf c0 (SZ.v len))

val quicksort_bounded (a: A.array int) (lo: nat) (hi: nat{lo <= hi}) (lb rb: erased int) (#s0: ...)
  : stt unit ... (ensures ... sorted s /\ permutation s0 s)
```

### [CREATE] `CLRS.Ch07.RandomizedPartition.Impl.fst` (deferred — §7.3)

Implement RANDOMIZED-PARTITION and RANDOMIZED-QUICKSORT from §7.3. Requires a random-number source (ghost/erased random oracle).

### [CREATE] Expected-case complexity proof (deferred — §7.4.2)

Prove Theorem 7.4: expected running time of RANDOMIZED-QUICKSORT is O(n lg n). Requires probability formalization and indicator random variables.

---

## Quality Checks

### Admits / Assumes

| File | Count | Details |
|------|------:|---------|
| `CLRS.Ch07.Quicksort.fst` | 0 | ✅ Admit-free, assume-free |
| `CLRS.Ch07.Quicksort.Complexity.fst` | 0 | ✅ Admit-free, assume-free |

### Proof Stability

| File | `#push-options` blocks | `--retry` usage | `--z3rlimit_factor` | Status |
|------|:----------------------:|:---------------:|:-------------------:|--------|
| `CLRS.Ch07.Quicksort.fst` | 0 | None | None | ✅ Stable |
| `CLRS.Ch07.Quicksort.Complexity.fst` | 0 | None | None | ✅ Stable |

### Imports / Dependencies

| Check | Status | Details |
|-------|--------|---------|
| Uses `CLRS.Common.SortSpec` | ✅ | `open CLRS.Common.SortSpec` at line 29 |
| No duplicate `sorted` def | ✅ | Imported from `SortSpec` |
| No duplicate `permutation` def | ✅ | Imported from `SortSpec` |
| `Quicksort.Complexity.fst` imported | ❌ | Standalone, not imported by `Quicksort.fst`; inline `lemma_quicksort_complexity_bound` duplicates logic |
| No orphaned modules | ✅ | Old `Partition.fst` and `LomutoPartition.fst` removed per audit |

### Functional Correctness Properties

| Property | Partition | Quicksort |
|----------|-----------|-----------|
| Permutation preservation | ✅ `permutation s0 s` (line 246) | ✅ `permutation s0 s` (line 441) |
| Partition correctness (≤ pivot / > pivot) | ✅ (lines 238–243) | N/A |
| Pivot placement | ✅ `Seq.index s (p - lo) == pivot` (line 242) | N/A |
| Sorted output | N/A | ✅ `sorted s` (line 439) |
| Bounds preservation | ✅ `between_bounds s lb rb` (line 245) | ✅ `between_bounds s lb rb` (line 440) |
| Complexity bound | ✅ `complexity_exact_linear` — exactly n−1 comparisons (line 248) | ✅ `complexity_bounded_quadratic` — ≤ n(n−1)/2 (line 522) |

### Top-Level API Completeness

| API Function | Sorted | Permutation | Complexity | Bounds |
|-------------|:------:|:-----------:|:----------:|:------:|
| `quicksort` (line 615) | ✅ | ✅ | ❌ Not exposed | ❌ Hidden |
| `quicksort_with_complexity` (line 585) | ✅ | ✅ | ✅ Quadratic | ❌ Hidden |
| `quicksort_bounded` (line 640) | ✅ | ✅ | ❌ Not exposed | ✅ Caller-provided |

### Documentation

| Check | Status | Details |
|-------|--------|---------|
| Module header accurate | ✅ | Lines 10–12 corrected per audit (n−1 comparisons, n(n−1)/2) |
| README up-to-date | ✅ | Stale admit claims removed per audit |
| Inline CLRS mapping comments | ✅ | SNIPPET markers present for key signatures |
| `Quicksort.Complexity.fst` not mentioned in README | ❌ | Deferred task #17 from audit |
