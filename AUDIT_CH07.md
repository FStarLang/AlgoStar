# Audit Report: Chapter 07 — Quicksort

**Date:** 2025-07-18
**Files audited:**
- `ch07-quicksort/CLRS.Ch07.Partition.fst` (272 lines)
- `ch07-quicksort/CLRS.Ch07.LomutoPartition.fst` (287 lines)
- `ch07-quicksort/CLRS.Ch07.Quicksort.fst` (710 lines)
- `ch07-quicksort/CLRS.Ch07.Quicksort.Complexity.fst` (97 lines)
- `ch07-quicksort/README.md`

**Total:** 1,364 lines of F*/Pulse code

---

## 1. CLRS Fidelity

### 1.1 CLRS Pseudocode Reference

CLRS §7.1 presents the **Lomuto partition scheme**:

```
PARTITION(A, p, r)
  x = A[r]
  i = p - 1
  for j = p to r - 1
    if A[j] <= x
      i = i + 1
      exchange A[i] with A[j]
  exchange A[i+1] with A[r]
  return i + 1

QUICKSORT(A, p, r)
  if p < r
    q = PARTITION(A, p, r)
    QUICKSORT(A, p, q - 1)
    QUICKSORT(A, q + 1, r)
```

CLRS §7.3 additionally presents:

```
RANDOMIZED-PARTITION(A, p, r)
  i = RANDOM(p, r)
  exchange A[r] with A[i]
  return PARTITION(A, p, r)

RANDOMIZED-QUICKSORT(A, p, r)
  if p < r
    q = RANDOMIZED-PARTITION(A, p, r)
    RANDOMIZED-QUICKSORT(A, p, q - 1)
    RANDOMIZED-QUICKSORT(A, q + 1, r)
```

### 1.2 Partition Scheme Coverage

| CLRS Algorithm | File | Status |
|---|---|---|
| PARTITION (Lomuto, §7.1) | `LomutoPartition.fst` | ✅ Faithful |
| PARTITION (Lomuto, §7.1) | `Quicksort.fst` `clrs_partition_with_ticks` | ✅ Faithful (re-implemented inline) |
| QUICKSORT (§7.1) | `Quicksort.fst` `clrs_quicksort_with_ticks` | ✅ Faithful |
| RANDOMIZED-PARTITION (§7.3) | — | ❌ **Missing** |
| RANDOMIZED-QUICKSORT (§7.3) | — | ❌ **Missing** |

**Finding 1a — Hoare vs. Lomuto:** CLRS Chapter 7 presents the **Lomuto** partition scheme as the primary algorithm. The Hoare partition (Problem 7-1) is presented only as an exercise. Both `Partition.fst` and `LomutoPartition.fst` implement Lomuto-style partitions. There is **no** Hoare partition implementation. This is consistent with the textbook's main presentation.

**Finding 1b — `Partition.fst` is a variant, not CLRS-faithful:** `Partition.fst` takes an *external* pivot value and partitions a flat array `a[0..n)` — the pivot is not an element of the array. CLRS PARTITION always uses the last element `A[r]` as pivot. This is a useful building block but does **not** match CLRS. The module header says "the two-pointer approach from CLRS" which is somewhat misleading.

**Finding 1c — `Partition.fst` is orphaned:** `Partition.fst` is not imported by any other module. `Quicksort.fst` re-implements its own `clrs_partition_with_ticks` that *does* faithfully follow CLRS (uses last element as pivot, returns pivot index).

**Finding 1d — Half-open vs. closed intervals:** CLRS uses **closed** intervals `A[p..r]`. The implementation uses **half-open** intervals `a[lo..hi)` where `hi` is exclusive. This is a standard and correct engineering choice (avoids off-by-one issues with 0-based indexing). The CLRS recursive calls are:
- CLRS: `QUICKSORT(A, p, q-1)` and `QUICKSORT(A, q+1, r)`
- Code: `clrs_quicksort_with_ticks a lo p ...` and `clrs_quicksort_with_ticks a (p+1) hi ...`

This correctly adapts the CLRS structure to half-open ranges.

**Finding 1e — RANDOMIZED-QUICKSORT missing:** CLRS §7.3 is an important section. The randomized version is what makes quicksort practical (expected O(n lg n) on all inputs). Not implemented.

### 1.3 Fidelity Rating

| Criterion | Rating |
|---|---|
| PARTITION (Lomuto) | ⭐⭐⭐⭐⭐ Faithful |
| QUICKSORT | ⭐⭐⭐⭐⭐ Faithful |
| RANDOMIZED variants | ⭐☆☆☆☆ Missing |
| Overall Chapter Coverage | ⭐⭐⭐☆☆ ~60% (§7.1, §7.2 done; §7.3 missing) |

---

## 2. Specification Strength

### 2.1 Partition Specifications

#### `Partition.fst` — `partition`

**Postconditions proved:**
1. ✅ Length preservation: `Seq.length s == Seq.length s0`
2. ✅ Valid split point: `SZ.v result <= SZ.v n`
3. ✅ Permutation: `permutation s0 s`
4. ✅ Partition correctness: `is_partitioned s pivot (SZ.v result)`
5. ✅ Complexity: `complexity_bounded_linear cf c0 (SZ.v n)` — exactly n comparisons

**Spec gap — nonneg precondition:** Line 194 requires `forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i >= 0`. This restricts the algorithm to non-negative integers, which is unnecessary — Lomuto partition works on arbitrary integers. This is an artificial restriction.

**Spec gap — external pivot:** The pivot is a parameter, not drawn from the array. This means the postcondition doesn't guarantee the pivot itself appears at the split point (unlike CLRS which guarantees `A[q] == pivot`).

**Rating:** ⭐⭐⭐⭐☆ (strong for what it proves, but external pivot and nonneg constraint weaken it)

#### `LomutoPartition.fst` — `lomuto_partition`

**Postconditions proved:**
1. ✅ Length preservation
2. ✅ Valid split point: `SZ.v p <= SZ.v q /\ SZ.v q <= SZ.v r`
3. ✅ Pivot placement: `Seq.index s (SZ.v q) == Seq.index s0 (SZ.v r)` (pivot from last element)
4. ✅ Left partition: `forall k. p <= k < q ==> s[k] <= pivot`
5. ✅ Right partition: `forall k. q < k <= r ==> s[k] > pivot`

**Spec gap — no permutation proof:** The postcondition does **not** include `permutation s0 s`. The `permutation_sub` predicate is defined (line 106) but never used in the postcondition. This is a significant omission — we know the output is partitioned but not that it's a rearrangement of the input.

**Rating:** ⭐⭐⭐☆☆ (partition correctness proved, but missing permutation is a notable gap)

#### `Quicksort.fst` — `clrs_partition_with_ticks`

**Postconditions proved:**
1. ✅ Length preservation
2. ✅ Valid pivot index: `lo <= p /\ p < hi`
3. ✅ Partition correctness: elements below p are ≤ pivot, above p are > pivot
4. ✅ Pivot placement: `A[p] == pivot`
5. ✅ Permutation: `permutation s0 s`
6. ✅ Bounds preservation: `between_bounds s lb rb` and `lb <= pivot <= rb`
7. ✅ Complexity: `complexity_exact_linear cf c0 (hi - lo - 1)` — exactly `hi-lo-1` comparisons

**Rating:** ⭐⭐⭐⭐⭐ (comprehensive, including both permutation and complexity)

### 2.2 Quicksort Specifications

#### `Quicksort.fst` — `clrs_quicksort_with_ticks`

**Postconditions proved:**
1. ✅ Sorted: `sorted s`
2. ✅ Permutation: `permutation s0 s`
3. ✅ Bounds: `between_bounds s lb rb`
4. ✅ Complexity: `complexity_bounded_quadratic cf c0 (hi - lo)` i.e., `cf - c0 <= n*(n-1)/2`

**Rating:** ⭐⭐⭐⭐⭐

#### `Quicksort.fst` — `quicksort` (top-level API)

**Postconditions proved:**
1. ✅ Sorted: `sorted s`
2. ✅ Permutation: `permutation s0 s`
3. ❌ No complexity guarantee exposed (ghost counter is allocated/freed internally)

**Spec gap — complexity not exposed:** The top-level `quicksort` function creates and destroys the ghost counter internally, so the quadratic bound is proved but not visible to callers.

**Rating:** ⭐⭐⭐⭐☆

### 2.3 Overall Specification Assessment

| Property | Partition.fst | LomutoPartition.fst | Quicksort.fst partition | Quicksort.fst sort |
|---|---|---|---|---|
| Length preservation | ✅ | ✅ | ✅ | ✅ |
| Valid indices | ✅ | ✅ | ✅ | ✅ |
| Partition correctness | ✅ | ✅ | ✅ | N/A |
| Permutation | ✅ | ❌ **Missing** | ✅ | ✅ |
| Sorted output | N/A | N/A | N/A | ✅ |
| Bounds preservation | ❌ | ❌ | ✅ | ✅ |
| Complexity | ✅ (linear) | ❌ | ✅ (linear) | ✅ (quadratic) |

---

## 3. Complexity Results

### 3.1 What Is Proved

| Result | File | Status |
|---|---|---|
| Partition: exactly `n-1` comparisons | `Quicksort.fst:281` | ✅ Proved (ghost ticks) |
| Worst-case recurrence: `T(n) = (n-1) + T(n-1)` | `Quicksort.Complexity.fst:14-16` | ✅ Proved |
| Closed form: `T(n) = n(n-1)/2` | `Quicksort.Complexity.fst:20-23` | ✅ Proved |
| `T(n) ≤ n²` | `Quicksort.Complexity.fst:29-37` | ✅ Proved |
| Partition-split convexity: `T(k) + T(n-k-1) ≤ T(n-1)` | `Quicksort.Complexity.fst:43-62` | ✅ Proved |
| Monotonicity of `worst_case_comparisons` | `Quicksort.Complexity.fst:72-84` | ✅ Proved |
| Quicksort overall: `cf - c0 ≤ n(n-1)/2` | `Quicksort.fst:593` | ✅ Proved |

### 3.2 Ghost Tick Mechanism

Ghost ticks use `Pulse.Lib.GhostReference.ref nat` — fully erased at runtime. Each comparison (`aj <= pivot`) gets exactly one tick. The counter threads through all recursive calls via the `ctr` parameter. This is clean and correct.

### 3.3 What Is NOT Proved

| Result | CLRS Section | Status |
|---|---|---|
| O(n lg n) expected-case (randomized) | §7.4.2, Theorem 7.4 | ❌ **Missing** |
| Best-case O(n lg n) | §7.2 | ❌ Not proved |
| Average-case analysis | §7.4.2 | ❌ Not proved |

The average-case / expected-case O(n lg n) analysis is arguably the most important result of CLRS Chapter 7 (Theorem 7.4) and is entirely absent.

### 3.4 Comment Inaccuracies

**Bug — line 10-12 of `Quicksort.fst`:**
```
3. Partition is Θ(n) - exactly n comparisons
4. Worst-case recurrence: T(n) = T(n-1) + n when partition is maximally unbalanced
5. Closed form: T(n) ≤ n(n+1)/2 = O(n²)
```

- Line 10: Says "exactly n comparisons" but the actual code proves `hi - lo - 1` comparisons (line 281). For an array of size n, partition performs **n-1** comparisons (all elements except the pivot). Should say "exactly n-1 comparisons".
- Line 11: Says `T(n) = T(n-1) + n` but the actual recurrence is `T(n) = T(n-1) + (n-1)`. The code at line 528 correctly has `(n - 1) + worst_case_ticks (n - 1)`.
- Line 12: Says `n(n+1)/2` but the code proves `n(n-1)/2` (line 151: `op_Multiply n (n - 1) / 2`). **The comment is wrong.** The correct closed form is `n(n-1)/2`.

**Bug — line 244 of `Quicksort.fst`:**
```
// This partition performs exactly (hi - lo) comparisons
```
Contradicted by line 281 which proves `hi - lo - 1` comparisons.

---

## 4. Code Quality

### 4.1 Duplication

**Major duplication issue — definitions copied across modules:**

| Definition | `Partition.fst` | `Quicksort.fst` | `Common.SortSpec` |
|---|---|---|---|
| `incr_nat` | ✅ line 39 | ✅ line 39 | — |
| `tick` ghost fn | ✅ line 42 | ✅ line 42 | — |
| `permutation` | ✅ line 63 | ✅ line 118 | ✅ line 31 |
| `permutation_same_length` | ✅ line 65 | ✅ line 120 | ✅ line 34 |
| `permutation_refl` | ✅ line 72 | ✅ line 138 | ✅ line 41 |
| `compose_permutations` | ✅ line 77 | ✅ line 127 | ✅ line 46 |
| `lemma_swap_is_two_upds` | ✅ line 90 | — | ✅ line 56 |
| `swap_is_permutation` | ✅ line 108 | — | ✅ line 71 |
| `sorted` | — | ✅ line 61 | ✅ line 23 |

The `CLRS.Common.SortSpec` module already provides canonical `sorted`, `permutation`, and related lemmas, yet `Quicksort.fst` and `Partition.fst` **do not import it** and instead duplicate all definitions locally. This is a significant maintainability problem.

Similarly, `worst_case_ticks`/`worst_case_comparisons` and `lemma_worst_case_formula`/`worst_case_bound` are duplicated between `Quicksort.fst` (lines 526-551) and `Quicksort.Complexity.fst` (lines 14-24).

### 4.2 Orphaned Code

- **`Partition.fst` is entirely orphaned.** It is not imported by `Quicksort.fst` or any other module. It implements a non-standard variant (external pivot, flat array) that duplicates functionality already in `Quicksort.fst`.
- **`LomutoPartition.fst` is also orphaned.** Not imported by `Quicksort.fst`. It provides a faithful CLRS partition but without permutation proof.
- **`Quicksort.Complexity.fst` is standalone.** It duplicates the complexity lemmas already proved inline in `Quicksort.fst`.

### 4.3 Dead Code

- `LomutoPartition.fst` lines 114-141: `do_swap`, `maybe_swap`, `partition_step` helper functions. `maybe_swap` is never called. `partition_step` is never called (the main loop inlines the logic directly).
- `Quicksort.fst` line 34: `seq_swap` and line 192: `seq_swap_commute` — these are only used by the `swap` function and `permutation_swap`.
- `LomutoPartition.fst` line 106: `permutation_sub` is defined but never used in any postcondition.

### 4.4 Naming

- `Partition.fst` vs `LomutoPartition.fst` — confusing since both implement Lomuto-style partitions. `Partition.fst` should be called something like `ExternalPivotPartition`.
- `clrs_partition_with_ticks` vs `lomuto_partition` — inconsistent naming. Both are Lomuto.
- `i_plus_1` naming in `LomutoPartition.fst` is good — clearly documents the off-by-one adaptation from CLRS's `i = p - 1`.

### 4.5 Organization

The chapter would benefit from:
1. A single `CLRS.Ch07.Partition.fst` that faithfully implements CLRS PARTITION (as `clrs_partition_with_ticks` currently does in `Quicksort.fst`).
2. `Quicksort.fst` importing from Partition and from `Common.SortSpec`.
3. Moving complexity proofs entirely to `Quicksort.Complexity.fst` and importing from there.

---

## 5. Proof Quality

### 5.1 Admits and Assumes

| File | Line | Type | Description |
|---|---|---|---|
| — | — | — | **None found in any `.fst` file** |

✅ **All four source files are admit-free and assume-free.** This is excellent.

**Note:** The `README.md` line 111 claims "One `admit()` in optional `quicksort` wrapper" but this is **stale/incorrect** — no admits exist in the current code. The README should be updated.

### 5.2 Z3 Resource Limits and Retries

| File | Line | Setting | Scope |
|---|---|---|---|
| `LomutoPartition.fst` | 175 | `--z3rlimit 200 --fuel 2 --ifuel 1` | `lomuto_partition` |
| `Quicksort.fst` | 246 | `--z3rlimit_factor 8 --retry 5` | `clrs_partition_with_ticks` |
| `Quicksort.fst` | 367 | `--z3rlimit_factor 8 --retry 5` | `clrs_partition_wrapper_with_ticks` |
| `Quicksort.fst` | 441 | `--retry 5` | `lemma_sorted_append` |
| `Quicksort.fst` | 646 | `--z3rlimit_factor 8 --retry 5` | `clrs_quicksort` (wrapper) |

**Assessment:**
- `--z3rlimit_factor 8` is 8× the default (which is typically 5, so this is effectively `z3rlimit 40`). Moderate but acceptable for separation-logic proofs with arrays.
- `--retry 5` appears on 4 of 5 push-options blocks. This indicates **proof instability** — the proofs sometimes fail and need multiple Z3 attempts. While the proofs do eventually succeed, this is a maintainability concern.
- `--z3rlimit 200` in `LomutoPartition.fst` is high and suggests the proof is expensive.
- `Partition.fst` and `Quicksort.Complexity.fst` need **no** special options — these are clean proofs.

### 5.3 Proof Techniques

- **Opaque permutation:** `permutation` is marked `[@@"opaque_to_smt"]` and manually revealed — this is correct practice to prevent SMT blow-up.
- **SMT patterns:** Appropriate patterns on `permutation_refl`, `permutation_same_length`, `compose_permutations`, and `permutation_swap`.
- **Separation logic:** Clean use of `pts_to_range` splitting/joining for divide-and-conquer ownership transfer.
- **Ghost proof function:** `quicksort_proof` (line 486) nicely isolates the post-recursive-call reasoning.
- **Squash wrappers:** `append_permutations_3_squash` and `lemma_sorted_append_squash` enable calling lemmas from ghost contexts — good technique.

---

## 6. Documentation & Comments

### 6.1 Module Headers

| File | Header Quality | Issues |
|---|---|---|
| `Partition.fst` | Good — lists 6 proven properties | Line 10: "exactly n comparisons" should be "exactly n" (since pivot is external, all n elements are compared). Actually correct for this variant. But line 19 "NO admits. NO assumes" is correct. |
| `LomutoPartition.fst` | Good — includes CLRS pseudocode | Accurate |
| `Quicksort.fst` | Good — lists 5 key results | **Lines 10-12 contain errors** (see §3.4) |
| `Quicksort.Complexity.fst` | Good | Accurate |

### 6.2 README.md

- **Stale information:** Line 111 claims an `admit()` exists; none does.
- **Stale information:** Line 123 repeats the admit claim.
- **Path error:** Line 93 says `cd /home/nswamy/workspace/clrs/ch07-quicksort` — incorrect absolute path.
- **Missing information:** Does not mention `LomutoPartition.fst`, `Partition.fst`, or `Quicksort.Complexity.fst`.

### 6.3 Inline Comments

Generally good. The CLRS mapping comments (e.g., `// x = A[r]`, `// i = p - 1`, `// for j = p to r-1`) in `LomutoPartition.fst` are helpful. The `//SNIPPET_START/END` markers indicate the code is used in documentation, which is a nice practice.

---

## 7. Task List

### Priority Levels
- **P0 — Critical:** Correctness or soundness issues
- **P1 — High:** Significant spec gaps or inaccurate claims
- **P2 — Medium:** Code quality, maintainability, duplication
- **P3 — Low:** Documentation, polish, nice-to-have

### Tasks

| # | Priority | Task | File(s) | Details |
|---|---|---|---|---|
| 0 | **P0** | Why have LomutoPartition.fst and Partition.fst? | `Partition.fst`, `LomutoPartition.fst` | Both implement Lomuto-style partitions. Partition is not CLRS-faithful and is not used by Quicksort. Whereas the partition used by Quicksort really does seem to be closer to Lomuto. Remove the redundant partitions | 
| 1 | **P1** | Fix comment: `n(n+1)/2` → `n(n-1)/2` | `Quicksort.fst:12` | Comment says `T(n) ≤ n(n+1)/2` but code proves `n(n-1)/2`. |
| 2 | **P1** | Fix comment: `T(n) = T(n-1) + n` → `T(n) = T(n-1) + (n-1)` | `Quicksort.fst:11` | Partition cost is n-1, not n. |
| 3 | **P1** | Fix comment: "exactly n comparisons" → "exactly n-1" | `Quicksort.fst:10,244` | Partition compares n-1 elements (excluding pivot). |
| 5 | **P1** | Update README: remove stale admit claims | `README.md:111,123` | No admits exist in current code. |
| 7 | **P2** | Deduplicate: use `CLRS.Common.SortSpec` | `Quicksort.fst`, `Partition.fst` | Remove local copies of `sorted`, `permutation`, `permutation_refl`, `compose_permutations`, `swap_is_permutation`, etc. Import from `common/CLRS.Common.SortSpec.fst`. |
| 8 | **P2** | Deduplicate: merge complexity into `Quicksort.Complexity.fst` | `Quicksort.fst:526-572`, `Quicksort.Complexity.fst` | `worst_case_ticks` and `lemma_worst_case_formula` are defined in both files. Move canonical versions to `Complexity.fst` and import. |
| 12 | **P2** | Reduce `--retry 5` proof instability | `Quicksort.fst` | 4 of 5 push-options use `--retry 5`. Investigate adding intermediate assertions or splitting lemmas to stabilize. |
| 16 | **P3** | Fix README path | `README.md:93` | `cd /home/nswamy/workspace/clrs/ch07-quicksort` → use relative path `cd ch07-quicksort`. |
| 19 | **P3** | Expose complexity bound through top-level `quicksort` | `Quicksort.fst:665-688` | The ghost counter is created/freed internally. Consider adding a version that exposes the bound. |



## Defer

| 14 | **P3** | Implement RANDOMIZED-PARTITION (§7.3) | New file | CLRS §7.3 is a core section. Would require a random-number source (could use a ghost/erased random oracle). |
| 15 | **P3** | Prove O(n lg n) expected-case bound (§7.4.2) | New file | Theorem 7.4 is the crown jewel of Ch7. Would be a significant proof effort (probability + indicator random variables). |
| 17 | **P3** | Update README to document all 4 source files | `README.md` | Currently only describes `Quicksort.fst`. Should mention `Partition.fst`, `LomutoPartition.fst`, `Quicksort.Complexity.fst`. |
| 18 | **P3** | Add `quicksort_bounded` to README/docs | `Quicksort.fst:690-709` | Useful sub-range API not mentioned in any documentation. |

---

## Summary

**Strengths:**
- ✅ Zero admits, zero assumes across all 1,364 lines
- ✅ Full functional correctness: sorted output, permutation preservation, partition correctness
- ✅ Worst-case O(n²) complexity formally proved with ghost ticks, including closed-form `n(n-1)/2`
- ✅ Elegant complexity infrastructure: convexity lemma (`sum_of_parts_bound`), monotonicity
- ✅ Clean separation-logic ownership management through recursive calls
- ✅ CLRS §7.1 PARTITION and QUICKSORT faithfully implemented

**Weaknesses:**
- ❌ CLRS §7.3 RANDOMIZED-QUICKSORT not implemented
- ❌ Expected O(n lg n) analysis (Theorem 7.4) not proved
- ❌ Significant code duplication (permutation, sorted, tick, complexity lemmas)
- ❌ Two orphaned modules (`Partition.fst`, `LomutoPartition.fst`)
- ❌ Inaccurate comments (`n(n+1)/2` vs `n(n-1)/2`, comparison counts)
- ❌ `LomutoPartition.fst` missing permutation postcondition
- ⚠️ Proof instability (`--retry 5` on most proof blocks)

**Overall Quality:** ⭐⭐⭐⭐☆ — Strong verified core with notable organizational and documentation issues.
