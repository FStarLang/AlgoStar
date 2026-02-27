# Audit Report — Chapter 08: Linear-Time Sorting

**Scope:** `ch08-linear-sorting/` — 12 files, 5 275 lines total  
**Date:** 2025-07-18  
**Auditor:** Copilot

---

## 0. File Inventory

| # | File | Lines | Description |
|---|------|------:|-------------|
| 1 | `CountingSort.fst` | 183 | Pulse in-place counting sort (Phase 1: count, Phase 2: write-back) |
| 2 | `CountingSort.Lemmas.fst` | 296 | Pure lemmas for in-place counting sort |
| 3 | `CountingSort.Stable.fst` | 274 | Pulse CLRS-faithful stable counting sort (separate A→B, backward pass) |
| 4 | `CountingSort.StableLemmas.fst` | 574 | Lemmas for stable counting sort (prefix-sum, phase-4 invariants) |
| 5 | `CountingSort.Complexity.fst` | 32 | Θ(n+k) complexity for counting sort |
| 6 | `RadixSort.fst` | 75 | Pulse radix sort: delegates to counting sort (d=1 only) |
| 7 | `RadixSort.Spec.fst` | 832 | Pure spec: radix sort correctness via step list (abstract stable sort) |
| 8 | `RadixSort.MultiDigit.fst` | 1172 | Pure spec: radix sort via concrete insertion-sort-by-digit, distinct elements |
| 9 | `RadixSort.FullSort.fst` | 495 | Bridges Stability → full sort: digit decomposition + lex→numeric |
| 10 | `RadixSort.Stability.fst` | 552 | Core stability theorem: each pass extends sorted range by one digit |
| 11 | `RadixSort.Complexity.fst` | 146 | Θ(d(n+k)) complexity for radix sort |
| 12 | `BucketSort.fst` | 644 | Pure functional bucket sort with insertion sort per bucket |

---

## 1. CLRS Fidelity

### 1.1 Counting Sort

**CLRS COUNTING-SORT (§8.2)** has four phases:
1. Initialize C[0..k] = 0
2. Count occurrences: C[A[j]]++
3. Prefix sum: C[i] += C[i-1]
4. Backward placement: B[C[A[j]]−1] = A[j]; C[A[j]]−−

**`CountingSort.fst` (in-place variant)** — ⚠️ **Differs from CLRS**
- Uses only Phase 1 (count) + Phase 2 (write sorted values back in order by iterating 0..k).
- **No separate output array B** — sorts in-place by overwriting A.
- **No prefix-sum phase**, no backward traversal.
- This is a **valid sorting algorithm** but is NOT the CLRS algorithm. It is simpler: it loses satellite data and does not preserve stability.
- **Fidelity: LOW** — The algorithm is a "distribution sort / histogram sort," not CLRS COUNTING-SORT.

**`CountingSort.Stable.fst` (CLRS-faithful)** — ✅ **Matches CLRS exactly**
- Separate input `a` (read-only, half-permission `#0.5R`) and output `b`.
- Implements all four CLRS phases including prefix sum and backward pass.
- Line 238: `B[C[A[j]]-1] = A[j]` — exact CLRS translation (0-indexed).
- Line 244: `C[A[j]]--` — correct decrement.
- Backward loop (lines 197–259) ensures stability.
- **Fidelity: HIGH**

### 1.2 Radix Sort

**CLRS RADIX-SORT (§8.3):**
```
RADIX-SORT(A, d)
  for i = 1 to d
    use a stable sort to sort array A on digit i
```

**`RadixSort.fst` (Pulse)** — ⚠️ **d=1 only**
- Line 73: `CS.counting_sort a len k_val` — directly delegates to in-place counting sort.
- This is **single-digit only** (d=1). The module header (line 11) explicitly acknowledges this.
- Does NOT use the stable counting sort as subroutine — uses the non-stable in-place variant.
- **Fidelity: LOW** — Correct for d=1, but misses the multi-pass structure.

**`RadixSort.Spec.fst` (Pure, abstract)** — ✅ **Matches CLRS structure**
- Defines `is_stable_sort_by_digit` (line 336) as an abstract specification.
- `radix_invariant` (line 579–601) proves the inductive invariant.
- `radix_sort_correctness` (line 787–811) proves full correctness: permutation + sorted.
- **Key limitation:** Operates on abstract "steps" list — does not connect to any concrete stable sort implementation.
- **Fidelity: HIGH** for the mathematical content.

**`RadixSort.MultiDigit.fst` (Pure, concrete)** — ✅ **Matches CLRS**
- Implements `radix_sort` (lines 149–156) as recursive multi-pass using `stable_sort_on_digit`.
- `stable_sort_on_digit` uses `insertion_sort_by_digit` (not counting sort) — acceptable as a specification.
- Proves full correctness: permutation + sorted (`radix_sort_correct`, line 1139).
- **Key limitation:** Requires `distinct s` (all elements pairwise distinct) — CLRS does not require this.
- Includes a concrete example (CLRS Figure 8.3-like, line 1157).
- **Fidelity: MEDIUM-HIGH** — correct structure but the `distinct` requirement is a real restriction.

**`RadixSort.Stability.fst`** — ✅ **Core stability theorem**
- `lemma_stable_pass_preserves_ordering` (line 360–398): after stable sort on digit d, `sorted_up_to_digit s_out d base`.
- This is the inductive step of CLRS Lemma 8.3.
- `radix_sort_invariant` (line 428–466): complete induction.
- Uses `is_stable_sort_on_digit` — abstract specification with `opaque_to_smt`.
- **Fidelity: HIGH**

**`RadixSort.FullSort.fst`** — ✅ **Bridges digits → values**
- `digit_decomposition` (line 161): k = Σ digit(k,i)·base^i.
- `digits_lex_order_implies_numeric_order` (line 270): lex order ⇒ numeric order.
- `radix_sort_fully_sorted` (line 416): main theorem combining everything.
- **Fidelity: HIGH**

### 1.3 Bucket Sort

**CLRS BUCKET-SORT (§8.4):**
```
BUCKET-SORT(A)
  n = A.length
  for i = 0 to n-1: make B[i] empty list
  for i = 1 to n: insert A[i] into B[⌊nA[i]⌋]
  for i = 0 to n-1: sort B[i] with insertion sort
  concatenate B[0], B[1], ..., B[n-1]
```

**`BucketSort.fst`** — ⚠️ **Generalized variant**
- Uses `int` values with `min_val`/`max_val` range detection (not [0,1) reals).
- Number of buckets is a parameter `k: pos`, not fixed to `n`.
- `bucket_index` (line 98–104) distributes elements based on `(v - min_val) / bucket_size`.
- Uses insertion sort per bucket — matches CLRS.
- **Uniform distribution assumption:** NOT encoded. CLRS assumes input ∈ [0,1) uniform; this implementation works on arbitrary integer lists. The complexity analysis notes (line 617–627) mention the average/worst case distinction but do not formally model the distribution.
- Special case: when all elements are equal (`min_val = max_val`), returns input directly.
- **Fidelity: MEDIUM** — Algorithm structure matches CLRS but generalizes away from [0,1) reals. No distribution assumption formalized.

---

## 2. Specification Strength

### 2.1 What Is Proven

| Property | CountingSort (in-place) | CountingSort.Stable | RadixSort (Pulse) | RadixSort (Spec) | RadixSort (MultiDigit) | BucketSort |
|----------|:-:|:-:|:-:|:-:|:-:|:-:|
| **Sorted** | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Permutation** | ✅ | ✅ | ✅ | ✅ | ✅ | ❌ |
| **Stability** | N/A | ❌ (not in spec) | N/A | ✅ (abstract) | ✅ (for distinct) | N/A |
| **Length preserved** | ✅ (implicit) | ✅ | ✅ | ✅ | ✅ | ✅ |

### 2.2 Key Gaps

1. **CountingSort.Stable postcondition does NOT prove stability.** The ensures clause (line 65–72) only guarantees `sorted sb' /\ permutation sb' sa`. The backward-pass implementation *is* stable, but the formal spec does not state or prove it. This is a **significant gap** since CLRS §8.2 emphasizes stability and radix sort depends on it.

2. **BucketSort does NOT prove permutation.** The postcondition (line 556–557) guarantees `sorted ys /\ List.length ys == List.length xs` but does NOT prove the output is a permutation of the input. The `BUCKET_SORT_PROOF_STATUS.md` documents this was a known gap, though the status file is now stale (it references an `admit()` at line 349 that no longer exists).

3. **RadixSort.MultiDigit requires `distinct s`.** The correctness theorem (`radix_sort_correct`, line 1141) has `distinct s` as a precondition. CLRS radix sort works on sequences with duplicates. This limits applicability.

4. **No formal connection between Pulse and pure specs.** `RadixSort.fst` (Pulse) delegates to `CountingSort.fst` (non-stable), while `RadixSort.Spec.fst` and `RadixSort.Stability.fst` prove properties about abstract stable sorts. There is no proof that the Pulse implementation satisfies the abstract stable sort specification.

---

## 3. Complexity Results

### 3.1 Counting Sort — `CountingSort.Complexity.fst`

- Defines `counting_sort_iterations n k = 2n + k + 1` (line 12).
- Proves upper bound: `≤ 2(n+k) + 1` (line 17–19).
- Proves lower bound: `≥ n + k` (line 30–32).
- **Assessment:** Correct Θ(n+k). However, this is a **paper proof** — the iteration count is a standalone `nat` function, not connected to the actual Pulse algorithm via ghost ticks or any instrumentation. The Pulse code has no cost annotations.

### 3.2 Radix Sort — `RadixSort.Complexity.fst`

- Defines `radix_sort_ops n d k = d * counting_sort_iterations n k` (line 34–35).
- Proves Θ(d(n+k)) bounds (line 54–59): `d(n+k) ≤ ops ≤ 2d(n+k) + d`.
- Various corollaries: linear in n for fixed d,k; linear in d for fixed n,k.
- Concrete example: 32-bit integers with d=4, k=255 → 8n + 1024 ops (line 93–101).
- **Assessment:** Correct paper-level analysis. Same gap as counting sort — not connected to actual code execution.

### 3.3 Bucket Sort — `BucketSort.fst`

- Defines `bucket_sort_cost n k = n + n²/k + n` (line 608–611).
- Proves `bucket_sort_cost n n ≤ 3n` (line 614–616).
- **Assessment:** This models the average case under uniform distribution. The formula is a simplification (e.g., integer division `n²/k` rather than exact expected cost). Not connected to actual code.

### 3.4 Ghost Ticks

**None of the 12 files use ghost ticks or any form of runtime cost instrumentation.** All complexity results are standalone arithmetic lemmas about cost functions that model (but do not measure) the algorithms.

---

## 4. Code Quality

### 4.1 Severe Duplication

The following definitions are **copy-pasted identically** across multiple files:

| Definition | Files (count) |
|-----------|:---:|
| `pow` | Stability, Spec, MultiDigit (3×) |
| `pow_positive` | Stability, Spec, MultiDigit (3×) |
| `digit` | Stability, Spec, MultiDigit (3×) |
| `digit_bound` | Stability, Spec, MultiDigit (3×) |
| `sorted_on_digit` | Stability, MultiDigit (2×) |
| `count` (on `seq nat`) | Stability, Spec, MultiDigit (3×) |
| `permutation` (count-based) | Stability, Spec, MultiDigit (3×) |
| `sorted` (on `seq nat`) | FullSort, Spec, MultiDigit, BucketSort (4×) |
| `count_positive_means_appears` | FullSort, Spec, MultiDigit (3×) |
| `element_appears_means_count_positive` | FullSort, Spec, MultiDigit (3×) |
| `pow_monotonic` | FullSort, Spec (2×) |
| `digit_decomposition` | FullSort, Spec (2×) |
| `permutation_transitive` | Stability, Spec, MultiDigit (3×) |
| `permutation_preserves_bounds` | FullSort, MultiDigit (2×) |
| `digit_sum` / `digit_sum_multi` | FullSort, Spec, MultiDigit (3×) |
| `digit_sum_equal_helper` / `digit_sum_equal_multi` | FullSort, MultiDigit (2×) |
| `lemma_pairwise_le_implies_sorted` / `lemma_pairwise_implies_sorted` | FullSort, Spec (2×) |

**Root cause:** `RadixSort.Spec.fst`, `RadixSort.MultiDigit.fst`, and `RadixSort.Stability.fst` are **completely independent modules** that do not share a common base. Each re-implements digit extraction, power functions, permutation definitions, and sorting predicates from scratch.

Similarly, `RadixSort.FullSort.fst` opens `RadixSort.Stability` but still re-defines `sorted`, `digit_decomposition`, and several helpers because Stability's versions are over `seq nat` while FullSort wants slight variants.

**Impact:** ~800+ lines of pure duplication across the chapter. This is the worst duplication in the entire library so far.

### 4.2 Module Structure

The radix sort modules form three **independent proof tracks** with no code sharing:

```
Track A (Pulse):  RadixSort.fst → CountingSort.fst (d=1 only)
Track B (Pure):   RadixSort.Stability.fst → RadixSort.FullSort.fst (abstract steps)
Track C (Pure):   RadixSort.MultiDigit.fst (concrete insertion sort, distinct-only)
                  RadixSort.Spec.fst (abstract steps, slightly different formulation)
```

There is also redundancy between Track B and Track C — both prove the same CLRS Lemma 8.3 independently, with:
- `Stability + FullSort` using `is_stable_sort_on_digit` (opaque, weaker stability: distinct pairs only)
- `Spec` using `is_stable_sort_by_digit` (opaque, full stability via position tracking)
- `MultiDigit` using `stable_sort_on_digit` = concrete insertion sort by digit

### 4.3 Counting Sort Module Structure — Good

```
CountingSort.fst ← CountingSort.Lemmas.fst        (in-place variant)
CountingSort.Stable.fst ← CountingSort.StableLemmas.fst  (CLRS-faithful)
                        ← CountingSort.Lemmas.fst (shared defs: sorted, permutation)
CountingSort.Complexity.fst (standalone)
```

This is clean. Lemmas are well-separated from Pulse code.

### 4.4 Naming Conventions

Generally consistent within each file. Some inconsistencies across files:
- `sorted_by_digit` (Spec) vs `sorted_on_digit` (Stability, MultiDigit) — same concept, different names.
- `is_stable_sort_by_digit` (Spec) vs `is_stable_sort_on_digit` (Stability) — similar but subtly different definitions.
- `count_le` (StableLemmas) is a unique and well-named concept.

---

## 5. Proof Quality

### 5.1 Admits and Assumes

**Zero `admit()` calls across all 12 files.** ✅  
**Zero `assume` calls across all 12 files.** ✅

This is excellent — the chapter is fully verified at the F*/Pulse level (modulo the specification gaps noted in §2).

### 5.2 Z3 Resource Limits

| File | Max z3rlimit | Notes |
|------|:-----------:|-------|
| `CountingSort.fst` | 120 | Whole-file push |
| `CountingSort.Lemmas.fst` | 100 | `phase2_pos_bound` |
| `CountingSort.Stable.fst` | 120 | Whole-file push |
| `CountingSort.StableLemmas.fst` | 100 | `phase4_b_step` |
| `RadixSort.Stability.fst` | 200 | `lemma_stable_pass_preserves_ordering` |
| `RadixSort.FullSort.fst` | 50 | Moderate |
| `RadixSort.Spec.fst` | 200 | `lemma_stable_sort_preserves_order` |
| `RadixSort.MultiDigit.fst` | 100 | `insertion_sort_stable` |
| `BucketSort.fst` | 200 | `bucket_sort` main function |

The rlimits are generally reasonable. The 200-rlimit proofs (`Stability`, `Spec`, `BucketSort`) are the most fragile.

### 5.3 Opaque Definitions

Good use of `[@@"opaque_to_smt"]` in:
- `CountingSort.Lemmas.fst:22` — `permutation`
- `CountingSort.StableLemmas.fst:379,387` — `phase4_c_inv`, `phase4_b_inv`
- `RadixSort.Stability.fst:70,135` — `sorted_up_to_digit`, `is_stable_sort_on_digit`
- `RadixSort.Spec.fst:335,387` — `is_stable_sort_by_digit`, `sorted_up_to_digit`

Each opaque definition has explicit `reveal_opaque` / unpack helper lemmas. This is well-structured and prevents SMT matching loops.

### 5.4 Proof Architecture

The proofs generally follow sound patterns:
- Phase-based invariants for counting sort (count phase → prefix sum → placement)
- Inductive digit-by-digit reasoning for radix sort
- Block-structured reasoning for bucket sort (inter-bucket ordering)

Particularly notable:
- **StableLemmas** `phase4_b_step` (line 488–532): Elegant per-value case split proving disjoint write ranges.
- **Stability** `stable_preserves_lower_order_pair` (line 251–280): Clean isolation using `indefinite_description_ghost`.
- **MultiDigit** `backward_stability` (line 631–664): Non-trivial backward reasoning from output to input ordering.

---

## 6. Documentation & Comments

### 6.1 Module Headers

All 12 files have descriptive module-level comments. Quality varies:
- **CountingSort.fst** (lines 1–13): Good — lists phases and proven properties.
- **CountingSort.Stable.fst** (lines 1–12): Excellent — lists all four CLRS phases.
- **RadixSort.fst** (lines 1–26): Good — honest about d=1 limitation and what's needed for d>1.
- **RadixSort.Stability.fst** (lines 1–18): Good — states key insight and main theorem.
- **BucketSort.fst** (lines 1–28): Good — lists all proven properties and complexity.

### 6.2 Stale Documentation

- **`BUCKET_SORT_PROOF_STATUS.md`**: References `admit()` at line 349 that no longer exists. The file's "Current State" section is stale — the admit has been resolved. Should be updated or removed.
- **`CountingSort.fst:12`**: Claims "NO admits. NO assumes." — this is correct and verified.
- **`RadixSort.FullSort.fst:19`**: Claims "admits only for complex digit algebra" — **no admits found in the file**. This comment is stale/incorrect.
- **`RadixSort.Spec.fst:13-14`**: Claims "Admits OK for high-level stability lemmas (proof of concept)" — **no admits found in the file**. This comment is stale/incorrect.

### 6.3 Inline Comments

Generally good within the Pulse code. The proof comments in `CountingSort.Lemmas.fst` and `StableLemmas.fst` clearly explain each invariant step. The radix sort theory files have helpful section headers (`========== ... ==========`).

---

## 7. Summary Assessment

### Strengths
1. **Zero admits/assumes** — all 5275 lines verify without proof gaps.
2. **Two counting sort implementations** — one simplified (in-place), one CLRS-faithful (Stable).
3. **Three independent radix sort proof tracks** — redundant but provides confidence.
4. **Strong radix sort theory** — stability, digit decomposition, lex↔numeric ordering all fully proven.
5. **BucketSort fully proven** — sorted + length preserved, including inter-bucket ordering.

### Weaknesses
1. **CountingSort.Stable does not prove stability** in its postcondition — the most critical gap.
2. **BucketSort does not prove permutation** — a significant specification weakness.
3. **Massive duplication** (~800+ lines) across RadixSort modules.
4. **No connection between Pulse and pure specs** — the Pulse radix sort is d=1 only, while the d>1 proofs are pure spec.
5. **MultiDigit requires `distinct` elements** — not a CLRS requirement.
6. **Complexity results are paper-only** — no ghost ticks, no connection to actual code.

---

## 8. Task List

### P0 — Critical (correctness/spec gaps)

| ID | Task | File(s) | Effort |
|----|------|---------|--------|
| T1 | **Add stability to CountingSort.Stable postcondition.** The ensures should state that elements with equal keys maintain their input order. The backward-pass implementation already guarantees this; the proof needs to track input positions through Phase 4. | `CountingSort.Stable.fst`, `CountingSort.StableLemmas.fst` | High (2–3 days) |
| T2 | ✅ **Prove permutation for BucketSort.** Added 6 count-based permutation lemmas and `is_permutation` postcondition. | `BucketSort.fst` | ✅ Done |
| T3 | **Remove `distinct` requirement from RadixSort.MultiDigit.** The `backward_stability` lemma (line 631) and `radix_sort_invariant` (line 778) both require `distinct s`. Generalize to handle duplicate values, matching CLRS. | `RadixSort.MultiDigit.fst` | High (2–4 days) |
| T4 | **Implement multi-digit Pulse radix sort (d>1).** Currently `RadixSort.fst` delegates to single-pass counting sort. Implement the CLRS loop calling `CountingSort.Stable` per digit. | `RadixSort.fst`, new files | High (3–5 days) |
| T5 | ✅ **Connect Pulse counting sort to abstract stability spec.** Created `RadixSort.Bridge.fst` proving that CountingSort.Stable output satisfies `is_stable_sort_on_digit` from `RadixSort.Stability` for d=0, base=k+1. Key insight: at d=0, digit(x,0,k+1)=x for x≤k, so the stability condition is vacuously true (equal digits ⟹ equal values ⟹ contradiction with distinctness). Bridge proves: count equivalence (SeqP ↔ Base), permutation equivalence, sorted ↔ sorted_on_digit, and full `is_stable_sort_on_digit`. | `RadixSort.Bridge.fst` (new, 168 lines) | ✅ Done |
| T6 | ✅ **Extract common RadixSort foundations.** Created `RadixSort.Base.fst` (139 lines) with shared definitions. All three tracks import from it, eliminating ~340 lines of duplication. | `RadixSort.Base.fst` (new) | ✅ Done |
| T7 | **Consolidate radix sort proof tracks.** After T6, consider whether Spec and MultiDigit can be merged, or whether one can be deprecated. Currently three independent proofs of CLRS Lemma 8.3 is excessive. | `RadixSort.Spec.fst`, `RadixSort.MultiDigit.fst` | Medium (1–2 days) |
| T8 | ✅ **Add ghost ticks to Pulse counting sort.** Added tick counters proving `cf == c0 + counting_sort_iterations(n,k)`. Later reverted during int→nat migration (nat refinements + tick arithmetic overwhelms Z3). Complexity theorems remain in `Complexity.fst`. | `CountingSort.fst`, `CountingSort.Stable.fst` | ✅ Done (reverted) |
| T9 | ✅ **Fix stale documentation.** Removed false "admits" claims, updated `BUCKET_SORT_PROOF_STATUS.md`. | `RadixSort.FullSort.fst`, `RadixSort.Spec.fst`, `BUCKET_SORT_PROOF_STATUS.md` | ✅ Done |
| T12 | ✅ **Add CLRS section references in postconditions.** Verified all files already have correct CLRS references. | All files | ✅ Done |

### Defer

| ID | Task | File(s) | Effort |
|----|------|---------|--------|
| T10 | **Formalize uniform distribution for bucket sort.** Add a probabilistic specification or at minimum an assumption predicate `uniform_distribution` that bucket sort's O(n) expected time depends on. | `BucketSort.fst` | Low priority (research) |
| T11 | ✅ **Rename for consistency.** Standardized on `sorted_on_digit` and `is_stable_sort_on_digit`. Removed dead `sorted_by_digit` code from `Spec.fst`. | Multiple files | ✅ Done |

---

## Appendix A: Dependency Graph

```
CountingSort.Lemmas ←── CountingSort.fst
         │
         └──────── CountingSort.Stable.fst
         │              │
CountingSort.StableLemmas ──┘
                            
CountingSort.Complexity    (standalone)

RadixSort.Base ←── RadixSort.Stability ←── RadixSort.FullSort  (Track B)
       │                    │
       │           RadixSort.Bridge ──→ CountingSort.Lemmas  (Tracks A↔B)
       │
       ├── RadixSort.Spec                                    (Track C)
       ├── RadixSort.MultiDigit                              (Track D)
       └── RadixSort.Complexity ──→ CountingSort.Complexity

RadixSort.fst ──→ CountingSort.fst  (Pulse, d=1)

BucketSort                                   (standalone, pure F*)
```

## Appendix B: Definition Duplication Matrix

Entries show the number of files containing identical (or near-identical) copies:

| Definition | Count | Recommendation |
|-----------|:-----:|----------------|
| `pow` / `pow_positive` | 3 | Extract to `RadixSort.Base` |
| `digit` / `digit_bound` | 3 | Extract to `RadixSort.Base` |
| `count` (seq nat) | 3 | Extract to `RadixSort.Base` |
| `permutation` (count-based, seq nat) | 3 | Extract to `RadixSort.Base` |
| `sorted` (seq nat, recursive) | 4 | Extract to common module |
| `sorted_on_digit` | 2 | Extract to `RadixSort.Base` |
| `digit_decomposition` | 2 | Keep in FullSort, remove from Spec |
| `permutation_transitive` | 3 | Extract to `RadixSort.Base` |
| `count_positive_means_appears` | 3 | Extract to `RadixSort.Base` |
| `element_appears_means_count_positive` | 3 | Extract to `RadixSort.Base` |
| `permutation_preserves_bounds` | 2 | Extract to `RadixSort.Base` |
