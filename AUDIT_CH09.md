# Audit Report: Chapter 09 — Order Statistics

**Scope:** `ch09-order-statistics/` (11 files)
**Date:** 2025-07-15
**Auditor:** Copilot

---

## 1. CLRS Fidelity

### 1.1 MINIMUM / MAXIMUM (§9.1)

**CLRS reference:** `MINIMUM(A)` — linear scan, `n − 1` comparisons, optimal.

**Implementation:** `CLRS.Ch09.MinMax.fst` — `find_minimum` and `find_maximum`.
- **Structure:** Faithful transcription. Initializes from `a[0]`, scans `i = 1..n−1`, tracks running min/max. ✅
- **Pivot selection:** Uses `a[0]` as initial, exactly like CLRS uses `A[1]`. ✅
- **Comparison count:** Proves exactly `n − 1` comparisons via ghost tick counter. This matches CLRS's stated optimality. ✅
- **Deviation:** None.

**Verdict: Faithful to CLRS §9.1 MINIMUM/MAXIMUM.**

### 1.2 Simultaneous Min/Max (§9.1)

**CLRS reference:** Pair-processing algorithm using **3⌊n/2⌋** comparisons — compare pairs against each other first, then smaller vs. current min, larger vs. current max.

**Implementation:** `CLRS.Ch09.SimultaneousMinMax.fst` — `find_minmax` and `find_minmax_complexity`.
- **Structure:** Simple linear scan doing 2 comparisons per element (one vs. min, one vs. max). ⚠️
- **Comparison count:** Proves exactly **2(n − 1)** comparisons, not 3⌊n/2⌋. ⚠️
- **Comment on line 7–9** openly acknowledges this: *"This implementation uses a linear scan (2n−2 comparisons)... The optimized pair-processing algorithm from CLRS Section 9.1 (using 3⌊n/2⌋ comparisons) requires more complex case analysis."*

| Metric | CLRS | Implementation |
|--------|------|----------------|
| Comparisons | 3⌊n/2⌋ ≈ 1.5n | 2(n−1) ≈ 2n |
| For n=100 | 150 | 198 |

**Verdict: ❌ Does NOT implement the CLRS pair-processing algorithm.** The file name is somewhat misleading — it is a "simultaneous" scan (finding both at once) but not the optimized CLRS algorithm. The honest documentation partially mitigates this, but the algorithm is asymptotically worse by a constant factor (2n vs 1.5n).

### 1.3 RANDOMIZED-SELECT / Quickselect (§9.2)

**CLRS reference:** `RANDOMIZED-SELECT(A, p, r, i)` — recursive, uses `RANDOMIZED-PARTITION` (random pivot), O(n) expected.

**Implementation:** `CLRS.Ch09.Quickselect.fst` — `partition_in_range` + `quickselect`.
- **Algorithm structure:** Iterative (tail-call optimized) vs. CLRS's recursive. Functionally equivalent. ✅
- **Pivot selection:** Uses **last element** `a[hi−1]` as pivot (deterministic), not a random pivot. ⚠️
  - Comment on line 7 claims "O(n) expected (same as CLRS RANDOMIZED-SELECT)" — this is **misleading** since without randomization there is no probabilistic guarantee. The deterministic variant has Θ(n²) worst case on adversarial inputs.
- **Partition:** Lomuto-style partition (CLRS PARTITION from §7.1), faithful. ✅
- **Termination:** Loop narrows `[lo, hi)` around `k` each iteration. Correct but no explicit termination metric in the invariant.

**Verdict: Partially faithful.** Structurally correct quickselect, but deterministic pivot makes the "O(n) expected" claim in comments inaccurate. Should be renamed or the randomization gap documented more prominently.

### 1.4 PartialSelectionSort (Custom — NOT in CLRS)

**Implementation:** `CLRS.Ch09.PartialSelectionSort.fst` — `select`.
- **Algorithm:** Performs `k` rounds of selection sort (find-min + swap), returning the k-th smallest.
- **CLRS status:** **Not a CLRS algorithm.** CLRS §9 presents RANDOMIZED-SELECT (§9.2) and median-of-medians SELECT (§9.3), neither of which is a partial selection sort.
- **Documentation honesty:** Lines 6–12 and 30–34 openly acknowledge this deviation and explain the trade-offs. ✅
- **Complexity:** O(nk) vs. CLRS's O(n) expected. For median (k = n/2), this is O(n²). ⚠️

**Verdict: Custom algorithm, not CLRS.** Well-documented as such. Serves as a simpler verified baseline.

---

## 2. Specification Strength

### 2.1 Quickselect — Does it prove it finds the i-th smallest?

**Postcondition of `quickselect` (lines 234–241):**
```fstar
result == Seq.index s_final (SZ.v k)   // result is s_final[k]
permutation s0 s_final                  // s_final is a permutation of s0
```

**What this proves:** The result is the value at position `k` in some rearrangement of the input.

**What this does NOT prove:** That `result` equals the k-th order statistic (i.e., `(sort s0)[k]`). The `kth_order_property` predicate is defined (line 214) but **never used** in any postcondition — it is dead code.

**Gap:** The postcondition does not prove that elements `[0,k)` are all ≤ `s_final[k]` and elements `(k,n)` are all ≥ `s_final[k]`. The partition property is proved for `partition_in_range` within `[lo,hi)`, but the quickselect loop invariant only tracks the range `[lo, hi)` containing `k` and the permutation — it does **not** propagate the partition ordering from completed iterations to the full array.

**Impact:** This is a **significant spec gap**. A buggy implementation that returns `s_final[k]` from an arbitrary permutation would also satisfy this postcondition. The `Correctness.fst` module provides the theoretical bridge (`pulse_correctness_hint`) but it is not wired into the Pulse implementation.

**PartialSelectionSort** is stronger: its postcondition includes `sorted_prefix s_final k` and `prefix_leq_suffix s_final k`, which together imply the result is the k-th smallest. ✅

### 2.2 Two competing permutation notions

- `CLRS.Ch09.Quickselect.fst` and `CLRS.Ch09.PartialSelectionSort.fst` use `Seq.Properties.permutation` (opaque wrapper).
- `CLRS.Ch09.PartialSelectionSort.Spec.fst` defines its own `is_permutation` based on `count_occ`.
- These two notions are **never connected** — there is no lemma proving they are equivalent.
- The `Correctness.fst` module's `pulse_correctness_hint` requires `is_permutation`, but the Pulse code produces `permutation` (the opaque wrapper).

---

## 3. Complexity Analysis

### 3.1 MinMax

| Algorithm | Bound Proved | Optimal? |
|-----------|-------------|----------|
| `find_minimum` | Exactly n−1 comparisons (ghost ticks) | ✅ Optimal |
| `find_maximum` | Exactly n−1 comparisons (ghost ticks) | ✅ Optimal |
| `find_minmax_complexity` | Exactly 2(n−1) comparisons | ❌ Not optimal (CLRS: 3⌊n/2⌋) |

Ghost tick counting in MinMax is clean and correct — `GhostReference.ref nat` is fully erased at extraction time.

### 3.2 Quickselect

- **`CLRS.Ch09.Quickselect.Complexity.fst`**: Pure F* module defining `qs_cost(n) = n + qs_cost(n−1)` and proving `qs_cost(n) ≤ n(n+1)/2 ≤ n²`. ✅
- **Gap:** This is a **standalone recurrence analysis**, not connected to the Pulse implementation. The Pulse `quickselect` function has no ghost tick counter and no complexity postcondition.
- **No O(n) expected-case proof.** The module only addresses worst case. The comment "O(n) expected" in the implementation is unproven. ⚠️

### 3.3 PartialSelectionSort Complexity

- **`Complexity.fst`**: Proves `select_comparisons n k = k*(n−1)` and `select_comparisons n k ≤ k*n`. ✅
- **`Complexity.Enhanced.fst`**: Proves `snd(select_with_ticks n k) ≤ n²` for worst case, plus a closed form for quickselect recurrence. ✅
- **`Complexity.Test.fst`**: Concrete instantiations (n=10, n=3, etc.). ✅
- **Gap:** Like Quickselect.Complexity, these are pure-F* cost models not connected to the Pulse implementation via ghost ticks.
- **Modeling inaccuracy (Complexity.fst lines 48–56):** Uses `n−1` comparisons per round (overestimate), but the actual code uses `n−i−1` comparisons in round `i`. This is documented but means the bound is not tight.

---

## 4. Code Quality

### 4.1 Duplicated Code (HIGH priority)

| Code Block | Files | Lines |
|-----------|-------|-------|
| `permutation` definition + `permutation_same_length` + `permutation_refl` + `compose_permutations` | `Quickselect.fst` (33–57), `PartialSelectionSort.fst` (55–97) | ~40 lines × 2 |
| `swap_is_permutation` | `Quickselect.fst` (61–85), `PartialSelectionSort.fst` (119–138) | ~25 lines × 2 |
| `incr_nat` + ghost `tick` | `MinMax.fst` (33–41), `SimultaneousMinMax.fst` (34–42) | ~9 lines × 2 |

**Recommendation:** Extract shared infrastructure into a common module (e.g., `CLRS.Common.Permutation`). The tick functions in MinMax and SimultaneousMinMax use `GhostReference` while `CLRS.Common.Complexity` uses `Reference` — these should be unified.

### 4.2 Dead Code

| Item | File | Line |
|------|------|------|
| `kth_order_property` — defined but never used | `Quickselect.fst` | 214–217 |
| `unchanged_outside` — defined but never used in any postcondition | `Quickselect.fst` | 90–95 |
| `partition_preserves_permutation` — trivial identity lemma | `Correctness.fst` | 42–46 |
| `select_partition_spec` — alias for `select_spec`, never used elsewhere | `Correctness.fst` | 226–227 |

### 4.3 Organization

- **Good:** Clean separation of Spec (pure F*), SortedPerm (isolated lemma), Correctness (pure proofs), Complexity (cost models).
- **Good:** Makefile disables `optimize_let_vc` and `fly_deps` with clear comment explaining why.
- **Questionable:** Module naming — `PartialSelectionSort.Correctness` and `PartialSelectionSort.Spec` contain lemmas about quickselect (e.g., `pulse_correctness_hint`, `partition_pivot_is_kth`), not just about PartialSelectionSort.
- **Questionable:** `Complexity.Enhanced.fst` covers both partial selection sort AND quickselect worst case, blurring the boundary.

### 4.4 File Size Distribution

| File | Lines | Purpose |
|------|-------|---------|
| `PartialSelectionSort.Spec.fst` | 674 | Pure spec + helpers — quite large |
| `PartialSelectionSort.fst` | 278 | Main Pulse implementation |
| `Quickselect.fst` | 286 | Main Pulse implementation |
| `PartialSelectionSort.Complexity.Enhanced.fst` | 263 | Enhanced complexity |
| `PartialSelectionSort.Correctness.fst` | 252 | Correctness proofs |
| `SimultaneousMinMax.fst` | 208 | Simultaneous min/max |
| `MinMax.fst` | 173 | Min and max |
| `PartialSelectionSort.Complexity.fst` | 135 | Basic complexity |
| `PartialSelectionSort.Complexity.Test.fst` | 124 | Tests |
| `PartialSelectionSort.SortedPerm.fst` | 89 | Sorted permutation lemma |

---

## 5. Proof Quality — Admits & Assumes

### 5.1 Admits

**None found.** All 11 files are free of `admit` and `assume` in executable positions. ✅

### 5.2 Proof Gaps (Logical, not syntactic)

| # | Gap | Severity | Location |
|---|-----|----------|----------|
| G1 | Quickselect postcondition does not prove k-th order statistic property | **HIGH** | `Quickselect.fst:234–241` |
| G2 | Two permutation notions (`permutation` vs `is_permutation`) never bridged | **HIGH** | `Quickselect.fst:34` vs `Spec.fst:44` |
| G3 | Complexity models not connected to Pulse code (no ghost ticks in quickselect/select) | **MEDIUM** | `Quickselect.Complexity.fst`, `Complexity.Enhanced.fst` |
| G4 | `partition_ordered` only covers `[lo,hi)` range; quickselect never extends this to full array | **HIGH** | `Quickselect.fst:99–105` |

### 5.3 SMT Configuration

- `--z3rlimit` ranges: 20–200 across files. The 200 for `select` (PartialSelectionSort.fst:209) is aggressive.
- `--split_queries always` used in SortedPerm.fst:53 for the key `sorted_permutation_equal` lemma.
- `--z3refresh` and `#restart-solver` used in SortedPerm.fst — indicates solver sensitivity.
- `--warn_error -328` suppressed in Spec.fst:150 for the `rec` annotation on non-recursive-looking functions (needed for Z3 encoding).

---

## 6. Documentation & Comments

### 6.1 Accuracy Issues

| # | Issue | File | Line |
|---|-------|------|------|
| D1 | "O(n) expected (same as CLRS RANDOMIZED-SELECT)" — misleading because pivot is deterministic (last element), not random | `Quickselect.fst` | 7 |
| D2 | "This replaces the O(nk) selection sort approach in Select.fst" — references `Select.fst` which does not exist (it's `PartialSelectionSort.fst`) | `Quickselect.fst` | 8 |
| D3 | Comment says "NO admits, NO assumes" — true, but omits the significant spec gap (result not proven to be k-th smallest) | `Quickselect.fst` | 11 |
| D4 | "Implementing RANDOMIZED-SELECT requires a random number source (not available)" — inaccurate; randomization is available in Pulse | `PartialSelectionSort.fst` | 33 |
| D5 | Header comment for `Complexity.Enhanced.fst` says "Enhanced Complexity Analysis for Quickselect" but it's primarily about partial selection sort | `Complexity.Enhanced.fst` | 24 |
| D6 | `find_maximum` uses predicate name `complexity_bounded_min` for the maximum's complexity bound | `MinMax.fst` | 134 |

### 6.2 Good Documentation

- MinMax.fst: Clear header listing exactly what is proved. ✅
- SimultaneousMinMax.fst: Honestly documents the gap vs CLRS pair-processing. ✅
- PartialSelectionSort.fst: Thorough comparison with CLRS algorithms and honest assessment. ✅
- Spec.fst: Detailed mathematical reasoning in comments (lines 346–359). ✅
- Correctness.fst: Clear outline of the proof strategy and connection to Pulse. ✅

---

## 7. Task List

### Critical (P0) — Correctness Gaps

- [ ] **P0-1: Strengthen quickselect postcondition.** Add the partition ordering property to the postcondition of `quickselect`: `(forall i. i < k ==> s_final[i] <= s_final[k]) /\ (forall i. k < i < n ==> s_final[k] <= s_final[i])`. This requires strengthening the loop invariant to propagate `partition_ordered` results across iterations.

- [ ] **P0-2: Bridge permutation notions.** Prove `Seq.Properties.permutation int s1 s2 <==> is_permutation s1 s2` (or at least one direction) so that `Correctness.fst`'s `pulse_correctness_hint` can be applied to the Pulse code's output.

- [ ] **P0-3: Wire correctness into quickselect.** After P0-1 and P0-2, add `assert (result == select_spec s0 (SZ.v k))` to quickselect's postcondition, using `pulse_correctness_hint`.

- [ ] **P1-1: Implement CLRS pair-processing SimultaneousMinMax.** Add a second function using the 3⌊n/2⌋-comparison algorithm (process elements in pairs, compare pair first, then compare smaller/larger vs running min/max). Keep the current simple version as a baseline.

- [ ] **P1-2: Rename to deterministic_select** (or rename to `deterministic_select` and document that O(n) expected does not apply). At minimum, fix the misleading comment on line 7.

- [ ] **P2-3: Add ghost tick counter to Pulse quickselect.** Connect the pure `qs_cost` model to the actual implementation to prove the O(n²) worst-case bound operationally.

- [ ] **P2-4: Add ghost tick counter to Pulse `select`.** The `Complexity.fst` model says `k*(n−1)` but the Pulse code has no counter to verify this.

- [ ] **P2-5: Tighten PartialSelectionSort complexity model.** The model uses `n−1` comparisons per round, but the actual code uses `n−i−1` in round `i`. The exact sum is `k*n − k(k+1)/2`, which is strictly better than `k*(n−1)`.

- [ ] **P3-1: Remove dead code.** Delete `kth_order_property` (Quickselect.fst:214–217), `unchanged_outside` (Quickselect.fst:90–95), `partition_preserves_permutation` (Correctness.fst:42–46), and `select_partition_spec` (Correctness.fst:226–227).

- [ ] **P3-2: Fix `complexity_bounded_min` naming.** `find_maximum` reuses the min-named predicate (MinMax.fst:134). Rename to `complexity_bounded` or add `complexity_bounded_max`.

- [ ] **P3-3: Fix stale file reference.** `Quickselect.fst:8` references `Select.fst` → should be `PartialSelectionSort.fst`.

- [ ] **P3-4: Rename Correctness/Spec modules** or at least document that they contain quickselect-related lemmas despite the `PartialSelectionSort` prefix.

- [ ] **P3-6: Reduce `--z3rlimit 200` in PartialSelectionSort.fst:209.** Try breaking the `select` proof into helper lemmas to reduce the required rlimit.

### DEFER

- [ ] **P2-1: Extract shared permutation infrastructure** into `CLRS.Common.Permutation.fst`. Both `Quickselect.fst` and `PartialSelectionSort.fst` copy ~65 lines of identical code.

- [ ] **P2-2: Unify ghost tick infrastructure.** `MinMax.fst` and `SimultaneousMinMax.fst` duplicate `incr_nat`/`tick` using `GhostReference`. Merge with `CLRS.Common.Complexity`'s `tick` (which uses `Reference`), or create a ghost variant in Common.



- [ ] **P3-5: Fix D1 comment accuracy.** Either add randomization or change comment from "O(n) expected" to "O(n²) worst case; O(n) expected requires randomized pivot (not implemented)".


---

## Summary Scorecard

| Dimension | Score | Notes |
|-----------|-------|-------|
| **CLRS Fidelity** | 6/10 | MinMax faithful; SimultaneousMinMax suboptimal; Quickselect lacks randomization; PartialSelectionSort is custom |
| **Specification Strength** | 5/10 | PartialSelectionSort strong; Quickselect has critical gap (doesn't prove k-th smallest) |
| **Complexity Proofs** | 6/10 | Clean pure-F* models but disconnected from Pulse implementations |
| **Code Quality** | 6/10 | Well-organized modules but significant duplication (~130 lines) |
| **Proof Quality** | 8/10 | Zero admits; two permutation notions unbridged; solver sensitivity in SortedPerm |
| **Documentation** | 7/10 | Honest about limitations; some inaccurate claims; stale references |
| **Overall** | 6.3/10 | Solid foundation with meaningful gaps in spec strength and CLRS fidelity |
