# Audit Report — Chapter 16: Greedy Algorithms

**Scope**: Activity Selection (§16.1) and Huffman Coding (§16.3)  
**Directory**: `ch16-greedy/`  
**Date**: 2025-02-26  
**Total LOC**: ~8,405 across 9 source files (+ 1 deleted source with orphan cache)

---

## File Inventory

| File | Lines | `.checked` | Description |
|------|------:|:----------:|-------------|
| `CLRS.Ch16.ActivitySelection.fst` | 197 | ✅ | Pulse implementation of GREEDY-ACTIVITY-SELECTOR |
| `CLRS.Ch16.ActivitySelection.Lemmas.fst` | 162 | ✅ | Loop invariant definitions & lemmas |
| `CLRS.Ch16.ActivitySelection.Spec.fst` | 1,178 | ✅ | Full optimality proof (exchange argument) |
| `CLRS.Ch16.Huffman.fst` | 2,308 | ❌ | Pulse implementation: `huffman_cost` + `huffman_tree` |
| `CLRS.Ch16.Huffman.Spec.fst` | 2,124 | ✅ | Spec-level htree, WPL, swap lemma, greedy choice |
| `CLRS.Ch16.Huffman.Complete.fst` | 1,807 | ✅ | Spec-level Huffman construction + WPL optimality |
| `CLRS.Ch16.Huffman.Optimality.fst` | 353 | ✅ | Bridge: greedy cost ↔ huffman_complete cost |
| `CLRS.Ch16.Huffman.Complexity.fst` | 225 | ✅ | O(n²) complexity proof for sorted-list Huffman |
| `TestHuffman.fst` | 48 | ✅ | Smoke test (CLRS Figure 16.3 frequencies) |

**Note**: An orphan `CLRS.Ch16.ActivitySelection.Complexity.fst.checked` exists in `_cache/` with no corresponding source file. Likely a renamed/deleted module.

---

## 1. CLRS Fidelity

### 1.1 Activity Selection — GREEDY-ACTIVITY-SELECTOR (CLRS p. 421)

**CLRS pseudocode** (iterative form):
```
GREEDY-ACTIVITY-SELECTOR(s, f)
1  n = s.length
2  A = {a₁}
3  k = 1
4  for m = 2 to n
5    if s[m] >= f[k]
6      A = A ∪ {aₘ}
7      k = m
8  return A
```

**Implementation** (`ActivitySelection.fst` lines 69–196):
- Faithful 1-indexed→0-indexed translation: selects activity 0 first, scans from i=1 to n-1.
- Condition `curr_start >= vlast_finish` (line 166) matches CLRS `s[m] >= f[k]`.
- Returns a count **and** writes selected indices into an output array `out` — goes beyond CLRS by tracking the actual selection set.
- Ghost selection sequence `sel_ref` mirrors the output array for proof purposes.
- Ghost tick counter `ctr` proves exactly `n-1` comparisons (one per candidate).

**Compatibility definition**: Uses `s[i] >= f[j]` (non-strict, matching CLRS).  
**Valid activity**: Uses `s[i] < f[i]` (strict, matching CLRS note that activities have positive duration).

**Verdict**: ✅ **Faithful** — the iterative algorithm is a correct direct translation.

### 1.2 Huffman — HUFFMAN(C) (CLRS p. 431)

**CLRS pseudocode**:
```
HUFFMAN(C)
1  n = |C|
2  Q = C
3  for i = 1 to n-1
4    allocate new node z
5    z.left = x = EXTRACT-MIN(Q)
6    z.right = y = EXTRACT-MIN(Q)
7    z.freq = x.freq + y.freq
8    INSERT(Q, z)
9  return EXTRACT-MIN(Q)
```

**Two implementations provided**:

1. **`huffman_cost`** (lines 1218–1304): Computes only the Huffman tree cost (sum of internal node frequencies) without building the tree. Uses a flat working array with sentinel `infinity = 10⁹` for "deleted" entries. Each iteration does two linear-scan min-finds, then merges. This is a cost-only shortcut not in CLRS.

2. **`huffman_tree`** (lines 1981–2307): Full tree construction using `Pulse.Lib.PriorityQueue` as the min-PQ, storing `(frequency, index)` entries. Allocates `hnode` values on the heap via `Box.alloc`. Follows the CLRS loop structure exactly: n iterations to init PQ, then n-1 merge iterations, then final extract-min. Returns a `hnode_ptr` with separation-logic predicate `is_htree` linking it to a spec-level `HSpec.htree`.

3. **`huffman_complete`** (Complete.fst line 437): Pure spec-level construction using a sorted list as PQ (functional, non-imperative). This is the reference against which optimality is proved.

**Verdict**: ✅ **Faithful** — `huffman_tree` maps line-by-line to CLRS. `huffman_cost` is a valid optimization. `huffman_complete` is a functional equivalent.

---

## 2. Specification Strength

### 2.1 Activity Selection — Optimality

The specification proves **full optimality** via a chain of theorems:

| Property | Where | Status |
|----------|-------|--------|
| Greedy choice (CLRS Thm 16.1): any OPT can be modified to include activity 0 | `Spec.fst:188–316` (`lemma_greedy_choice`) | ✅ Proven |
| Optimal substructure: removing activity 0 from OPT gives OPT for subproblem | `Spec.fst:566–588` (`lemma_optimal_substructure`) | ✅ Proven |
| `greedy[i] <= other[i]`: greedy selection dominates any valid selection | `Spec.fst:736–791` (`lemma_greedy_dominates`) | ✅ Proven by induction |
| No valid selection is larger than greedy | `Spec.fst:796–837` (`lemma_greedy_is_maximal`) | ✅ Proven (contradiction via exhaustiveness) |
| Greedy selection has maximum cardinality | `Spec.fst:872–887` (`lemma_greedy_is_optimal`) | ✅ Proven |
| Implementation selection == optimal | `Spec.fst:1052–1075` (`theorem_implementation_optimal`) | ✅ Proven |
| **Postcondition**: `count == max_compatible_count` | `ActivitySelection.fst:114` | ✅ In postcondition |

The optimality proof uses `max_compatible_count` defined via `find_max_compatible` with `StrongExcludedMiddle` for the existential search (line 289). This is a clean ghost-level definition.

**Verdict**: ✅ **Full optimality proven end-to-end.** The Pulse postcondition (line 114) states `SZ.v count == S.max_compatible_count ss sf (SZ.v n)`, meaning the output provably achieves the maximum.

### 2.2 Huffman — Optimal Prefix Code

| Property | Where | Status |
|----------|-------|--------|
| WPL == cost for any tree | `Spec.fst:53–67` (`wpl_equals_cost`) | ✅ Proven |
| Greedy choice (CLRS Lemma 16.2): two min-freq chars can be siblings at max depth | `Spec.fst:1944–1970` (`greedy_choice_theorem`) | ✅ Fully proven (exchange argument) |
| Optimal substructure (CLRS Lemma 16.3): WPL(T) = WPL(T') + f1 + f2 for sibling merge | `Spec.fst:2096–2124` (`optimal_substructure_theorem`) | ✅ Proven |
| Swap reduces WPL (key exchange lemma) | `Spec.fst:618–639` (`swap_reduces_wpl`) | ✅ Proven (disjoint + prefix cases) |
| `huffman_complete` preserves frequency multiset | `Complete.fst:673–693` | ✅ Proven via count-based equality |
| `huffman_complete` is WPL-optimal (`is_wpl_optimal`) | `Complete.fst:1744–1775` (`huffman_complete_optimal`) | ✅ Proven |
| Spec huffman_from_pq WPL ≤ any tree with same multiset | `Complete.fst:1547–1700` (`huffman_from_pq_wpl_le`) | ✅ Proven by induction with exchange |
| Bridge: `huffman_complete` cost == `greedy_cost` | `Optimality.fst:177–232` | ✅ Proven |
| Imperative `huffman_tree` postcondition | `Huffman.fst:1993–1995` | ⚠️ Only `cost >= 0` and `same_frequency_multiset` |

**Key gap**: The imperative `huffman_tree` postcondition (line 1993) ensures `HSpec.cost ft >= 0` and `HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0)` but does **not** assert `is_wpl_optimal`. The optimality is proved for the spec-level `huffman_complete` (sorted-list PQ version in Complete.fst), and the bridge through `Optimality.fst` connects greedy cost computations, but there is no formal link stating that the imperative tree's cost equals `huffman_complete`'s cost. The `huffman_cost` function's postcondition (line 1229–1233) is even weaker: just `result_cost >= 0` and sign properties.

**Verdict**: ⚠️ **Optimality is proven for the spec-level construction but NOT threaded through to the imperative Pulse implementation's postcondition.** The imperative `huffman_tree` ensures multiset preservation (sufficient to invoke `huffman_complete_optimal` externally), but it would be stronger if the postcondition included `is_wpl_optimal` directly.

---

## 3. Complexity Analysis

### 3.1 Activity Selection — O(n) (presorted)

- **Proven**: Exactly `n-1` comparisons via ghost tick counter.
- Postcondition (line 103): `complexity_bounded_linear cf (reveal c0) (SZ.v n)` which expands to `cf - c0 == n - 1`.
- **Matches CLRS**: Θ(n) for presorted input.

**Verdict**: ✅ **Exact complexity proven** (n-1 comparisons, tight).

### 3.2 Huffman — Complexity

Three different complexity profiles exist:

1. **`huffman_cost` (imperative, flat array)**: Each of n-1 iterations does 2×O(n) linear scans + O(1) merge → **O(n²)**. No formal complexity proof in the Pulse code.

2. **`huffman_tree` (imperative, PQ-based)**: Uses `Pulse.Lib.PriorityQueue` (binary heap). Each of n-1 iterations does 2 extract-min + 1 insert → 3×O(lg n) → **O(n lg n)**. No formal complexity proof; the CLRS-expected O(n lg n) depends on the PQ implementation.

3. **`Complexity.fst` (spec-level sorted-list)**: Proves `huffman_ticks l <= square (length l)` (line 107–108), i.e., O(n²) for the sorted-list implementation. This is correct for the sorted-list PQ variant (insert is O(n)) but does not apply to the heap-based imperative version.

**CLRS target**: O(n lg n) with a min-heap.

| Implementation | Actual complexity | Formally proven? |
|----------------|------------------|:----------------:|
| `huffman_cost` (flat array) | O(n²) | ❌ |
| `huffman_tree` (heap PQ) | O(n lg n) | ❌ |
| `huffman_complete` (sorted list) | O(n²) | ✅ |

**Verdict**: ⚠️ The CLRS-targeted O(n lg n) is achieved by `huffman_tree` via the heap-based PQ but **not formally proven**. The complexity proof covers only the sorted-list spec version at O(n²).

---

## 4. Code Quality

### Strengths
- **Clean module decomposition**: Spec/Lemmas/Implementation/Optimality/Complexity layers are well-separated.
- **Ghost infrastructure**: tick counters and ghost selection sequences add proof obligations without runtime overhead.
- **Separation logic**: `is_htree` recursive predicate cleanly relates heap trees to spec trees.
- **Forest ownership pattern**: `forest_own` (list-based separating conjunction) is a sophisticated and clean way to track ownership of multiple heap trees.
- **Output array**: Activity selection writes indices to `out` array, going beyond CLRS's set-based return.
- **Read-only arrays**: Activity selection uses fractional permission `#p` for input arrays.

### Concerns
- **Hardcoded sentinel**: `infinity = 10⁹` (Huffman.fst line 1097) is fragile. If input frequencies sum above ~10⁹, the sentinel collides with valid data. Should be `max_int` or a separate `Option`-based representation.
- **`huffman_cost` postcondition weakness**: Only states `result_cost >= 0`, not that it equals the Huffman tree cost. The correctness of `huffman_cost` relative to `huffman_tree` or `huffman_complete` is unproven.
- **PQ entry type**: `pq_entry = int & SZ.t` loses the `pos` refinement from `HSpec.htree`. The positivity invariant must be manually threaded as `pq_freqs_positive`.
- **File sizes**: `Huffman.fst` (2,308 lines) and `Huffman.Spec.fst` (2,124 lines) are very large for single modules. Consider further decomposition.
- **No `free_htree`**: The `huffman_tree` function allocates heap nodes but provides no deallocation function. Memory can only be reclaimed by unfolding `is_htree` recursively. A `free_htree` function is mentioned in the module header (line 18) but not implemented.
- **z3rlimit escalation**: `huffman_tree` uses `--z3rlimit 200` (line 1980); `pq_idx_unique_extends` uses `--z3rlimit 120`. These are high and may indicate fragile proofs.

**Verdict**: ⚠️ Good architecture but with some engineering gaps (sentinel, missing `free_htree`, weak postconditions on `huffman_cost`).

---

## 5. Proof Quality — Admits & Assumes

### 5.1 Admits

**Zero admits found across all 9 files.** ✅

Searched all files for `admit`, `Admit`, `sorry`, `ADMIT` — no proof holes.

### 5.2 Assumes

**Zero `assume` statements found.** ✅

The only hits for "assume" are in comments (e.g., "CLRS assumes strict inequality" in Lemmas.fst:9) or in proof sketch comments (Complete.fst:704, 722, 723, 824). No executable `assume` or `admit` calls.

### 5.3 Verification Status

| File | `.checked` exists? |
|------|:------------------:|
| `ActivitySelection.fst` | ✅ |
| `ActivitySelection.Lemmas.fst` | ✅ |
| `ActivitySelection.Spec.fst` | ✅ |
| **`Huffman.fst`** | **❌ Missing** |
| `Huffman.Spec.fst` | ✅ |
| `Huffman.Complete.fst` | ✅ |
| `Huffman.Optimality.fst` | ✅ |
| `Huffman.Complexity.fst` | ✅ |
| `TestHuffman.fst` | ✅ |

**Critical finding**: `CLRS.Ch16.Huffman.fst` (the 2,308-line Pulse imperative implementation) has **no `.checked` file**, meaning it has not been verified by the F* type-checker. All spec-level modules verify, but the main imperative code may contain errors. This is the highest-priority issue.

### 5.4 `StrongExcludedMiddle` Usage

`ActivitySelection.Spec.fst` uses `FStar.StrongExcludedMiddle.strong_excluded_middle` (lines 289, 320, 346, 368) in the definition of `find_max_compatible`. This is a ghost-level (GTot) definition used only for specification, which is acceptable — it does not affect executable code.

**Verdict**: ⚠️ **Zero admits/assumes** is excellent, but the **unverified `Huffman.fst`** is a critical gap.

---

## 6. Documentation Accuracy

### README.md
- Covers only Activity Selection, not Huffman.
- States "NO admits. NO assumes." — **accurate** for all source files.
- States "Full optimality proof (showing this equals the maximum independent set) would require additional theorems" — **outdated/inaccurate**: the optimality proof IS complete (`count == max_compatible_count` is in the postcondition, line 114).
- Loop invariant description is accurate.
- Build instructions reference `cd /home/nswamy/workspace/clrs/ch16-greedy` — **incorrect path** (should be `AutoCLRS`).

### Module-level comments
- `ActivitySelection.fst` header (lines 1–22): Claims "Pairwise non-overlapping" and "Optimality: count == max_compatible_count" — **accurate**.
- `Huffman.fst` header (lines 1–21): Claims "NO admits. NO assumes." — **accurate** in source but **unverifiable** since the file doesn't type-check.
- `Huffman.Complete.fst` summary (lines 1793–1799): States "The Spec module has zero admits" — **accurate**. States WPL-optimality "uses greedy choice property from CLRS Lemma 16.2, axiomatized in the Spec module" — **outdated**: `greedy_choice_theorem` is now fully proven (Spec.fst:1944).
- `Huffman.Complexity.fst` summary (lines 196–225): Accurately describes O(n²) bound for sorted-list variant.

**Verdict**: ⚠️ README is incomplete (missing Huffman docs) and has an incorrect build path. Some module comments are outdated regarding the optimality proof status.

---

## 7. Task List

### Critical (P0)

| # | Task | Detail |
|---|------|--------|
| 1 | **Verify `Huffman.fst`** | The 2,308-line Pulse implementation has no `.checked` file. Run verification and fix any errors. This blocks all confidence in the imperative Huffman code. |
| 2 | **Implement `free_htree`** | Module header promises `free_htree` but it's missing. Without it, `huffman_tree` leaks all heap-allocated tree nodes. |

### High (P1)

| # | Task | Detail |
|---|------|--------|
| 3 | **Strengthen `huffman_tree` postcondition** | Add `is_wpl_optimal ft (seq_to_pos_list freq_seq 0)` to the postcondition. The proof ingredients exist (`huffman_complete_optimal` + multiset preservation); they just need to be connected to the imperative code. |
| 4 | **Strengthen `huffman_cost` postcondition** | Currently only states `result_cost >= 0`. Should state equality with `HSpec.cost` of the Huffman tree for the same frequencies. |
| 5 | **Replace hardcoded `infinity`** | `infinity = 10⁹` (Huffman.fst:1097) will cause silent corruption for large frequency sums. Use `max_int` or an `option`-based encoding. |

### Medium (P2)

| # | Task | Detail |
|---|------|--------|
| 6 | **Prove O(n lg n) for `huffman_tree`** | The heap-based PQ achieves CLRS's O(n lg n) but this isn't formally proven. Add ghost tick counting (as done for activity selection). |
| 7 | **Update README** | Add Huffman documentation, fix build path (`AutoCLRS` not `clrs`), and remove the outdated claim that optimality proof is missing. |
| 8 | **Update stale module comments** | `Complete.fst:824` says greedy choice is "axiomatized" — it's now fully proven. `Complete.fst:1797–1799` similarly outdated. |
| 9 | **Clean up orphan cache** | Remove `_cache/CLRS.Ch16.ActivitySelection.Complexity.fst.checked` (no matching source). |

### Low (P3)

| # | Task | Detail |
|---|------|--------|
| 10 | **Reduce z3rlimit** | `huffman_tree` uses `--z3rlimit 200`, `pq_idx_unique_extends` uses 120. Try to bring these below 60 by adding intermediate assertions. |
| 11 | **Split large files** | `Huffman.fst` (2,308 lines) and `Huffman.Spec.fst` (2,124 lines) could be decomposed further for maintainability. |
| 12 | **Add more test cases** | `TestHuffman.fst` covers only one example (CLRS Figure 16.3). Add edge cases: single character, two characters, equal frequencies, large inputs. No test file for Activity Selection. |

---

## Summary Scorecard

| Dimension | Activity Selection | Huffman |
|-----------|:-----------------:|:-------:|
| CLRS Fidelity | ✅ Excellent | ✅ Excellent |
| Specification Strength | ✅ Full optimality | ⚠️ Spec-level optimal; imperative postcondition weak |
| Complexity | ✅ Exact n-1 proven | ⚠️ O(n²) proven for spec; O(n lg n) not proven for imperative |
| Code Quality | ✅ Clean | ⚠️ Missing `free_htree`, hardcoded sentinel |
| Proof Quality | ✅ Zero admits, verified | ⚠️ Zero admits, but **`Huffman.fst` unverified** |
| Documentation | ⚠️ Outdated optimality claim | ⚠️ Missing from README |

**Overall**: Activity Selection is a **model implementation** — fully verified with complete optimality proof, exact complexity, and clean code. Huffman has excellent spec-level proofs but the critical imperative implementation (`Huffman.fst`) is **unverified**, and the optimality guarantee doesn't flow through to the Pulse postcondition. Fixing `Huffman.fst` verification is the top priority.
