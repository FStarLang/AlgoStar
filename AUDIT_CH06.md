# Audit Report — Chapter 06: Heapsort

**Files audited:**
- `ch06-heapsort/CLRS.Ch06.Heap.fst` (683 lines)
- `ch06-heapsort/CLRS.Ch06.Heap.Complexity.fst` (515 lines)

**Date:** 2025-07-17

---

## 1. CLRS Fidelity

### Index Convention (0-based vs 1-based)

CLRS uses **1-based** indexing:
- `PARENT(i) = ⌊i/2⌋`, `LEFT(i) = 2i`, `RIGHT(i) = 2i + 1`

The implementation uses **0-based** indexing (lines 37–39):
- `parent_idx(i) = (i - 1) / 2`, `left_idx(i) = 2*i + 1`, `right_idx(i) = 2*i + 2`

This is the standard and correct translation for 0-based arrays. ✅

### MAX-HEAPIFY (lines 322–423)

| Aspect | CLRS | Implementation | Match? |
|--------|------|----------------|--------|
| Structure | Recursive, finds `largest` among {i, left, right}, swaps + recurses | Recursive Pulse `fn rec`, same logic | ✅ |
| Two-child case | Single `largest` variable through two comparisons | Nested if-else: `lv >= rv` then check `lv > cur`, else check `rv > cur` | ✅ Equivalent |
| One-child case | Subsumed by bounds check `l ≤ heap-size` | Explicit separate branch when `right ≥ heap_size` (line 402) | ✅ |
| Base case | `largest = i` → stop | `left ≥ heap_size` → leaf, or child ≤ current → stop | ✅ |
| Swap | `exchange A[i] with A[largest]` | Manual read-write of two elements (lines 369–371) | ✅ |

**Deviation:** The comparison uses `>` (strict) rather than `>=` for parent-vs-child. CLRS uses `A[l] > A[i]` (strict), so this matches. Note: when `lv == cur`, the code does not swap, which matches CLRS behavior where `largest` stays `i`. ✅

**Extra parameter:** `start: Ghost.erased nat` — not in CLRS. This is a proof artifact that tracks the "heaps_from" region. It allows `max_heapify` to prove correctness when called from different starting points (build-heap from `idx`, extract-max from `0`). Acceptable.

### BUILD-MAX-HEAP (lines 596–626, inlined in `heapsort`)

| Aspect | CLRS | Implementation | Match? |
|--------|------|----------------|--------|
| Loop range | `for i = ⌊n/2⌋ downto 1` | `while (!i > 0sz)` starting from `half = n/2`, decrementing | ✅ |
| Body | `MAX-HEAPIFY(A, i)` | `max_heapify a idx n (SZ.v idx)` | ✅ |
| heap-size | Set to `A.length` | `heap_size = n` (passed through) | ✅ |

**Note:** BUILD-MAX-HEAP is not a separate function — it is inlined as Phase 1 of `heapsort`. This is a minor organizational deviation from CLRS which presents it as a standalone procedure, but is functionally equivalent.

### HEAPSORT (lines 574–682)

| Aspect | CLRS | Implementation | Match? |
|--------|------|----------------|--------|
| Phase 1 | `BUILD-MAX-HEAP(A)` | Build-heap while loop (lines 600–626) | ✅ |
| Phase 2 loop | `for i = n downto 2` | `while (!heap_sz > 1sz)` | ✅ |
| Swap | `exchange A[1] with A[i]` | Manual swap of `a[0]` and `a[last]` (lines 655–658) | ✅ |
| Shrink | `heap-size = heap-size - 1` | `new_sz = vsz - 1sz` | ✅ |
| Restore | `MAX-HEAPIFY(A, 1)` | `max_heapify a 0sz new_sz zero` | ✅ |

**Overall CLRS fidelity: High.** All three algorithms faithfully implement CLRS pseudocode with the standard 0-based index adaptation. No algorithmic deviations.

---

## 2. Specification Strength

### Heap Property Definition

The max-heap property is **formally defined** (lines 62–68):

```fstar
let heap_down_at (s:Seq.seq int) (len:nat) (i:nat{i < len /\ len <= Seq.length s}) : prop =
  (left_idx i < len ==> Seq.index s i >= Seq.index s (left_idx i)) /\
  (right_idx i < len ==> Seq.index s i >= Seq.index s (right_idx i))

let is_max_heap (s:Seq.seq int) (len:nat{len <= Seq.length s}) : prop =
  forall (i:nat). i < len ==> heap_down_at s len i
```

This correctly captures: for every node `i`, `s[i] >= s[left(i)]` and `s[i] >= s[right(i)]` when children exist within `heap_size`. ✅

The `almost_heaps_from` predicate (lines 71–74) captures the key invariant for sift-down: all nodes satisfy heap-down except possibly one "bad" node. This is exactly the CLRS invariant for MAX-HEAPIFY.

### Function Specifications

| Function | Postconditions | Rating |
|----------|---------------|--------|
| `max_heapify` | `heaps_from s' heap_size start`, `permutation s s'`, elements outside `[0, heap_size)` unchanged, length preserved | **Strong** |
| `heapsort` | `sorted s`, `permutation s0 s`, length preserved | **Strong** |

**`max_heapify` (lines 342–349):**
- Proves: full heap property restored from `start` onwards ✅
- Proves: result is a permutation of input ✅
- Proves: elements outside heap region are unchanged (critical for heapsort correctness) ✅
- Precondition: `almost_heaps_from` + grandparent condition ✅
- **Rating: Strong** — complete functional correctness

**`heapsort` (lines 587–593):**
- Proves: result is `sorted` ✅
- Proves: result is a `permutation` of the input ✅
- **Rating: Strong** — both key properties (sorting + permutation) are established

### Supporting Specifications

- `sorted` (line 97): standard `∀ i j. i ≤ j → s[i] ≤ s[j]` ✅
- `suffix_sorted` (line 100): sorted from index `k` onwards ✅
- `prefix_le_suffix` (line 104): all prefix elements ≤ all suffix elements ✅
- `permutation` (line 109): delegates to `SeqP.permutation`, marked `opaque_to_smt` for controlled reasoning ✅
- `root_ge_element` (lines 434–444): proves root is maximum in a max-heap — essential for extract-max correctness ✅

### Loop Invariants

**Build-heap loop (lines 602–612):**
- `SZ.v vi ≤ SZ.v half` (counter in range)
- `permutation s0 s_cur` (permutation maintained)
- `heaps_from s_cur n vi` (nodes from `vi` onward satisfy heap property)

This directly mirrors the CLRS loop invariant: "At the start of each iteration, each node `i+1, i+2, ..., n` is the root of a max-heap." ✅

**Extract-max loop (lines 633–647):**
- `is_max_heap s_cur vsz` (prefix is a max-heap)
- `suffix_sorted s_cur vsz` (suffix is sorted)
- `prefix_le_suffix s_cur vsz` (heap elements ≤ sorted elements)
- `permutation s0 s_cur` (permutation maintained)

This matches the CLRS Exercise 6.4-2 loop invariant precisely. ✅

**Overall specification strength: Strong.** Complete functional correctness with sorted + permutation for heapsort, and full heap-property restoration + permutation for max-heapify.

---

## 3. Complexity Results

### Overview

The complexity analysis is in a **separate pure F\* module** (`CLRS.Ch06.Heap.Complexity.fst`). It is a **paper proof** encoded in F\*: it defines cost functions over `nat` and proves bounds using lemmas, but does **not** instrument the Pulse implementation with ghost tick counters.

### Results Proved

| Algorithm | Bound Proved | CLRS Reference | Status |
|-----------|-------------|----------------|--------|
| MAX-HEAPIFY | `max_heapify_ops(h) = 2h` (2 comparisons per level) | O(lg n) — §6.2 | ✅ Definition only; bound implicit from heap height |
| BUILD-MAX-HEAP | `build_heap_ops(n) ≤ 4n` | O(n) — Theorem 6.3 | ✅ `build_heap_ops_linear` (line 287) |
| HEAPSORT | `heapsort_ops(n) ≤ 6n(1 + ⌊log₂ n⌋)` | O(n lg n) — §6.4 | ✅ `heapsort_ops_simplified` (line 322) |
| HEAPSORT | `heapsort_ops(n) ≤ 2n·log₂n + 4n` | Tighter bound | ✅ `heapsort_practical_bound` (line 344) |
| HEAPSORT | `heapsort_ops(n) ≤ 3n·log₂n` for n ≥ 16 | Asymptotic | ✅ `heapsort_asymptotic` (line 364) |
| HEAPSORT | `heapsort_ops(n) < n²` for n ≥ 11 | Beats quadratic | ✅ `heapsort_better_than_quadratic` (line 449) |

### Build-Heap O(n) Proof (CLRS Theorem 6.3)

The proof follows the textbook strategy:
1. Defines `nodes_at_height(n, h) = ⌈n / 2^(h+1)⌉` (line 42) ✅
2. Defines `build_heap_ops` as sum over heights of `nodes_at_height * 2h` (line 46) ✅
3. Decomposes ceiling into floor + correction term (`sum_bound_decomp`, line 209) ✅
4. Bounds floor part via weighted power-of-2 sum identity: `Σ h·2^(H-h) = 2^(H+1) - H - 2` (`weighted_pow2_sum_exact`, line 158) ✅
5. Bounds correction via `h(h+1) ≤ 2·2^h` (`h_sq_bound`, line 248) ✅
6. Combines: `< 2n + 2n = 4n` (`simple_sum_bound`, line 260) ✅

This is a faithful and complete encoding of the CLRS Theorem 6.3 proof.

### Duplicate Analysis

The file has **two parallel analysis tracks**:
1. **Enhanced analysis (lines 16–469):** Uses `build_heap_ops`/`heapsort_ops` with the O(n) build-heap proof
2. **Simple analysis (lines 471–515):** Uses `heapsort_comparisons` with a conservative `2n` bound for build-heap

These overlap significantly — `extract_max_ops` and `extract_max_comparisons` are essentially identical functions. See Code Quality §4 for details.

### Ghost Tick Instrumentation

**Not present.** The complexity module is a standalone mathematical analysis. It does not connect to the Pulse implementation via ghost counters (as done in e.g., `ch25-apsp` and `ch28-matrix-ops`). The cost model is:
- Defined as recursive nat-valued functions over `n`
- Proved to satisfy bounds via lemmas
- **Not linked** to actual operation counts in `max_heapify` or `heapsort`

This means the complexity bounds are proved correct in isolation, but there is no machine-checked proof that the Pulse implementation actually performs ≤ `heapsort_ops(n)` operations.

---

## 4. Code Quality

### Organization

The code is well-organized into logical sections with clear `// ========== ... ==========` headers:
1. Heap index functions
2. Max-heap predicates
3. Core lemmas
4. Sorted/permutation definitions
5. Swap utilities
6. Sift-down lemmas
7. MAX-HEAPIFY
8. Extract-max lemmas
9. Main HEAPSORT

**Positive:**
- Clean separation of concerns
- Snippet markers for documentation extraction
- Good use of `#push-options`/`#pop-options` scoping

### Duplication

**Issue: Duplicate complexity analyses in the Complexity file.**

| Enhanced Version | Simple Version | Difference |
|-----------------|----------------|------------|
| `max_heapify_ops` (line 29) | `max_heapify_comparisons` (line 477) | Identical: `2 * height` vs `2 * log2_floor heap_size` |
| `extract_max_ops` (line 51) | `extract_max_comparisons` (line 481) | Nearly identical recursive structure |
| `heapsort_ops` (line 56) | `heapsort_comparisons` (line 489) | Same structure, different build-heap model |
| `heapsort_ops_simplified` (line 322) | `heapsort_simplified_bound` (line 512) | Same final bound: `2n(1 + log₂ n)` |

The simple analysis section (lines 471–515) could be removed; the enhanced analysis subsumes it with strictly tighter bounds.

### Dead Code

- None detected. All lemmas are either used in proofs or exported as API.

### Naming

| Name | Quality | Notes |
|------|---------|-------|
| `parent_idx`, `left_idx`, `right_idx` | ✅ Good | Clear, matches CLRS PARENT/LEFT/RIGHT |
| `heap_down_at` | ✅ Good | Descriptive of the "sift-down" direction |
| `almost_heaps_from` | ✅ Good | Captures the "all-except-one" invariant |
| `bad_is_child_of_parent` | ⚠️ Acceptable | Parameter name `bad` is informal; `child_of_parent` would be clearer |
| `sift_down_swap_lemma_from` | ✅ Good | Descriptive |
| `perm_preserves_sorted_suffix` | ✅ Good | Self-documenting |

### BUILD-MAX-HEAP Not a Separate Function

BUILD-MAX-HEAP is inlined into `heapsort` rather than being a standalone `fn`. This prevents reuse (e.g., for a priority queue) and deviates from the CLRS modular structure. However, for a heapsort-only module this is acceptable.

---

## 5. Proof Quality

### Admits and Assumes

**Zero admits. Zero assumes.** ✅

The module header (line 16) claims "NO admits. NO assumes." — this is verified: `grep` finds no `admit` or `assume` in either file. The word "assume" appears only in a comment in the Complexity file (line 394) in a proof sketch.

### Z3 Resource Limits

| File | Location (line) | z3rlimit | fuel/ifuel | Scope |
|------|----------------|----------|------------|-------|
| Heap.fst | 169 | 20 | 1/1 | `swap_preserves_heap_down_other` |
| Heap.fst | 185 | 10 | 1/1 | `swap_heap_down_at_parent` |
| Heap.fst | 224 | 10 | 1/1 | `swap_heap_down_at_grandparent` |
| Heap.fst | 255 | 20 | 1/1 | `sift_down_swap_lemma_from` |
| Heap.fst | 320 | 20 | 1/1 | `max_heapify` |
| Heap.fst | 513 | 50 | 2/2 | `perm_preserves_sorted_suffix` |
| Heap.fst | 572 | 50 | 1/1 | `heapsort` |
| Complexity.fst | 168 | 40 | default | `scaled_floor_sum_bound` and nearby |

All limits are **moderate** (max 50). No extreme values. The higher limits (50) are on the main heapsort function and the `perm_preserves_sorted_suffix` lemma, which are the most complex proofs — reasonable.

### Proof Techniques

- **Classical.forall_intro / move_requires**: Used extensively for quantifier instantiation (lines 307, 462, 484, 537, 565–567). Standard and appropriate.
- **reveal_opaque**: Used to control `permutation` opacity (lines 115, 121, 127–129, 154, 522). Good practice for controlling SMT search.
- **Recursive lemmas**: `root_ge_element` (line 434) is a clean inductive proof over parent chains. `weighted_pow2_sum_exact` (line 158) is a clean inductive identity proof.
- **assert_norm**: Used once in Complexity.fst (line 467) for `log2_floor 15 = 3` — appropriate for small concrete computations.

### Proof Robustness

- Fuel/ifuel tightly controlled at 1/1 in most places (prevents proof brittleness)
- One spot uses fuel 2/ifuel 2 (`perm_preserves_sorted_suffix`), which is slightly more fragile but necessary for the nested counting argument
- No `z3seed`, `retry`, or `quake` options — no signs of flaky proofs ✅

---

## 6. Documentation & Comments

### Module-Level Documentation

`CLRS.Ch06.Heap.fst` has a thorough header comment (lines 1–17) that:
- Lists what's implemented (BUILD-MAX-HEAP, extract-max loop) ✅
- States the heap variant (max-heap on int) ✅
- Lists what's proved (sorted + permutation) ✅
- Claims "NO admits. NO assumes." — verified true ✅

`CLRS.Ch06.Heap.Complexity.fst` has a thorough header (lines 3–13) documenting:
- Simple vs. enhanced analysis ✅
- CLRS theorem references (6.3, 6.4) ✅
- Summary of all bounds ✅

### Inline Comments

- Sift-down swap lemmas have case-analysis comments explaining each case (lines 198–202, 235–239) ✅
- `heapsort` has Phase 1/Phase 2 section comments ✅
- Complexity proofs have detailed algebraic derivation comments (lines 326–336, 394–409) ✅
- The `perm_preserves_sorted_suffix` lemma has an extensive proof sketch (lines 524–545) ✅

### Accuracy

- Line 8 says "Pulse.Lib.PriorityQueue (adapted for max-heap on int)" — there is no evidence that this code was adapted from a priority queue library. This is likely an aspirational or historical note. **Minor inaccuracy.**
- All CLRS theorem references are correct (Theorem 6.3, Exercise 6.4-2, etc.)
- Mathematical derivations in comments match the actual proofs

### Missing Documentation

- No documentation explaining the `start` ghost parameter in `max_heapify` — this is a non-obvious design choice that deserves a comment
- No documentation on why `SZ.fits (op_Multiply 2 (Seq.length s) + 2)` is required (overflow prevention for index arithmetic)

---

## 7. Task List

### Priority: High

| # | Task | File | Lines | Notes |
|---|------|------|-------|-------|
| H1 | **Add ghost-tick instrumentation** to connect Pulse implementation with complexity bounds | Heap.fst | — | Currently complexity analysis is disconnected from the implementation. Add ghost counters to `max_heapify` and `heapsort` loops, and prove they match `heapsort_ops`. Follow patterns from `ch25-apsp` or `ch28-matrix-ops`. |
| H2 | **Extract BUILD-MAX-HEAP as a standalone function** | Heap.fst | 596–626 | Enables reuse for priority queue operations (CLRS §6.5). Also improves CLRS fidelity. |

### Priority: Medium

| # | Task | File | Lines | Notes |
|---|------|------|-------|-------|
| M1 | **Remove duplicate simple analysis** in Complexity file | Complexity.fst | 471–515 | `heapsort_comparisons`, `extract_max_comparisons`, `heapsort_simplified_bound` duplicate the enhanced analysis with weaker bounds. Keep only the enhanced version. |
| M2 | **Document the `start` parameter** in `max_heapify` | Heap.fst | 323 | Add a comment explaining why this ghost parameter is needed and how it differs from the CLRS interface. |
| M3 | **Document the `SZ.fits` precondition** | Heap.fst | 329, 585 | Explain that `fits(2*n+2)` prevents overflow when computing `right_idx`. |
| M4 | **Fix inaccurate comment** about Pulse.Lib.PriorityQueue | Heap.fst | 10 | Either remove or clarify the reference to PriorityQueue adaptation. |

### Priority: Low

| # | Task | File | Lines | Notes |
|---|------|------|-------|-------|
| L1 | **Add `n = 0` support to heapsort** | Heap.fst | 584 | Currently requires `SZ.v n > 0`. Empty arrays are trivially sorted. |
| L2 | **Rename `bad` parameter** in `bad_is_child_of_parent` | Heap.fst | 44 | Use a more descriptive name like `child`. |
| L3 | **Consider reducing z3rlimit 50 on `heapsort`** | Heap.fst | 572 | Try if a lower limit (e.g., 30) suffices after splitting the proof. |
| L4 | **Add CLRS section references** as comments on each major definition | Complexity.fst | — | e.g., mark `nodes_at_height` with "CLRS §6.3, Exercise 6.3-3" |

---

## Summary

| Dimension | Rating | Notes |
|-----------|--------|-------|
| CLRS Fidelity | ⭐⭐⭐⭐⭐ | Faithful implementation of all three algorithms |
| Specification Strength | ⭐⭐⭐⭐⭐ | Strong: sorted + permutation + heap property |
| Complexity Results | ⭐⭐⭐⭐ | Complete bounds proved, but not linked to implementation via ghost ticks |
| Code Quality | ⭐⭐⭐⭐ | Well-organized; minor duplication in complexity file |
| Proof Quality | ⭐⭐⭐⭐⭐ | Zero admits, moderate z3rlimits, no flaky proofs |
| Documentation | ⭐⭐⭐⭐ | Good overall; a few inaccuracies and gaps |

**Overall: Excellent.** This is a high-quality verified heapsort implementation with complete functional correctness proofs and thorough complexity analysis. The main gap is the lack of ghost-tick instrumentation to connect the complexity bounds to the actual Pulse code.
