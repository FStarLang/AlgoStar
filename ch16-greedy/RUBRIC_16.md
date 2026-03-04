# Chapter 16: Greedy Algorithms — Rubric Compliance

**Directory**: `ch16-greedy/`
**Date**: 2025-07-18
**Based on**: `RUBRIC.md` (canonical), `AUDIT_CH16.md` (prior audit, 2025-02-26)
**Total LOC**: ~9,985 across 16 source files (9 `.fst` + 3 `.fsti` + support)

> **Key change since audit**: `Huffman.fst` was refactored from 2,308 → 521 lines
> by extracting `Defs.fst`, `PQLemmas.fst/.fsti`, `ForestLemmas.fst/.fsti`, and
> `PQForest.fst/.fsti`. All files (including `Huffman.fst`) now have `.checked`
> caches. The `huffman_tree` postcondition now includes `is_wpl_optimal`.

---

## Current File Inventory

| File | Lines | `.checked` | Rubric Role | Algorithm |
|------|------:|:----------:|-------------|-----------|
| `CLRS.Ch16.ActivitySelection.fst` | 197 | ✅ | **Impl** (Pulse) | ActivitySelection |
| `CLRS.Ch16.ActivitySelection.Lemmas.fst` | 316 | ✅ | **Lemmas** | ActivitySelection |
| `CLRS.Ch16.ActivitySelection.Spec.fst` | 1,178 | ✅ | **Spec** | ActivitySelection |
| `CLRS.Ch16.Huffman.fst` | 521 | ✅ | **Impl** (Pulse) | Huffman |
| `CLRS.Ch16.Huffman.Spec.fst` | 2,124 | ✅ | **Spec** | Huffman |
| `CLRS.Ch16.Huffman.Complete.fst` | 1,807 | ✅ | **Lemmas** (WPL optimality) | Huffman |
| `CLRS.Ch16.Huffman.Optimality.fst` | 353 | ✅ | **Lemmas** (bridge: greedy cost ↔ WPL) | Huffman |
| `CLRS.Ch16.Huffman.Complexity.fst` | 225 | ✅ | **Complexity** (O(n²) sorted-list) | Huffman |
| `CLRS.Ch16.Huffman.Defs.fst` | 475 | ✅ | **Lemmas** (shared defs for Impl) | Huffman |
| `CLRS.Ch16.Huffman.PQLemmas.fst` | 323 | ✅ | **Lemmas** (PQ invariant preservation) | Huffman |
| `CLRS.Ch16.Huffman.PQLemmas.fsti` | 65 | ✅ | **Lemmas** interface | Huffman |
| `CLRS.Ch16.Huffman.ForestLemmas.fst` | 804 | ✅ | **Lemmas** (forest–PQ structural) | Huffman |
| `CLRS.Ch16.Huffman.ForestLemmas.fsti` | 242 | ✅ | **Lemmas** interface | Huffman |
| `CLRS.Ch16.Huffman.PQForest.fst` | 918 | ✅ | **Lemmas** (opaque predicate intro/elim) | Huffman |
| `CLRS.Ch16.Huffman.PQForest.fsti` | 383 | ✅ | **Lemmas** interface | Huffman |
| `TestHuffman.fst` | 54 | ✅ | Test | Huffman |

---

## Algorithms Covered

### Activity Selection (CLRS §16.1 — GREEDY-ACTIVITY-SELECTOR)

Iterative greedy algorithm selecting the maximum-cardinality set of mutually
compatible activities, sorted by finish time. Faithful 1-indexed → 0-indexed
translation of CLRS pseudocode.

- **Spec**: Full optimality proof via greedy choice (Thm 16.1), optimal substructure, dominance, and maximality.
- **Impl**: Pulse implementation with ghost tick counter proving exactly `n−1` comparisons.
- **Postcondition**: `count == max_compatible_count` (end-to-end optimality).

### Huffman Coding (CLRS §16.3 — HUFFMAN)

Builds an optimal prefix-code tree by repeatedly merging the two lowest-frequency
subtrees. The codebase provides:

1. **`huffman_complete`** (Complete.fst) — Pure spec-level construction using sorted list as PQ; WPL-optimality proven.
2. **`huffman_tree`** (Huffman.fst) — Imperative Pulse implementation using `Pulse.Lib.PriorityQueue` (binary heap); postcondition now includes `is_wpl_optimal`.
3. **`huffman_cost`** — Cost-only shortcut (flat array, linear scans); present in the older audit but superseded by the refactored implementation.

**Huffman module mapping** (fragmented → rubric):

| Rubric Slot | Mapped Modules |
|-------------|----------------|
| `Spec` | `Huffman.Spec.fst` — htree type, WPL, cost, swap lemma, greedy choice theorem |
| `Lemmas` | `Huffman.Complete.fst` (WPL optimality), `Huffman.Optimality.fst` (bridge), `Huffman.Defs.fst` (shared defs), `Huffman.PQLemmas.fst/.fsti`, `Huffman.ForestLemmas.fst/.fsti`, `Huffman.PQForest.fst/.fsti` |
| `Complexity` | `Huffman.Complexity.fst` — O(n²) for sorted-list variant |
| `Impl` | `Huffman.fst` — Pulse imperative `huffman_tree` |

---

## Rubric Compliance Matrix

### Activity Selection

| Rubric File | Required? | Status | Current File | Notes |
|-------------|:---------:|:------:|--------------|-------|
| `AlgoName.Spec.fst` | ✅ | ✅ | `ActivitySelection.Spec.fst` (1,178 L) | Full optimality proof |
| `AlgoName.Lemmas.fst` | ✅ | ✅ | `ActivitySelection.Lemmas.fst` (316 L) | Loop invariant defs & lemmas |
| `AlgoName.Lemmas.fsti` | ✅ | ❌ | *Missing* | No interface file for Lemmas |
| `AlgoName.Complexity.fst` | ✅ | 🔶 | *Inline in Impl* | Tick counter in `.fst` proves n−1 comparisons; no separate module |
| `AlgoName.Complexity.fsti` | ✅ | ❌ | *Missing* | No complexity interface |
| `AlgoName.Impl.fst` | ✅ | ✅ | `ActivitySelection.fst` (197 L) | Pulse impl, verified |
| `AlgoName.Impl.fsti` | ✅ | ❌ | *Missing* | No public interface for Impl |

### Huffman

| Rubric File | Required? | Status | Current File(s) | Notes |
|-------------|:---------:|:------:|-----------------|-------|
| `AlgoName.Spec.fst` | ✅ | ✅ | `Huffman.Spec.fst` (2,124 L) | htree, WPL, cost, greedy choice, optimal substructure |
| `AlgoName.Lemmas.fst` | ✅ | 🔶 | 7 modules (see mapping above) | Correct content, non-standard naming; total ~4,200 L |
| `AlgoName.Lemmas.fsti` | ✅ | 🔶 | `PQLemmas.fsti`, `ForestLemmas.fsti`, `PQForest.fsti` | Fragmented across 3 interfaces |
| `AlgoName.Complexity.fst` | ✅ | 🔶 | `Huffman.Complexity.fst` (225 L) | O(n²) for sorted-list only; O(n lg n) for heap-PQ not proven |
| `AlgoName.Complexity.fsti` | ✅ | ❌ | *Missing* | No complexity interface |
| `AlgoName.Impl.fst` | ✅ | ✅ | `Huffman.fst` (521 L) | Pulse impl, now verified ✅ |
| `AlgoName.Impl.fsti` | ✅ | ❌ | *Missing* | No public interface for Impl |

### Summary

| Category | Activity Selection | Huffman |
|----------|:-----------------:|:-------:|
| Spec | ✅ | ✅ |
| Lemmas | ✅ (no `.fsti`) | 🔶 Fragmented (7 modules) |
| Complexity | 🔶 Inline | 🔶 Sorted-list only |
| Impl | ✅ (no `.fsti`) | ✅ (no `.fsti`) |
| Verified (`.checked`) | ✅ All 3 files | ✅ All 13 files |
| Admits / Assumes | ✅ Zero | ✅ Zero |
| Optimality in postcondition | ✅ `count == max_compatible_count` | ✅ `is_wpl_optimal` |

---

## Detailed Action Items

### P0 — Critical

*None remaining.* The prior audit's P0 (`Huffman.fst` unverified) is resolved — all 16 files
now have `.checked` caches, and the `huffman_tree` postcondition includes `is_wpl_optimal`.

### P1 — Rubric Structural Compliance

| # | Task | Detail |
|---|------|--------|
| 1 | **Add `ActivitySelection.Lemmas.fsti`** | Rubric requires an interface file for Lemmas. Extract signatures from `Lemmas.fst`. |
| 2 | **Add `ActivitySelection.Impl.fsti`** | Rubric requires a public interface for the Pulse implementation. Extract `activity_selection` signature. |
| 3 | **Add `Huffman.Impl.fsti`** | Rubric requires a public interface for `huffman_tree`. Extract signature with `is_wpl_optimal` postcondition. |
| 4 | **Extract `ActivitySelection.Complexity.fst/.fsti`** | Complexity proof (tick counter) is inline in Impl. Move to a separate module per rubric. |
| 5 | **Add `Huffman.Complexity.fsti`** | Rubric requires an interface file for the complexity module. |

### P2 — Proof & Specification Gaps

| # | Task | Detail |
|---|------|--------|
| 6 | **Prove O(n lg n) for `huffman_tree`** | `Complexity.fst` proves O(n²) for the sorted-list spec variant. The heap-based Pulse impl achieves CLRS's O(n lg n) but has no formal proof. Add ghost tick counting. |
| 7 | **Consolidate Huffman Lemmas naming** | The 7 fragmented lemma modules (`Defs`, `PQLemmas`, `ForestLemmas`, `PQForest`, `Complete`, `Optimality`) don't follow the rubric's single `Huffman.Lemmas.fst/.fsti` pattern. Options: (a) create a facade `Huffman.Lemmas.fst/.fsti` re-exporting key signatures, or (b) rename to `Huffman.Lemmas.*.fst` sub-modules. |

### P3 — Documentation & Cleanup

| # | Task | Detail |
|---|------|--------|
| 8 | **Update README.md** | Missing Huffman docs; incorrect build path (`clrs` → `AutoCLRS`); outdated claim that optimality proof is missing. |
| 9 | **Update stale module comments** | `Complete.fst` says greedy choice is "axiomatized" — it is now fully proven in `Spec.fst`. |
| 10 | **Add Activity Selection test file** | No `TestActivitySelection.fst` exists. Add a smoke test. |
| 11 | **Add more Huffman test cases** | `TestHuffman.fst` covers only CLRS Figure 16.3. Add edge cases (1 char, 2 chars, equal freqs). |
| 12 | **Clean up orphan cache** | Remove `_cache/CLRS.Ch16.ActivitySelection.Complexity.fst.checked` if it still exists (no matching source). |

---

## Quality Checks

### Admits & Assumes

| Check | Result |
|-------|--------|
| `admit` / `Admit` in source | ✅ **Zero** across all 16 files |
| `assume` in source | ✅ **Zero** (only in comments) |
| `sorry` in source | ✅ **Zero** |
| `StrongExcludedMiddle` | 🔶 Used in `ActivitySelection.Spec.fst` for ghost-level `find_max_compatible` — acceptable (GTot only) |

### Verification Status

| Check | Result |
|-------|--------|
| All `.fst` have `.checked` | ✅ 9/9 |
| All `.fsti` have `.checked` | ✅ 3/3 (PQLemmas, ForestLemmas, PQForest) |
| `Huffman.fst` verified | ✅ **Resolved** (was ❌ in prior audit) |

### z3rlimit Health

| File | Max rlimit | Assessment |
|------|:----------:|------------|
| `ActivitySelection.fst` | — | Clean |
| `Huffman.fst` | 8 | Clean (post-refactor) |
| `Huffman.Defs.fst` | 8 | Clean |
| `Huffman.PQLemmas.fst` | 8 | Clean |
| `Huffman.ForestLemmas.fst` | 8 | Clean |
| `Huffman.PQForest.fst` | 8 | Clean |
| `TestHuffman.fst` | 20 | Acceptable |

> Post-refactoring, the prior audit's concern about `--z3rlimit 200` in `Huffman.fst`
> is resolved. The split into smaller modules brought all rlimits to ≤ 20.

### Postcondition Strength

| Algorithm | Functional Correctness | Optimality | Complexity |
|-----------|:---------------------:|:----------:|:----------:|
| Activity Selection | ✅ `greedy_selection_inv` | ✅ `count == max_compatible_count` | ✅ `complexity_bounded_linear` (n−1) |
| Huffman (`huffman_tree`) | ✅ `same_frequency_multiset` | ✅ `is_wpl_optimal` | ❌ Not in postcondition |

### CLRS Fidelity

| Algorithm | CLRS Section | Pseudocode Match | Verdict |
|-----------|:------------:|:----------------:|---------|
| GREEDY-ACTIVITY-SELECTOR | §16.1 p.421 | Line-by-line (iterative) | ✅ Faithful |
| HUFFMAN | §16.3 p.431 | `huffman_tree`: init PQ → n−1 merges → extract-min | ✅ Faithful |
