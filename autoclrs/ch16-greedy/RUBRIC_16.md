# Chapter 16: Greedy Algorithms — Rubric Compliance

**Directory**: `ch16-greedy/`
**Date**: 2025-07-18 (updated 2025-07-24)
**Based on**: `RUBRIC.md` (canonical), `AUDIT_CH16.md` (prior audit, 2025-02-26)

> **Key changes since audit**:
> - `Huffman.fst` refactored from 2,308 → 521 lines (extracted `Defs`, `PQLemmas`,
>   `ForestLemmas`, `PQForest`). `huffman_tree` postcondition now includes `is_wpl_optimal`.
> - Impl files renamed: `ActivitySelection.fst` → `ActivitySelection.Impl.fst`,
>   `Huffman.fst` → `Huffman.Impl.fst` (per rubric naming convention).
> - Created `.fsti` interfaces for all modules: Impl, Lemmas, Complexity, Optimality.
> - Added `sym:nat` to `htree` Leaf (CLRS §16.3 character labels) + `sym:int` to heap `hnode`.
> - New `Huffman.Codec.fst/.fsti`: verified encode/decode with round-trip proofs on real htree.
> - New `Huffman.Codec.Impl.fst/.fsti`: Pulse imperative decode_step with proof connection to pure Codec.
> - Ghost elim/intro helpers for `is_htree` exposed in `Huffman.Impl.fsti`.
> - All files verified (zero admits, zero assumes).

---

## Current File Inventory

| File | Lines | `.checked` | Rubric Role | Algorithm |
|------|------:|:----------:|-------------|-----------|
| `CLRS.Ch16.ActivitySelection.Impl.fst` | 157 | ✅ | **Impl** (Pulse) | ActivitySelection |
| `CLRS.Ch16.ActivitySelection.Impl.fsti` | 85 | ✅ | **Impl** interface | ActivitySelection |
| `CLRS.Ch16.ActivitySelection.Lemmas.fst` | 256 | ✅ | **Lemmas** | ActivitySelection |
| `CLRS.Ch16.ActivitySelection.Lemmas.fsti` | 96 | ✅ | **Lemmas** interface | ActivitySelection |
| `CLRS.Ch16.ActivitySelection.Spec.fst` | 1,178 | ✅ | **Spec** | ActivitySelection |
| `CLRS.Ch16.ActivitySelection.Complexity.fst` | 11 | ✅ | **Complexity** | ActivitySelection |
| `CLRS.Ch16.ActivitySelection.Complexity.fsti` | 13 | ✅ | **Complexity** interface | ActivitySelection |
| `CLRS.Ch16.Huffman.Impl.fst` | 556 | ✅ | **Impl** (Pulse) | Huffman |
| `CLRS.Ch16.Huffman.Impl.fsti` | 73 | ✅ | **Impl** interface | Huffman |
| `CLRS.Ch16.Huffman.Spec.fst` | 2,124 | ✅ | **Spec** | Huffman |
| `CLRS.Ch16.Huffman.Complete.fst` | 1,807 | ✅ | **Lemmas** (pure algorithm + WPL optimality proof) | Huffman |
| `CLRS.Ch16.Huffman.Optimality.fst` | 353 | ✅ | **Lemmas** (bridge: greedy cost ↔ WPL) | Huffman |
| `CLRS.Ch16.Huffman.Optimality.fsti` | 73 | ✅ | **Lemmas** interface (greedy_cost + key lemmas) | Huffman |
| `CLRS.Ch16.Huffman.Codec.fst` | 240 | ✅ | **Lemmas** (encode/decode round-trip proofs) | Huffman |
| `CLRS.Ch16.Huffman.Codec.fsti` | 65 | ✅ | **Lemmas** interface (encode, decode, round-trips) | Huffman |
| `CLRS.Ch16.Huffman.Codec.Impl.fst` | 108 | ✅ | **Impl** (Pulse decode_step) | Huffman |
| `CLRS.Ch16.Huffman.Codec.Impl.fsti` | 56 | ✅ | **Impl** interface (Pulse decode_step) | Huffman |
| `CLRS.Ch16.Huffman.Complexity.fst` | 223 | ✅ | **Complexity** (O(n²) sorted-list) | Huffman |
| `CLRS.Ch16.Huffman.Complexity.fsti` | 49 | ✅ | **Complexity** interface | Huffman |
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

1. **`huffman_complete`** (Complete.fst) — Pure spec-level construction using sorted list as PQ; WPL-optimality proven via CLRS Lemma 16.2 (greedy exchange argument).
2. **`huffman_tree`** (Impl.fst) — Imperative Pulse implementation using `Pulse.Lib.PriorityQueue` (binary heap); postcondition includes `is_wpl_optimal`.
3. **Optimality bridge** (Optimality.fst) — Proves `cost(huffman_complete freqs) == greedy_cost freqs` and the critical `greedy_cost_implies_optimal` lemma used by the Pulse Impl.
4. **Codec** (Codec.fst) — Pure encode/decode on real `htree` with verified round-trip:
   `decode(encode(msg)) == msg` and `encode(decode(bits)) == bits` (for well-formed trees).
5. **Codec.Impl** (Codec.Impl.fst) — Pulse imperative `decode_step_impl` that walks a heap-allocated tree, preserving `is_htree`, with postcondition connecting to the pure `HCodec.decode_step` spec.

**htree type**: Leaves carry `sym:nat` (CLRS character label) and `freq:pos`. The heap `hnode` has `sym:int` matched by `is_htree`.

**Huffman.Complete** is the correctness cornerstone: it implements the algorithm purely
(no mutation) and proves WPL-optimality (`huffman_complete_optimal`). Optimality.fst
bridges the gap by defining `greedy_cost` and showing cost-equivalence. The Pulse Impl
references `greedy_cost_implies_optimal` to close its postcondition.

**Huffman module dependency chain**:
`Spec` (types, WPL) → `Complete` (pure algorithm + optimality proof) → `Optimality` (greedy cost bridge) → `Impl` (Pulse imperative)

**Huffman module mapping** (fragmented → rubric):

| Rubric Slot | Mapped Modules |
|-------------|----------------|
| `Spec` | `Huffman.Spec.fst` — htree type (Leaf sym:nat freq:pos), WPL, cost, swap lemma, greedy choice theorem |
| `Lemmas` | `Huffman.Complete.fst` (WPL optimality), `Huffman.Optimality.fst/.fsti` (bridge), `Huffman.Codec.fst/.fsti` (encode/decode round-trips), `Huffman.Defs.fst` (shared defs), `Huffman.PQLemmas.fst/.fsti`, `Huffman.ForestLemmas.fst/.fsti`, `Huffman.PQForest.fst/.fsti` |
| `Complexity` | `Huffman.Complexity.fst/.fsti` — O(n²) for sorted-list variant |
| `Impl` | `Huffman.Impl.fst/.fsti` — Pulse imperative `huffman_tree`, `free_htree`, ghost helpers; `Huffman.Codec.Impl.fst/.fsti` — Pulse `decode_step_impl` |

---

## Rubric Compliance Matrix

### Activity Selection

| Rubric File | Required? | Status | Current File | Notes |
|-------------|:---------:|:------:|--------------|-------|
| `AlgoName.Spec.fst` | ✅ | ✅ | `ActivitySelection.Spec.fst` (1,178 L) | Full optimality proof |
| `AlgoName.Lemmas.fst` | ✅ | ✅ | `ActivitySelection.Lemmas.fst` (256 L) | Loop invariant defs & lemmas |
| `AlgoName.Lemmas.fsti` | ✅ | ✅ | `ActivitySelection.Lemmas.fsti` | Interface file with predicate defs + lemma signatures |
| `AlgoName.Complexity.fst` | ✅ | ✅ | `ActivitySelection.Complexity.fst` | Defines `complexity_bounded_linear` |
| `AlgoName.Complexity.fsti` | ✅ | ✅ | `ActivitySelection.Complexity.fsti` | Interface for complexity definition |
| `AlgoName.Impl.fst` | ✅ | ✅ | `ActivitySelection.Impl.fst` (157 L) | Pulse impl, verified |
| `AlgoName.Impl.fsti` | ✅ | ✅ | `ActivitySelection.Impl.fsti` | Named-predicate pre/postcondition |

### Huffman

| Rubric File | Required? | Status | Current File(s) | Notes |
|-------------|:---------:|:------:|-----------------|-------|
| `AlgoName.Spec.fst` | ✅ | ✅ | `Huffman.Spec.fst` (2,124 L) | htree, WPL, cost, greedy choice, optimal substructure |
| `AlgoName.Lemmas.fst` | ✅ | 🔶 | 7 modules (see mapping above) | Correct content, non-standard naming; total ~4,200 L |
| `AlgoName.Lemmas.fsti` | ✅ | 🔶 | `PQLemmas.fsti`, `ForestLemmas.fsti`, `PQForest.fsti`, `Optimality.fsti` | Fragmented across 4 interfaces |
| `AlgoName.Complexity.fst` | ✅ | 🔶 | `Huffman.Complexity.fst` (223 L) | O(n²) for sorted-list only; O(n lg n) for heap-PQ not proven |
| `AlgoName.Complexity.fsti` | ✅ | ✅ | `Huffman.Complexity.fsti` | Interface for complexity definitions and lemmas |
| `AlgoName.Impl.fst` | ✅ | ✅ | `Huffman.Impl.fst` (523 L) | Pulse impl, verified ✅ |
| `AlgoName.Impl.fsti` | ✅ | ✅ | `Huffman.Impl.fsti` | Public Pulse interface for `huffman_tree` and `free_htree` |

### Summary

| Category | Activity Selection | Huffman |
|----------|:-----------------:|:-------:|
| Spec | ✅ | ✅ |
| Lemmas | ✅ (with `.fsti`) | 🔶 Fragmented (7 modules, all with `.fsti`) |
| Complexity | ✅ Separate module | 🔶 Sorted-list only (with `.fsti`) |
| Impl | ✅ `.Impl.fst/.fsti` | ✅ `.Impl.fst/.fsti` |
| Verified (`.checked`) | ✅ All files | ✅ All files |
| Admits / Assumes | ✅ Zero | ✅ Zero |
| Optimality in postcondition | ✅ `count == max_compatible_count` | ✅ `is_wpl_optimal` |
| Encode/Decode round-trip | — | ✅ `encode_decode_roundtrip`, `decode_encode_roundtrip` |
| Pulse Codec | — | ✅ `decode_step_impl` with pure spec connection |

---

## Detailed Action Items

### P0 — Critical

*None remaining.* The prior audit's P0 (`Huffman.fst` unverified) is resolved — all 16 files
now have `.checked` caches, and the `huffman_tree` postcondition includes `is_wpl_optimal`.

### P1 — Rubric Structural Compliance

| # | Task | Detail | Status |
|---|------|--------|--------|
| 1 | **Add `ActivitySelection.Lemmas.fsti`** | Interface file with predicate definitions + lemma signatures. | ✅ Done |
| 2 | **Add `ActivitySelection.Impl.fsti`** | Public Pulse interface for `activity_selection` with full postcondition. | ✅ Done |
| 3 | **Add `Huffman.Impl.fsti`** | Public Pulse interface for `huffman_tree` and `free_htree`. | ✅ Done |
| 4 | **Extract `ActivitySelection.Complexity.fst/.fsti`** | Created separate module with `complexity_bounded_linear`; Impl imports it. | ✅ Done |
| 5 | **Add `Huffman.Complexity.fsti`** | Interface with complexity definitions and lemma signatures. | ✅ Done |
| 6 | **Rename Impl files** | `ActivitySelection.fst` → `.Impl.fst`, `Huffman.fst` → `.Impl.fst` (per rubric naming). | ✅ Done |
| 7 | **Add `Huffman.Optimality.fsti`** | Interface with `greedy_cost` definition and key lemma signatures. | ✅ Done |

### P2 — Proof & Specification Gaps

| # | Task | Detail |
|---|------|--------|
| 6 | **Prove O(n lg n) for `huffman_tree`** | `Complexity.fst` proves O(n²) for the sorted-list spec variant. The heap-based Pulse impl achieves CLRS's O(n lg n) but has no formal proof. Add ghost tick counting. |
| 7 | **Consolidate Huffman Lemmas naming** | The 7 fragmented lemma modules (`Defs`, `PQLemmas`, `ForestLemmas`, `PQForest`, `Complete`, `Optimality`) don't follow the rubric's single `Huffman.Lemmas.fst/.fsti` pattern. Options: (a) create a facade `Huffman.Lemmas.fst/.fsti` re-exporting key signatures, or (b) rename to `Huffman.Lemmas.*.fst` sub-modules. |

### P3 — Documentation & Cleanup

| # | Task | Detail | Status |
|---|------|--------|--------|
| 8 | **Update README.md** | Added Huffman documentation, fixed build path, removed outdated optimality claim. | ✅ Done |
| 9 | **Update stale module comments** | `Complete.fst`: "axiomatized" → "fully proven"; fixed stale build paths in `Complete.fst` and `Complexity.fst`. | ✅ Done |
| 10 | **Add Activity Selection test file** | No `TestActivitySelection.fst` exists. Add a smoke test. | Pending |
| 11 | **Add more Huffman test cases** | `TestHuffman.fst` covers only CLRS Figure 16.3. Add edge cases (1 char, 2 chars, equal freqs). | Pending |
| 12 | **Clean up orphan cache** | `_cache/CLRS.Ch16.ActivitySelection.Complexity.fst.checked` — no longer orphaned (source exists now). | ✅ Resolved |

---

## Quality Checks

### Admits & Assumes

| Check | Result |
|-------|--------|
| `admit` / `Admit` in source | ✅ **Zero** across all 27 files |
| `assume` / `assume_` in source | ✅ **Zero** (only in comments) |
| `sorry` in source | ✅ **Zero** |
| `StrongExcludedMiddle` | 🔶 Used in `ActivitySelection.Spec.fst` for ghost-level `find_max_compatible` — acceptable (GTot only) |

### Verification Status

| Check | Result |
|-------|--------|
| All `.fst` have `.checked` | ✅ 14/14 |
| All `.fsti` have `.checked` | ✅ 12/12 |
| `Huffman.Impl.fst` verified | ✅ **Resolved** (was ❌ in prior audit) |
| Pulse `.Impl.fsti` verified against `.Impl.fst` | ✅ Both `ActivitySelection.Impl` and `Huffman.Impl` |

> **Note**: All Pulse `.fsti` files (`ActivitySelection.Impl.fsti`, `Huffman.Impl.fsti`) have been
> verified against their `.fst` implementations. `ActivitySelection.Impl.fsti` uses named
> predicates (`activity_selection_pre`, `activity_selection_post`) to avoid SMT subtyping
> issues with inline quantifiers in Pulse fn declarations.

### z3rlimit Health

| File | Max rlimit | z3refresh? | Assessment |
|------|:----------:|:----------:|------------|
| `ActivitySelection.Impl.fst` | 40 | No | Clean |
| `ActivitySelection.Spec.fst` | 40 | No | Clean |
| `Huffman.Impl.fst` | 500 | No | **Moderate** — `merge_step_local` (reduced from 800) |
| `Huffman.Spec.fst` | 600 | No | **High** — swap WPL lemma |
| `Huffman.Complete.fst` | 400 | No | Moderate |
| `Huffman.Codec.Impl.fst` | 400 | No | Moderate |
| `Huffman.PQForest.fst` | 800 | Yes (3×) | **Fragile** |
| `Huffman.ForestLemmas.fst` | 200 | No | Acceptable |
| `Huffman.PQLemmas.fst` | 120 | No | Acceptable |
| `Huffman.Optimality.fst` | 80 | No | Clean |
| `Huffman.Defs.fst` | 8 | No | Clean |
| `TestHuffman.fst` | 20 | No | Acceptable |

**Stability concerns**: `PQForest.fst` uses `z3refresh` in 3 places
(lines 211, 444, 751), indicating Z3 non-determinism. These proofs may
fail on different Z3 seeds or versions. The high rlimits (800) in
`PQForest.fst` and `Impl.fst` suggest that better intermediate
assertions or proof restructuring could improve stability.

> Post-refactoring, the prior audit's concern about `--z3rlimit 200` in `Huffman.fst`
> is resolved. The split into smaller modules brought most rlimits to ≤ 50,
> though `PQForest.fst` and `Impl.fst` (merge-step wrapper) remain high.

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
