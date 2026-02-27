# Audit Report — Chapter 23: Minimum Spanning Trees (Kruskal, Prim)

**Auditor**: Copilot CLI  
**Date**: 2025-07-17  
**Scope**: `/ch23-mst/` — 12 files, 8 773 total lines of F*/Pulse

---

## 0. File Inventory

| # | File | Lines | Language | Role |
|---|------|------:|---------|------|
| 1 | `CLRS.Ch23.MST.Spec.fsti` | 438 | F* | Cut-property interface: graph, spanning tree, MST, cut, light edge, exchange/path lemma sigs |
| 2 | `CLRS.Ch23.MST.Spec.fst` | 1 745 | F* | Full proofs of the above, including cut_property (Thm 23.1) |
| 3 | `CLRS.Ch23.MST.Complexity.fst` | 102 | F* | Arithmetic-only O(V³) Kruskal / O(V²) Prim bounds (adj-matrix) |
| 4 | `CLRS.Ch23.Kruskal.Spec.fst` | 2 951 | F* | Pure Kruskal: BFS components, insertion sort, `pure_kruskal`, `theorem_kruskal_produces_mst` |
| 5 | `CLRS.Ch23.Kruskal.fst` | 325 | Pulse | Imperative Kruskal (adj-matrix, flat arrays, union-find) |
| 6 | `CLRS.Ch23.Kruskal.EdgeSorting.fst` | 339 | F* | sort_edges preserves permutation, MST weight independence |
| 7 | `CLRS.Ch23.Kruskal.SortedEdges.fst` | 142 | F* | Thin wrapper: kruskal_spec over sorted input, subset/forest proven |
| 8 | `CLRS.Ch23.Kruskal.UF.fst` | 389 | F* | Union-find correctness: `find_pure`, soundness, completeness |
| 9 | `CLRS.Ch23.Kruskal.Complexity.fst` | 521 | Pulse | Ghost-tick instrumented Kruskal, proves `ticks ≤ 4·V³` |
| 10 | `CLRS.Ch23.Prim.fst` | 352 | Pulse | Imperative Prim (adj-matrix, `in_mst` + `key` arrays) |
| 11 | `CLRS.Ch23.Prim.Spec.fst` | 1 036 | F* | Pure Prim: adj-matrix, `pure_prim`, n−1 edges, connectivity, safety via cut property, `prim_spec` |
| 12 | `CLRS.Ch23.Prim.Complexity.fst` | 433 | Pulse | Ghost-tick instrumented Prim, proves `ticks ≤ 3·V²` |

---

## 1. CLRS Fidelity

### 1.1 MST-KRUSKAL (CLRS p. 631)

| CLRS Step | AutoCLRS | Fidelity |
|-----------|----------|----------|
| `A ← ∅` | `kruskal_process sorted [] g.n` | ✅ |
| `MAKE-SET(v)` for each v | Imperative: `parent[i] = i` init loop | ✅ |
| Sort edges by weight | `sort_edges` (insertion sort, proven permutation & sorted) | ✅ Correct, though O(E²) sort — CLRS uses comparison sort O(E lg E). Functionally equivalent. |
| `for each (u,v)` in sorted order | `kruskal_process` recursion / imperative double loop | ⚠️ **Imperative version scans V² each round instead of iterating sorted edge list** — see §1.3 |
| `if FIND-SET(u) ≠ FIND-SET(v)` | Pure: `not (same_component_dec forest e.u e.v)` — BFS-based. Imperative: `find` (path-following parent array) | ✅ (pure) / ⚠️ (imperative — no path compression, no union-by-rank) |
| `A ← A ∪ {(u,v)}; UNION(u,v)` | Pure: `e :: forest`. Imperative: write to edge arrays + `do_union` | ✅ |

**Deviation**: The **imperative** Kruskal (`CLRS.Ch23.Kruskal.fst`) does **not** sort edges. It scans the full V×V adjacency matrix each round to find the minimum-weight edge, making it a _Borůvka-like_ variant rather than the edge-list Kruskal from CLRS. The **pure** specification (`Kruskal.Spec.fst`) faithfully implements CLRS's edge-sorted-then-process scheme.

### 1.2 MST-PRIM (CLRS p. 634)

| CLRS Step | AutoCLRS | Fidelity |
|-----------|----------|----------|
| `u.key ← ∞; u.π ← NIL` | `key = V.alloc infinity n` | ✅ |
| `r.key ← 0` | `A.op_Array_Assignment key_a source 0sz` | ✅ |
| `Q ← G.V` | `in_mst` array (0 = in Q, 1 = extracted) | ✅ Equivalent |
| `u ← EXTRACT-MIN(Q)` | Linear scan over `key` array with `in_mst` check | ✅ (adj-matrix variant) |
| `for each v ∈ G.Adj[u]` | Linear scan `v = 0..n-1`, read `weights[u*n+v]` | ✅ |
| `if v ∈ Q and w(u,v) < v.key` / update | Same condition, `A.op_Array_Assignment key_a v new_key_v` | ✅ |

Prim is a very faithful rendering of CLRS's adjacency-matrix variant. `π` (parent) array is **omitted** — only `key` is returned. This means the _actual MST edge set_ is never materialized in the imperative implementation.

### 1.3 Fidelity Verdict

| Algorithm | Pure Spec | Imperative | Overall |
|-----------|-----------|------------|---------|
| Kruskal | ✅ Faithful | ⚠️ V²-scan per round, not edge-sorted | **Good (pure) / Fair (imperative)** |
| Prim | ✅ Faithful | ✅ Faithful | **Excellent** |

---

## 2. Specification Strength

### 2.1 MST Property

| Property | Module | Status |
|----------|--------|--------|
| `is_mst g result` (MST) | `Kruskal.Spec:2714` `theorem_kruskal_produces_mst` | ✅ **Fully proven** — spanning tree + minimum weight |
| `subset result ⊆ some MST` | `Prim.Spec:976` `prim_spec` | ✅ **Proven** (implies min weight) |
| `|result| = n − 1` + connectivity | `Prim.Spec:990–996` | ✅ **Proven** jointly |
| `is_spanning_tree g result` | `Kruskal.Spec:2466` `theorem_kruskal_produces_spanning_tree` | ✅ **Fully proven** (acyclic + connected + n−1 edges + subset) |

### 2.2 Cut Property (Theorem 23.1)

**Fully formalized and proven** in `MST.Spec.fst/fsti`:

```
val cut_property: g → a → e → s → Lemma
  (requires ∃ t. is_mst g t ∧ subset a t)  ∧  is_light_edge e s g  ∧  respects a s
  (ensures  ∃ t'. is_mst g t' ∧ subset (e :: a) t')
```

The proof at line 1655 uses the classical exchange argument: if `e ∉ T`, find a simple path in T between `e.u` and `e.v`, locate a crossing edge `e'` on that path, exchange `e'` for `e`. All supporting lemmas (`exchange_is_spanning_tree`, `lemma_exchange_preserves_mst`, `reachable_simple`, etc.) are proven in the `.fst` file.

### 2.3 Corollary 23.2

Used implicitly: Kruskal's safe-edge proof (`lemma_kruskal_step_safe_edge`, line 1070) defines the cut as the component containing `e.u`, and Prim's safe-edge proof (`lemma_prim_step_preserves_safety`, line 830) defines the cut as tree-vs-non-tree vertices.

### 2.4 Specification Gaps

| Gap | Severity | Notes |
|-----|----------|-------|
| Prim imperative postcondition is `prim_correct` = `source key = 0 ∧ keys bounded` only — does **not** prove MST | **High** | The pure spec proves MST; the Pulse implementation does not connect to it |
| Kruskal imperative postcondition is `result_is_forest` — does **not** prove spanning tree or MST | **High** | Forest + edge count only; no connectivity proof |
| `prim_spec` requires `∃ t. is_mst g t` as precondition | **Medium** | Existence of MST should follow from connectivity; not proven here |
| `theorem_kruskal_produces_mst` requires `∃ mst. is_mst g mst` as precondition | **Medium** | Same issue |

---

## 3. Complexity

### 3.1 Proven Bounds

| Module | Bound Proven | CLRS Bound | Match? |
|--------|-------------|------------|--------|
| `Kruskal.Complexity.fst` | `ticks ≤ 4·V³` | O(E lg V) with sorted edges + UF with union-by-rank | ❌ **Weaker** — see below |
| `Prim.Complexity.fst` | `ticks ≤ 3·V²` | O(V²) with adj-matrix / O(E lg V) with binary heap | ✅ **Matches** adj-matrix variant |
| `MST.Complexity.fst` | Kruskal: O(V³), Prim: O(V²) (arithmetic only) | — | Consistent with above |

### 3.2 Analysis

**Kruskal Complexity**: The 4V³ bound reflects the V²-scan-per-round imperative variant (not the classic edge-sorted O(E lg E) algorithm). Each of V−1 rounds scans V² matrix entries + 2 finds of O(V) each + 1 union. Budget: (V−1)·(V²+2V+1) ≤ 4V³. This is **correct for the implemented algorithm** but is **not** O(E lg V). The CLRS algorithm with sorted edge list + union-find with path compression gives O(E α(V)) ≈ O(E lg V). The pure `Kruskal.Spec` uses insertion sort O(E²) and BFS reachability O(V+E) per step, giving O(E²+E·(V+E)) which is also not the textbook bound.

**Prim Complexity**: The 3V² bound is tight for the adj-matrix Prim. V iterations × (V comparisons for extract-min + V updates for key relaxation) = 2V² work. The factor of 3 accounts for overhead. This matches CLRS's stated O(V²) for adj-matrix Prim. A binary-heap Prim giving O(E lg V) is **not implemented**.

### 3.3 Ghost Tick Mechanism

Both complexity modules use `GhostReference` for an erased tick counter. Ticks are incremented via a `ghost fn tick`. Loop invariants carry tick bounds that accumulate across iterations. The final bound is established when the main loop exits. This is a clean and sound approach — the ghost state does not affect runtime behavior.

---

## 4. Code Quality

### 4.1 Architecture

**Strengths**:
- Clean separation: interface (`.fsti`) / proof (`.fst`) / implementation (Pulse `.fst`)
- MST.Spec provides a reusable theory foundation shared by both algorithms
- Pure specs are separate from imperative implementations
- Edge sorting correctness is modularized in EdgeSorting and SortedEdges

**Weaknesses**:
- `Kruskal.Spec.fst` at 2 951 lines is monolithic — BFS, components, sorting, the main theorem, and many utility lemmas are all in one file
- `stable_permutation` in EdgeSorting (line 133) was simplified to just membership equivalence, losing the stability semantics its name implies
- `SortedEdges.fst` has two vacuous lemmas (`sorted_input_property`, `greedy_property`) with `ensures True` — dead code

### 4.2 Data Structures

| Data Structure | Implementation | Notes |
|----------------|---------------|-------|
| Graph | `{n: nat; edges: list edge}` (pure) / flat `int` array (Pulse) | Two representations; no formal bridging |
| Union-Find | Simple parent array, no path compression, no union-by-rank | Sufficient for O(V³) but not CLRS's O(E α(V)) |
| Priority Queue | Linear scan (Prim) | Correct for adj-matrix variant |
| Edge Sort | Insertion sort (`insert_edge/sort_edges`) | Proven correct; O(E²) not O(E lg E) |

### 4.3 Pulse Coding Patterns

- Unconditional writes with conditional values (e.g., `best_u := (if take_it then vui else vbu_old)`) — good Pulse pattern
- Array ownership tracked via `A.pts_to` with proper ghost state
- `Vec` alloc/free properly paired
- Index arithmetic uses `U64.mul_mod`/`U64.add_mod` with overflow proofs — well done

### 4.4 Infinity Handling

Prim uses `65535sz` as infinity in the imperative code but `1000000000` in the pure spec. This mismatch means the imperative implementation cannot handle graphs with edge weights ≥ 65535, while the pure spec supports weights up to ~10⁹. The bridging function `weights_to_adj_matrix` (Prim.fst:35–48) converts between representations but **no lemma connects the two**.

---

## 5. Proof Quality — Admits and Assumes

### 5.1 Admits

| # | File | Line | Code | Severity | What's Missing |
|---|------|------|------|----------|----------------|
| **A1** | `CLRS.Ch23.Kruskal.UF.fst` | 360 | `admit()` | **Medium** | Edge endpoint validity: handles the case `e.u ≥ n ∨ e.v ≥ n`. The comment says "vacuous in practice" — true if all edges have valid endpoints, but the precondition doesn't enforce this. |
| **A2** | `CLRS.Ch23.Kruskal.fst` | 315 | `assume_ (pure (KSpec.is_forest ...))` | **High** | Assumes the edge set output forms a forest. The comment (line 311) says "TODO: Prove by establishing formal UF component tracking invariant." This is the **critical gap** between the imperative Kruskal and its specification. |

### 5.2 Assumed Preconditions

| # | File | Line | Precondition | Notes |
|---|------|------|-------------|-------|
| **P1** | `Prim.Spec.fst` | 986 | `∃ t. is_mst (adj_to_graph adj n) t` | MST existence assumed, not derived from connectivity |
| **P2** | `Kruskal.Spec.fst` | 2717 | `∃ mst. is_mst g mst` | Same issue |
| **P3** | `Kruskal.Spec.fst` | 2470–2471 | `∀ e. e ∈ g.edges ⟹ e.u ≠ e.v` | No self-loops — reasonable but limits generality |

### 5.3 Proof Statistics

| Module | Lines | Admits | Status |
|--------|------:|------:|--------|
| MST.Spec.fst | 1 745 | 0 | ✅ Fully proven |
| MST.Spec.fsti | 438 | — | Interface only (all vals implemented) |
| Kruskal.Spec.fst | 2 951 | 0 | ✅ Fully proven |
| Kruskal.fst | 325 | 1 `assume_` | ⚠️ Forest property assumed |
| Kruskal.EdgeSorting.fst | 339 | 0 | ✅ |
| Kruskal.SortedEdges.fst | 142 | 0 | ✅ |
| Kruskal.UF.fst | 389 | 1 `admit()` | ⚠️ Edge-endpoint edge case |
| Kruskal.Complexity.fst | 521 | 0 | ✅ |
| Prim.fst | 352 | 0 | ✅ No admits |
| Prim.Spec.fst | 1 036 | 0 | ✅ Fully proven |
| Prim.Complexity.fst | 433 | 0 | ✅ |
| MST.Complexity.fst | 102 | 0 | ✅ |

**Total**: 2 admits across 8 773 lines (0.023% admit rate). The Kruskal `assume_` at line 315 is the most significant.

---

## 6. Documentation Accuracy

### 6.1 README.md

| Claim | Accuracy |
|-------|----------|
| "Fully verified — No admits, no assumes" | ❌ **Incorrect** — Kruskal.fst has an `assume_` (line 315); UF.fst has an `admit()` (line 360). This claim appears to refer to Prim.fst only, but the README covers the whole directory. |
| "Verification time: ~240 seconds" | Unverifiable without running; plausible for Prim.fst alone |
| "Verification Status: Total Lines: 365 / Admits: 6" (for MST.Spec) | ❌ **Stale** — MST.Spec.fst is now 1 745 lines with 0 admits. This reflects an earlier version. |
| Files list mentions only Prim.fst and Makefile | ❌ **Incomplete** — 12 source files exist; README describes only 2 |

### 6.2 Inline Documentation

- Module headers are accurate and helpful
- SNIPPET markers provide clear anchoring points
- Comment at `Kruskal.fst:311` honestly flags the TODO
- `Prim.Spec.fst:1004–1036` summary of proof strategy is excellent

---

## 7. Task List

### Priority 1 (Critical — Soundness)

| ID | Task | File(s) | Effort |
|----|------|---------|--------|
| **T1** | **Close Kruskal `assume_` at line 315**: Prove `is_forest (edges_from_arrays ...)` by connecting the UF component invariant (soundness: different roots ⟹ unreachable; completeness: reachable ⟹ same root) to `acyclic_when_unreachable` from MST.Spec. This requires maintaining a ghost edge-list in the imperative loop and proving that UF-find correctly tracks connected components. | `Kruskal.fst`, `Kruskal.UF.fst` | **Large** (2–4 days) |
| **T2** | **Close UF `admit()` at line 360**: Add precondition `e.u < n ∧ e.v < n` to the enclosing lemma, or prove the `find_pure` identity property for out-of-range vertices. The latter is straightforward: `find_pure` returns `v` when `v ≥ n`. | `Kruskal.UF.fst` | **Small** (1–2 hours) |

### Priority 2 (Specification Gap)

| ID | Task | File(s) | Effort |
|----|------|---------|--------|
| **T3** | **Connect Prim Pulse to pure spec**: Currently `prim_correct` only asserts `source key = 0 ∧ keys bounded`. Add a ghost `tree_edges` accumulator or post-hoc extraction and prove the result matches `pure_prim`, inheriting MST correctness from `prim_spec`. | `Prim.fst`, `Prim.Spec.fst` | **Large** (3–5 days) |
| **T4** | **Connect Kruskal Pulse to pure spec**: Similarly, bridge imperative output to `pure_kruskal` and inherit `theorem_kruskal_produces_mst`. Depends on T1. | `Kruskal.fst`, `Kruskal.Spec.fst` | **Large** (3–5 days) |
| **T5** | **Prove MST existence from connectivity**: Derive `∃ t. is_mst g t` from `all_connected g.n g.edges` to remove the assumed precondition in both `theorem_kruskal_produces_mst` and `prim_spec`. This requires showing that connected graphs have spanning trees and that the weight function has a minimum. | `MST.Spec.fst` | **Medium** (1–2 days) |

### Priority 3 (Fidelity & Performance)

| ID | Task | File(s) | Effort |
|----|------|---------|--------|
| **T6** | **Implement edge-sorted Kruskal in Pulse**: Replace V²-scan-per-round with edge-array-scan (sort edges, iterate once). This would give O(E lg E + E·α(V)) matching CLRS. | New file or refactor `Kruskal.fst` | **Large** |
| **T7** | **Add union-by-rank / path compression to UF**: Current `do_union` just sets `parent[root_u] = root_v`. Adding rank-based union + path compression gives inverse-Ackermann amortized find, matching CLRS §21.3. | `Kruskal.fst`, `Kruskal.UF.fst` | **Medium** |
| **T8** | **Add π (parent) array to Prim Pulse**: Current implementation only returns keys, not the MST edges. Adding parent tracking matches CLRS and enables materializing the MST. | `Prim.fst` | **Small** (half day) |

### Priority 4 (Code Quality)

| ID | Task | File(s) | Effort |
|----|------|---------|--------|
| **T9** | **Fix README**: Update line counts, admit counts, file list; remove the incorrect "No admits" claim. | `README.md` | **Trivial** |
| **T10** | **Remove dead code**: `sorted_input_property` and `greedy_property` in SortedEdges.fst (lines 133–142) have `ensures True` — either give them real postconditions or delete them. | `Kruskal.SortedEdges.fst` | **Trivial** |
| **T11** | **Reconcile infinity values**: Prim Pulse uses 65535, Prim.Spec uses 10⁹. Add a bridging lemma or parameterize. | `Prim.fst`, `Prim.Spec.fst` | **Small** |
| **T12** | **Split Kruskal.Spec.fst**: Factor BFS/component logic, edge sorting, and the main theorem into separate modules. The file is ~3K lines. | `Kruskal.Spec.fst` | **Medium** |

---

## 8. Summary

**What's excellent**:
- The **cut property (Theorem 23.1)** is **fully formalized and proven** — a significant achievement. The exchange argument is carried out in detail across ~1 700 lines of pure F*.
- The **pure Kruskal specification** proves `is_mst g (pure_kruskal g)` end-to-end: forest preservation, edge subset, connectivity via maximal-forest argument, and MST via weight exchange.
- The **pure Prim specification** proves n−1 edges, all-connected, and subset-of-MST via inductive application of the cut property.
- **Complexity proofs** for both algorithms are clean, with ghost-tick counting and tight loop invariants.

**What needs work**:
- The **imperative implementations** have a significant verification gap: neither Kruskal.fst nor Prim.fst connects its postcondition to the pure MST specification. Kruskal has an explicit `assume_`; Prim simply does not assert MST correctness.
- The **Kruskal imperative algorithm** is a V²-scan variant, not the CLRS edge-sorted algorithm.
- **README is stale** and contains inaccurate claims about verification status.

**Overall assessment**: The pure specification layer is **strong** — cut property + two algorithm correctness proofs is a substantial formalization. The imperative layer is **functional but under-specified**, with the key gap being the missing proof that imperative output matches the pure spec. Closing T1–T4 would make this a fully verified MST library.
