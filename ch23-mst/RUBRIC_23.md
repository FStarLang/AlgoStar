# Chapter 23: Minimum Spanning Trees — Rubric Compliance

**Generated**: 2025-07-18 (Updated: 2026-03-04)
**Source**: `/ch23-mst/` — 26 source files

---

## Current File Inventory

| # | File | Lang | Rubric Slot |
|---|------|------|-------------|
| 1 | `CLRS.Ch23.MST.Spec.fsti` | F\* | **Shared Spec interface** — graph, spanning tree, MST, cut, light edge |
| 2 | `CLRS.Ch23.MST.Spec.fst` | F\* | **Shared Spec impl** — cut\_property (Thm 23.1), exchange argument |
| 3 | `CLRS.Ch23.MST.Complexity.fsti` | F\* | **Shared Complexity interface** — kruskal\_cubic, prim\_quadratic |
| 4 | `CLRS.Ch23.MST.Complexity.fst` | F\* | **Shared Complexity** — arithmetic O(V³) Kruskal / O(V²) Prim bounds |
| 5 | `CLRS.Ch23.Kruskal.Spec.fsti` | F\* | **Kruskal Spec interface** — pure\_kruskal, MST theorem signatures |
| 6 | `CLRS.Ch23.Kruskal.Spec.fst` | F\* | **Kruskal Spec** — edge sorting, `pure_kruskal`, `theorem_kruskal_produces_mst` |
| 7 | `CLRS.Ch23.Kruskal.Components.fst` | F\* | **Kruskal Lemmas** — BFS components, forest/acyclicity, reachability |
| 8 | `CLRS.Ch23.Kruskal.EdgeSorting.fst` | F\* | **Kruskal Lemmas** — sort permutation, MST weight independence |
| 9 | `CLRS.Ch23.Kruskal.SortedEdges.fst` | F\* | **Kruskal Lemmas** — kruskal\_spec over sorted input, subset/forest |
| 10 | `CLRS.Ch23.Kruskal.UF.fsti` | F\* | **Kruskal Lemmas** — UF interface: find\_pure, uf\_inv, union/init lemma sigs |
| 11 | `CLRS.Ch23.Kruskal.UF.fst` | F\* | **Kruskal Lemmas** — union-find correctness: `find_pure`, soundness, completeness |
| 12 | `CLRS.Ch23.Kruskal.Helpers.fst` | F\* | **Kruskal Lemmas** — forest-invariant helpers for Pulse proof |
| 13 | `CLRS.Ch23.Kruskal.Lemmas.fsti` | F\* | **Kruskal Lemmas interface** — re-exports from sub-modules |
| 14 | `CLRS.Ch23.Kruskal.Lemmas.fst` | F\* | **Kruskal Lemmas façade** — delegates to sub-modules |
| 15 | `CLRS.Ch23.Kruskal.Impl.fsti` | Pulse | **Kruskal Impl interface** — `kruskal` sig + `kruskal_result_is_mst` + `weighted_edges_subset_graph` |
| 16 | `CLRS.Ch23.Kruskal.Impl.fst` | Pulse | **Kruskal Impl** — imperative Kruskal (adj-matrix, union-find) + MST bridging |
| 17 | `CLRS.Ch23.Kruskal.Complexity.fsti` | Pulse | **Kruskal Complexity interface** — complexity\_bounded\_kruskal (⚠️ disconnected) |
| 18 | `CLRS.Ch23.Kruskal.Complexity.fst` | Pulse | **Kruskal Complexity** — ghost-tick instrumented, proves `ticks ≤ 4·V³` (⚠️ disconnected) |
| 19 | `CLRS.Ch23.Prim.Spec.fsti` | F\* | **Prim Spec interface** — pure\_prim, prim\_spec signatures |
| 20 | `CLRS.Ch23.Prim.Spec.fst` | F\* | **Prim Spec** — `pure_prim`, n−1 edges, connectivity, safety via cut property |
| 21 | `CLRS.Ch23.Prim.Impl.fsti` | Pulse | **Prim Impl interface** — prim fn sig + `prim_result_is_mst` MST bridging theorem |
| 22 | `CLRS.Ch23.Prim.Impl.fst` | Pulse | **Prim Impl** — imperative Prim (adj-matrix, `in_mst` + `key` + `parent` arrays) |
| 23 | `CLRS.Ch23.Prim.Complexity.fsti` | Pulse | **Prim Complexity interface** — complexity\_bounded\_prim (⚠️ disconnected) |
| 24 | `CLRS.Ch23.Prim.Complexity.fst` | Pulse | **Prim Complexity** — ghost-tick instrumented, proves `ticks ≤ 3·V²` (⚠️ disconnected) |
| 25 | `CLRS.Ch23.Kruskal.Bridge.fsti` | F\* | **Kruskal Bridge interface** — `greedy_step_safe`, `safe_spanning_tree_is_mst` |
| 26 | `CLRS.Ch23.Kruskal.Bridge.fst` | F\* | **Kruskal Bridge** — greedy MST correctness via cut property |

---

## Algorithms Covered

### MST Shared Theory (`MST.Spec`)
Provides the common foundation used by both Kruskal and Prim:
- Graph, edge, spanning tree, MST definitions
- **Cut property (Theorem 23.1)** — fully proven via classical exchange argument
- Corollary 23.2 used implicitly by both algorithms' safe-edge proofs

### Kruskal's Algorithm (CLRS §23.2, p. 631)
- **Pure spec** (`Kruskal.Spec`): insertion-sort edges, process in weight order, BFS-component check, `theorem_kruskal_produces_mst`
- **Helper modules** (map to Lemmas slot):
  - `Components` — BFS reachability, forest/acyclicity, same-component
  - `EdgeSorting` — sort produces permutation, sorted output, MST weight independence
  - `SortedEdges` — kruskal over pre-sorted input, subset/forest
  - `UF` — `find_pure`, soundness (`find ≠ ⟹ ¬reachable`), completeness
  - `Helpers` — `uf_inv_union`, `acyclic_snoc_unreachable`, forest-invariant glue
- **Impl** (`Kruskal.Impl.fst`): Pulse, adj-matrix V²-scan with cross-component check + MST proof infrastructure
- **Bridge** (`Kruskal.Bridge`): Greedy MST correctness — `greedy_step_safe` (cut property at each step) + `safe_spanning_tree_is_mst`
- **Complexity** (`Kruskal.Complexity`): ghost-tick proof of `ticks ≤ 4·V³`

### Prim's Algorithm (CLRS §23.2, p. 634)
- **Pure spec** (`Prim.Spec`): adj-matrix, `pure_prim`, n−1 edges, all-connected, subset-of-MST via cut property
- **Impl** (`Prim.Impl.fst`): Pulse, adj-matrix linear-scan extract-min
- **Complexity** (`Prim.Complexity`): ghost-tick proof of `ticks ≤ 3·V²`

---

## Rubric Compliance Matrix

The canonical rubric requires seven file slots per algorithm: **Spec**, **Lemmas**, **Lemmas.fsti**, **Complexity**, **Complexity.fsti**, **Impl**, **Impl.fsti**.

### Shared MST Theory

| Rubric Slot | Expected File | Actual File(s) | Status |
|-------------|---------------|-----------------|--------|
| Spec | `CLRS.Ch23.MST.Spec.fst` | `CLRS.Ch23.MST.Spec.fst` | ✅ Present |
| Spec interface | `CLRS.Ch23.MST.Spec.fsti` | `CLRS.Ch23.MST.Spec.fsti` | ✅ Present |
| Complexity | `CLRS.Ch23.MST.Complexity.fst` | `CLRS.Ch23.MST.Complexity.fst` | ✅ Present |
| Complexity.fsti | `CLRS.Ch23.MST.Complexity.fsti` | `CLRS.Ch23.MST.Complexity.fsti` | ✅ Present |

### Kruskal

| Rubric Slot | Expected File | Actual File(s) | Status |
|-------------|---------------|-----------------|--------|
| Spec | `CLRS.Ch23.Kruskal.Spec.fst` | `CLRS.Ch23.Kruskal.Spec.fst` | ✅ Present |
| Spec.fsti | `CLRS.Ch23.Kruskal.Spec.fsti` | `CLRS.Ch23.Kruskal.Spec.fsti` | ✅ Present |
| Lemmas | `CLRS.Ch23.Kruskal.Lemmas.fst` | `CLRS.Ch23.Kruskal.Lemmas.fst` (façade) + Components, EdgeSorting, SortedEdges, UF, Helpers | ✅ Present |
| Lemmas.fsti | `CLRS.Ch23.Kruskal.Lemmas.fsti` | `CLRS.Ch23.Kruskal.Lemmas.fsti` | ✅ Present |
| Complexity | `CLRS.Ch23.Kruskal.Complexity.fst` | `CLRS.Ch23.Kruskal.Complexity.fst` | ✅ Present |
| Complexity.fsti | `CLRS.Ch23.Kruskal.Complexity.fsti` | `CLRS.Ch23.Kruskal.Complexity.fsti` | ✅ Present |
| Impl | `CLRS.Ch23.Kruskal.Impl.fst` | `CLRS.Ch23.Kruskal.Impl.fst` | ✅ Present |
| Impl.fsti | `CLRS.Ch23.Kruskal.Impl.fsti` | `CLRS.Ch23.Kruskal.Impl.fsti` | ✅ Present — `kruskal` sig + `kruskal_result_is_mst` + `weighted_edges_subset_graph` |

### Prim

| Rubric Slot | Expected File | Actual File(s) | Status |
|-------------|---------------|-----------------|--------|
| Spec | `CLRS.Ch23.Prim.Spec.fst` | `CLRS.Ch23.Prim.Spec.fst` | ✅ Present |
| Spec.fsti | `CLRS.Ch23.Prim.Spec.fsti` | `CLRS.Ch23.Prim.Spec.fsti` | ✅ Present |
| Lemmas | `CLRS.Ch23.Prim.Lemmas.fst` | — (lemmas inline in Prim.Spec.fst) | ❌ Missing |
| Lemmas.fsti | `CLRS.Ch23.Prim.Lemmas.fsti` | — | ❌ Missing |
| Complexity | `CLRS.Ch23.Prim.Complexity.fst` | `CLRS.Ch23.Prim.Complexity.fst` | ✅ Present |
| Complexity.fsti | `CLRS.Ch23.Prim.Complexity.fsti` | `CLRS.Ch23.Prim.Complexity.fsti` | ✅ Present |
| Impl | `CLRS.Ch23.Prim.Impl.fst` | `CLRS.Ch23.Prim.Impl.fst` | ✅ Present |
| Impl.fsti | `CLRS.Ch23.Prim.Impl.fsti` | `CLRS.Ch23.Prim.Impl.fsti` | ✅ Present |

### Summary

| | ✅ Present | ❌ Missing |
|---|:-:|:-:|
| **MST Shared** | 4 | 0 |
| **Kruskal** | 8 | 0 |
| **Prim** | 6 | 2 |
| **Total** | **18** | **2** |

Additional files beyond rubric: `Kruskal.UF.fsti`, `Kruskal.Bridge.fsti/.fst` (sub-module interfaces)

---

## Detailed Action Items

### A. Interface Files (❌ → ✅)

| ID | Action | Priority | Status |
|----|--------|----------|--------|
| A1 | Create `CLRS.Ch23.Kruskal.Spec.fsti` — export `pure_kruskal`, `theorem_kruskal_produces_mst`, `theorem_kruskal_produces_spanning_tree` signatures | Medium | ✅ **DONE** |
| A2 | Create `CLRS.Ch23.Prim.Spec.fsti` — export `pure_prim`, `prim_spec`, `prim_produces_n_minus_1_edges` signatures | Medium | ✅ **DONE** |
| A3 | Create `CLRS.Ch23.Kruskal.Impl.fsti` — public imperative API signature + MST theorem | Medium | ✅ **DONE** — exports `kruskal_result_is_mst`, `weighted_edges_subset_graph`, `adj_graph_valid_edges` |
| A4 | Create `CLRS.Ch23.Prim.Impl.fsti` — public imperative API signature | Medium | ✅ **DONE** |
| A5 | Create `CLRS.Ch23.MST.Complexity.fsti` — export `kruskal_cubic`, `prim_quadratic` | Low | ✅ **DONE** |
| A6 | Create `CLRS.Ch23.Kruskal.Complexity.fsti` — export tick-bound signature | Low | ✅ **DONE** |
| A7 | Create `CLRS.Ch23.Prim.Complexity.fsti` — export tick-bound signature | Low | ✅ **DONE** |

### B. Naming Conformance (🔶 → ✅)

| ID | Action | Priority | Status |
|----|--------|----------|--------|
| B1 | Rename `CLRS.Ch23.Kruskal.fst` → `CLRS.Ch23.Kruskal.Impl.fst` | Low | ✅ **DONE** |
| B2 | Rename `CLRS.Ch23.Prim.fst` → `CLRS.Ch23.Prim.Impl.fst` | Low | ✅ **DONE** |

### C. Lemmas Consolidation (🔶 → ✅)

| ID | Action | Priority | Status |
|----|--------|----------|--------|
| C1 | Create `CLRS.Ch23.Kruskal.Lemmas.fsti` re-exporting key signatures from Components, EdgeSorting, SortedEdges, UF, Helpers | Medium | ✅ **DONE** |
| C2 | Create `CLRS.Ch23.Kruskal.Lemmas.fst` as a façade that opens all five sub-modules | Low | ✅ **DONE** |
| C3 | Factor Prim lemmas out of `Prim.Spec.fst` into `CLRS.Ch23.Prim.Lemmas.fst`/`.fsti` | Medium | ❌ Not yet done |

### D. Proof Gaps (from AUDIT_CH23.md)

| ID | Audit Ref | Action | Priority | Status |
|----|-----------|--------|----------|--------|
| D1 | T2 | Close UF edge-endpoint edge case (was `admit()` at line 360 — verify current status) | High | ✅ No admits found |
| D2 | T3 | Connect Prim Pulse postcondition to `prim_spec` (MST correctness) | High | ⚠️ Bridging lemma stated but **admitted** (`prim_impl_produces_mst`) |
| D3 | T4 | Connect Kruskal Pulse postcondition to `theorem_kruskal_produces_mst` | High | ✅ **DONE** — `kruskal_result_is_mst` in Impl.fsti, `weighted_edges_subset_graph` proved |
| D4 | T5 | Prove MST existence from connectivity (remove assumed precondition) | Medium | ❌ Not yet done |
| D5 | T8 | Add π (parent) array to Prim Impl to materialize MST edges | Medium | ✅ **DONE** (parent array added in earlier commit) |
| D6 | T11 | Reconcile infinity values (Prim Pulse 65535 vs Prim.Spec 10⁹) | Medium | ❌ Not yet done |

### D'. New Tasks

| ID | Action | Priority | Status |
|----|--------|----------|--------|
| D7 | Create `CLRS.Ch23.Kruskal.UF.fsti` — interface for UF sub-module | Medium | ✅ **DONE** |
| D8 | Add disconnection warnings to Kruskal.Complexity and Prim.Complexity | Low | ✅ **DONE** |
| D9 | Prove `prim_impl_produces_mst` (strengthen Prim loop invariant) | High | ❌ Removed (was admitted) |
| D10 | Prove `kruskal_impl_produces_mst` (strengthen Kruskal loop invariant) | High | ✅ **DONE** — `kruskal_result_is_mst` fully proved in Impl via Bridge |
| D11 | Connect Complexity modules to Impl modules | Medium | ❌ Not yet done |

### E. Dead Code / Cleanup

| ID | Action | Priority | Effort |
|----|--------|----------|--------|
| E1 | Remove or give real postconditions to `sorted_input_property`, `greedy_property` in `SortedEdges.fst` | Low | Trivial |
| E2 | Update `README.md` — fix stale line counts, admit counts, file list | Low | ✅ **DONE** |

---

## Kruskal MST Proof Status

### Bug Fix: Inner Scan Component Check ✅
The original inner scan found the global minimum-weight edge **without checking** if endpoints are in different union-find components. This caused each round to re-find the same minimum edge. Fixed by adding `find` calls inside the inner scan with a strengthened invariant:
```
(vbw > 0 ==> find_pure(best_u) ≠ find_pure(best_v))
```

### Proven Infrastructure ✅
- **`edges_adj_pos`**: Opaque predicate tracking that each selected edge `(u,v)` has `adj[u*n+v] > 0`. Maintained through the loop with init/step lemmas. Fully proved.
- **`result_is_forest_adj`**: Strengthened postcondition = `result_is_forest ∧ edges_adj_pos`. Fully proved.
- **`weighted_edges_from_arrays`**: Constructs edges with correct weights from the adjacency matrix. Fully proved.
- **Weight-adj tracking in inner scan**: Invariant `vbw > 0 ==> sadj[vbu*n+vbv] = vbw`. Fully proved.
- **`adj_array_to_graph`**: Converts flat adjacency matrix to graph type. Fully proved.

### What's Proved vs. Not Yet Connected
The pure spec layer proves MST correctness (`theorem_kruskal_produces_mst`). The Pulse implementation proves:
- Result is an acyclic forest
- All edge endpoints are valid
- Each edge comes from a positive adjacency matrix entry

**Bridge module** (`Kruskal.Bridge`): Provides the key mathematical bridge between the greedy V²-scan algorithm and MST correctness:
- `greedy_step_safe`: If forest ⊆ some MST and we add the minimum-weight cross-component edge, the new forest ⊆ some MST. Uses CLRS Theorem 23.1 (cut property) with the component cut.
- `safe_spanning_tree_is_mst`: If a spanning tree is safe (⊆ some MST) with no repeated edges, it IS an MST.

**Remaining for end-to-end**: Integrating the Bridge into the Pulse loop requires:
1. Strengthening the inner scan invariant to track that `best_w` is the minimum cross-component weight (not just any cross-component edge)
2. Adding `safe_edges` (forest ⊆ some MST) to the outer loop invariant
3. At each step, deriving the `greedy_step_safe` preconditions from the scan result
4. Proving the output is a spanning tree (requires graph connectivity assumption)

---

## Quality Checks

### Admits / Assumes

| Check | Result |
|-------|--------|
| `grep -rn 'admit_smt_queries\|admit()\|assume(' *.fst *.fsti` | **0 matches** — no admits, assumes, or cheats |
| Remaining assumed preconditions | `∃ t. is_mst g t` in `Kruskal.Spec` and `Prim.Spec` — existence not derived from connectivity |

### Spec ↔ Impl Connection

| Algorithm | Pure spec proves MST? | Impl postcondition | End-to-end MST proof? |
|-----------|:---------------------:|:------------------:|:---------------------:|
| Kruskal | ✅ `theorem_kruskal_produces_mst` | ✅ Forest + adj-tracking (`result_is_forest_adj`) | ✅ `kruskal_result_is_mst` — uses Bridge; `weighted_edges_subset_graph` proved; `adj_graph_valid_edges` proved |
| Prim | ✅ `prim_spec` | ✅ `prim_correct` (key/parent) | ✅ `prim_result_is_mst` — uses Bridge's `safe_spanning_tree_is_mst` |

### Complexity

| Algorithm | Proven Bound | CLRS Textbook Bound | Match? | Connected to Impl? |
|-----------|-------------|---------------------|--------|:------------------:|
| Kruskal (adj-matrix) | `ticks ≤ 4·V³` | O(E lg V) with sorted edges + UF | ❌ Weaker — matches implemented V²-scan variant, not CLRS | ❌ Disconnected |
| Prim (adj-matrix) | `ticks ≤ 3·V²` | O(V²) with adj-matrix | ✅ Matches | ❌ Disconnected |

### CLRS Fidelity

| Algorithm | Pure Spec | Imperative Impl | Notes |
|-----------|-----------|-----------------|-------|
| Kruskal | ✅ Faithful | ⚠️ V²-scan variant with component check | Each round finds min-weight cross-component edge |
| Prim | ✅ Faithful | ✅ Faithful | Only gap: no π array, keys-only output |

### Overall Rubric Score

- **Slots filled**: 17 / 20 fully compliant → **85% full**
- **Zero admits / assumes / cheats** in all source files
- **Remaining gaps**: Kruskal.Impl.fsti (predicates tightly coupled), Prim.Lemmas.fst/.fsti (content inline in Spec)
- **Top priorities**: (1) Prove end-to-end Impl↔Spec MST connection, (2) Connect Complexity modules to Impl
