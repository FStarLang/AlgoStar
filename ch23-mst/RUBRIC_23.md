# Chapter 23: Minimum Spanning Trees — Rubric Compliance

**Generated**: 2025-07-18
**Source**: `/ch23-mst/` — 14 source files, 9 660 lines of F\*/Pulse

---

## Current File Inventory

| # | File | Lines | Lang | Rubric Slot |
|---|------|------:|------|-------------|
| 1 | `CLRS.Ch23.MST.Spec.fsti` | 458 | F\* | **Shared Spec interface** — graph, spanning tree, MST, cut, light edge, exchange/path lemma sigs |
| 2 | `CLRS.Ch23.MST.Spec.fst` | 2 212 | F\* | **Shared Spec impl** — cut\_property (Thm 23.1), exchange argument, all supporting lemmas |
| 3 | `CLRS.Ch23.MST.Complexity.fst` | 102 | F\* | **Shared Complexity** — arithmetic O(V³) Kruskal / O(V²) Prim bounds |
| 4 | `CLRS.Ch23.Kruskal.Spec.fst` | 2 138 | F\* | **Kruskal Spec** — edge sorting, `pure_kruskal`, `theorem_kruskal_produces_mst` |
| 5 | `CLRS.Ch23.Kruskal.Components.fst` | 836 | F\* | **Kruskal Lemmas** — BFS components, forest/acyclicity, reachability |
| 6 | `CLRS.Ch23.Kruskal.EdgeSorting.fst` | 339 | F\* | **Kruskal Lemmas** — sort permutation, MST weight independence |
| 7 | `CLRS.Ch23.Kruskal.SortedEdges.fst` | 130 | F\* | **Kruskal Lemmas** — kruskal\_spec over sorted input, subset/forest |
| 8 | `CLRS.Ch23.Kruskal.UF.fst` | 350 | F\* | **Kruskal Lemmas** — union-find correctness: `find_pure`, soundness, completeness |
| 9 | `CLRS.Ch23.Kruskal.Helpers.fst` | 118 | F\* | **Kruskal Lemmas** — forest-invariant helpers for Pulse proof |
| 10 | `CLRS.Ch23.Kruskal.fst` | 575 | Pulse | **Kruskal Impl** — imperative Kruskal (adj-matrix, flat arrays, union-find) |
| 11 | `CLRS.Ch23.Kruskal.Complexity.fst` | 526 | Pulse | **Kruskal Complexity** — ghost-tick instrumented, proves `ticks ≤ 4·V³` |
| 12 | `CLRS.Ch23.Prim.Spec.fst` | 1 036 | F\* | **Prim Spec** — `pure_prim`, n−1 edges, connectivity, safety via cut property |
| 13 | `CLRS.Ch23.Prim.fst` | 404 | Pulse | **Prim Impl** — imperative Prim (adj-matrix, `in_mst` + `key` arrays) |
| 14 | `CLRS.Ch23.Prim.Complexity.fst` | 436 | Pulse | **Prim Complexity** — ghost-tick instrumented, proves `ticks ≤ 3·V²` |

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
- **Impl** (`Kruskal.fst`): Pulse, adj-matrix V²-scan variant (not edge-sorted CLRS)
- **Complexity** (`Kruskal.Complexity`): ghost-tick proof of `ticks ≤ 4·V³`

### Prim's Algorithm (CLRS §23.2, p. 634)
- **Pure spec** (`Prim.Spec`): adj-matrix, `pure_prim`, n−1 edges, all-connected, subset-of-MST via cut property
- **Impl** (`Prim.fst`): Pulse, adj-matrix linear-scan extract-min
- **Complexity** (`Prim.Complexity`): ghost-tick proof of `ticks ≤ 3·V²`

---

## Rubric Compliance Matrix

The canonical rubric requires seven file slots per algorithm: **Spec**, **Lemmas**, **Lemmas.fsti**, **Complexity**, **Complexity.fsti**, **Impl**, **Impl.fsti**.

### Shared MST Theory

| Rubric Slot | Expected File | Actual File(s) | Status |
|-------------|---------------|-----------------|--------|
| Spec | `CLRS.Ch23.MST.Spec.fst` | `CLRS.Ch23.MST.Spec.fst` (2 212 lines) | ✅ Present |
| Spec interface | `CLRS.Ch23.MST.Spec.fsti` | `CLRS.Ch23.MST.Spec.fsti` (458 lines) | ✅ Present |
| Complexity | `CLRS.Ch23.MST.Complexity.fst` | `CLRS.Ch23.MST.Complexity.fst` (102 lines) | ✅ Present |
| Complexity.fsti | `CLRS.Ch23.MST.Complexity.fsti` | — | ❌ Missing |

### Kruskal

| Rubric Slot | Expected File | Actual File(s) | Status |
|-------------|---------------|-----------------|--------|
| Spec | `CLRS.Ch23.Kruskal.Spec.fst` | `CLRS.Ch23.Kruskal.Spec.fst` (2 138 lines) | ✅ Present |
| Spec.fsti | `CLRS.Ch23.Kruskal.Spec.fsti` | — | ❌ Missing |
| Lemmas | `CLRS.Ch23.Kruskal.Lemmas.fst` | Split across 5 files: `Components` (836), `EdgeSorting` (339), `SortedEdges` (130), `UF` (350), `Helpers` (118) | 🔶 Content present, naming diverges |
| Lemmas.fsti | `CLRS.Ch23.Kruskal.Lemmas.fsti` | — | ❌ Missing |
| Complexity | `CLRS.Ch23.Kruskal.Complexity.fst` | `CLRS.Ch23.Kruskal.Complexity.fst` (526 lines) | ✅ Present |
| Complexity.fsti | `CLRS.Ch23.Kruskal.Complexity.fsti` | — | ❌ Missing |
| Impl | `CLRS.Ch23.Kruskal.Impl.fst` | `CLRS.Ch23.Kruskal.fst` (575 lines) | 🔶 Present, named `Kruskal.fst` not `Kruskal.Impl.fst` |
| Impl.fsti | `CLRS.Ch23.Kruskal.Impl.fsti` | — | ❌ Missing |

### Prim

| Rubric Slot | Expected File | Actual File(s) | Status |
|-------------|---------------|-----------------|--------|
| Spec | `CLRS.Ch23.Prim.Spec.fst` | `CLRS.Ch23.Prim.Spec.fst` (1 036 lines) | ✅ Present |
| Spec.fsti | `CLRS.Ch23.Prim.Spec.fsti` | — | ❌ Missing |
| Lemmas | `CLRS.Ch23.Prim.Lemmas.fst` | — (lemmas are inline in `Prim.Spec.fst`) | ❌ Missing (content exists, not factored) |
| Lemmas.fsti | `CLRS.Ch23.Prim.Lemmas.fsti` | — | ❌ Missing |
| Complexity | `CLRS.Ch23.Prim.Complexity.fst` | `CLRS.Ch23.Prim.Complexity.fst` (436 lines) | ✅ Present |
| Complexity.fsti | `CLRS.Ch23.Prim.Complexity.fsti` | — | ❌ Missing |
| Impl | `CLRS.Ch23.Prim.Impl.fst` | `CLRS.Ch23.Prim.fst` (404 lines) | 🔶 Present, named `Prim.fst` not `Prim.Impl.fst` |
| Impl.fsti | `CLRS.Ch23.Prim.Impl.fsti` | — | ❌ Missing |

### Summary

| | ✅ Present | 🔶 Partial | ❌ Missing |
|---|:-:|:-:|:-:|
| **MST Shared** | 3 | 0 | 1 |
| **Kruskal** | 2 | 2 | 4 |
| **Prim** | 2 | 1 | 5 |
| **Total** | **7** | **3** | **10** |

---

## Detailed Action Items

### A. Interface Files (❌ → ✅)

| ID | Action | Priority | Effort |
|----|--------|----------|--------|
| A1 | Create `CLRS.Ch23.Kruskal.Spec.fsti` — export `pure_kruskal`, `theorem_kruskal_produces_mst`, `theorem_kruskal_produces_spanning_tree` signatures | Medium | Small |
| A2 | Create `CLRS.Ch23.Prim.Spec.fsti` — export `pure_prim`, `prim_spec`, `prim_produces_n_minus_1_edges` signatures | Medium | Small |
| A3 | Create `CLRS.Ch23.Kruskal.Impl.fsti` — public imperative API signature | Medium | Small |
| A4 | Create `CLRS.Ch23.Prim.Impl.fsti` — public imperative API signature | Medium | Small |
| A5 | Create `CLRS.Ch23.MST.Complexity.fsti` — export `kruskal_cubic`, `prim_quadratic` | Low | Trivial |
| A6 | Create `CLRS.Ch23.Kruskal.Complexity.fsti` — export tick-bound signature | Low | Trivial |
| A7 | Create `CLRS.Ch23.Prim.Complexity.fsti` — export tick-bound signature | Low | Trivial |

### B. Naming Conformance (🔶 → ✅)

| ID | Action | Priority | Effort |
|----|--------|----------|--------|
| B1 | Rename `CLRS.Ch23.Kruskal.fst` → `CLRS.Ch23.Kruskal.Impl.fst` | Low | Trivial (+ update Makefile/.depend) |
| B2 | Rename `CLRS.Ch23.Prim.fst` → `CLRS.Ch23.Prim.Impl.fst` | Low | Trivial (+ update Makefile/.depend) |

### C. Lemmas Consolidation (🔶 → ✅)

| ID | Action | Priority | Effort |
|----|--------|----------|--------|
| C1 | Create `CLRS.Ch23.Kruskal.Lemmas.fsti` re-exporting key signatures from Components, EdgeSorting, SortedEdges, UF, Helpers | Medium | Small |
| C2 | Optionally create `CLRS.Ch23.Kruskal.Lemmas.fst` as a façade that opens all five sub-modules | Low | Small |
| C3 | Factor Prim lemmas out of `Prim.Spec.fst` into `CLRS.Ch23.Prim.Lemmas.fst`/`.fsti` | Medium | Medium |

### D. Proof Gaps (from AUDIT_CH23.md)

| ID | Audit Ref | Action | Priority | Effort |
|----|-----------|--------|----------|--------|
| D1 | T2 | Close UF edge-endpoint edge case (was `admit()` at line 360 — verify current status) | High | Small |
| D2 | T3 | Connect Prim Pulse postcondition to `prim_spec` (MST correctness) | High | Large |
| D3 | T4 | Connect Kruskal Pulse postcondition to `theorem_kruskal_produces_mst` | High | Large |
| D4 | T5 | Prove MST existence from connectivity (remove assumed precondition) | Medium | Medium |
| D5 | T8 | Add π (parent) array to Prim Impl to materialize MST edges | Medium | Small |
| D6 | T11 | Reconcile infinity values (Prim Pulse 65535 vs Prim.Spec 10⁹) | Medium | Small |

### E. Dead Code / Cleanup

| ID | Action | Priority | Effort |
|----|--------|----------|--------|
| E1 | Remove or give real postconditions to `sorted_input_property`, `greedy_property` in `SortedEdges.fst` | Low | Trivial |
| E2 | Update `README.md` — fix stale line counts, admit counts, file list | Low | Trivial |

---

## Quality Checks

### Admits / Assumes

| Check | Result |
|-------|--------|
| `grep -n 'admit\|assume_' *.fst *.fsti` | **0 live admits** — all previously reported admits (Kruskal.fst:315, UF.fst:360) appear resolved |
| Remaining assumed preconditions | `∃ t. is_mst g t` in `Kruskal.Spec` and `Prim.Spec` — existence not derived from connectivity |

### Spec ↔ Impl Connection

| Algorithm | Pure spec proves MST? | Impl postcondition proves MST? | Gap? |
|-----------|:---------------------:|:------------------------------:|:----:|
| Kruskal | ✅ `theorem_kruskal_produces_mst` | ❌ Postcondition: forest + edge count + valid endpoints | **Yes** |
| Prim | ✅ `prim_spec` | ❌ Postcondition: `source key = 0 ∧ keys bounded` | **Yes** |

### Complexity

| Algorithm | Proven Bound | CLRS Textbook Bound | Match? |
|-----------|-------------|---------------------|--------|
| Kruskal (adj-matrix) | `ticks ≤ 4·V³` | O(E lg V) with sorted edges + UF | ❌ Weaker — matches implemented V²-scan variant, not CLRS |
| Prim (adj-matrix) | `ticks ≤ 3·V²` | O(V²) with adj-matrix | ✅ Matches |

### CLRS Fidelity

| Algorithm | Pure Spec | Imperative Impl | Notes |
|-----------|-----------|-----------------|-------|
| Kruskal | ✅ Faithful | ⚠️ V²-scan variant, not edge-sorted | Imperative is Borůvka-like; pure follows CLRS |
| Prim | ✅ Faithful | ✅ Faithful | Only gap: no π array, keys-only output |

### Overall Rubric Score

- **Slots filled**: 7 / 20 fully compliant, 3 partial → **35% full, 50% with partials**
- **Proof quality**: Strong pure layer; imperative layer under-specified
- **Top priorities**: (D2) Prim Impl↔Spec bridge, (D3) Kruskal Impl↔Spec bridge, (A1–A4) interface files
