# Chapter 24: Single-Source Shortest Paths — Rubric Compliance

**Date:** 2025-07-17 (updated 2026-03-04)
**Scope:** `ch24-sssp/` — 16 `.fst` files + 8 `.fsti` files, ~7 000 lines
**Verification:** All files verify — `make -j4` clean

---

## Current File Inventory

| # | File | Lines | Rubric Role | Algorithm |
|---|------|------:|-------------|-----------|
| 1 | `CLRS.Ch24.ShortestPath.Spec.fst` | 504 | **Spec** (shared) | — (shared by BF & Dijkstra) |
| 2 | `CLRS.Ch24.ShortestPath.Triangle.fst` | 330 | **Lemmas** (shared) | — (shared by BF & Dijkstra) |
| 3 | `CLRS.Ch24.BellmanFord.Spec.fst` | 1 040 | **Spec** | Bellman-Ford |
| 4 | `CLRS.Ch24.BellmanFord.Impl.fst` + `.fsti` | ~880 | **Impl** (fused: impl + complexity) | Bellman-Ford |
| 5 | `CLRS.Ch24.BellmanFord.SpecBridge.fst` | 219 | **Lemmas** (bridge) | Bellman-Ford |
| 6 | `CLRS.Ch24.BellmanFord.TriangleInequality.fst` + `.fsti` | 340 | **Lemmas** (triangle) | Bellman-Ford |
| 7 | `CLRS.Ch24.BellmanFord.Lemmas.fst` + `.fsti` | ~80 | **Lemmas** (re-export) | Bellman-Ford |
| 8 | `CLRS.Ch24.BellmanFord.Complexity.fst` + `.fsti` | 101 | **Complexity** (pure bounds) | Bellman-Ford |
| 9 | `CLRS.Ch24.Dijkstra.fst` | ~870 | **Impl** (core: impl + complexity) | Dijkstra |
| 10 | `CLRS.Ch24.Dijkstra.Impl.fst` + `.fsti` | ~170 | **Impl** (interface + re-export) | Dijkstra |
| 11 | `CLRS.Ch24.Dijkstra.Spec.fst` | ~40 | **Spec** (re-export) | Dijkstra |
| 12 | `CLRS.Ch24.Dijkstra.Correctness.fst` | 539 | **Lemmas** (greedy, Thm 24.6) | Dijkstra |
| 13 | `CLRS.Ch24.Dijkstra.TriangleInequality.fst` + `.fsti` | 891 | **Lemmas** (triangle) | Dijkstra |
| 14 | `CLRS.Ch24.Dijkstra.Lemmas.fst` + `.fsti` | ~80 | **Lemmas** (re-export) | Dijkstra |
| 15 | `CLRS.Ch24.Dijkstra.Complexity.fst` + `.fsti` | ~80 | **Complexity** (re-export) | Dijkstra |

### Removed Files (merged into Impl)

| File | Merged Into |
|------|-------------|
| `CLRS.Ch24.BellmanFord.fst` | `BellmanFord.Impl.fst` |
| `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst` | `BellmanFord.Impl.fst` |
| `CLRS.Ch24.Dijkstra.Complexity.fst` (standalone) | `Dijkstra.fst` (then re-exported via `Dijkstra.Complexity.fst`) |

---

## Algorithms Covered

### Bellman-Ford (CLRS §24.1)

| Component | File(s) | Notes |
|-----------|---------|-------|
| Pure spec (`sp_dist_k`, convergence, neg-cycle detection) | `BellmanFord.Spec.fst` | 1 040 lines; proves Lemma 24.2, Thm 24.4, Cor 24.5 |
| Shared shortest-path oracle (`sp_dist_k`, `sp_dist`) | `ShortestPath.Spec.fst` | Flat-weight formulation; `triangle_ineq_implies_upper_bound` (Cor 24.3) |
| Spec bridge (flat-weights ↔ adj_matrix) | `BellmanFord.SpecBridge.fst` | Mutual induction; zero admits |
| Triangle inequality from relaxation | `BellmanFord.TriangleInequality.fst` + `.fsti` | BF fixpoint ⇒ triangle; tight interface |
| Stabilization / pigeonhole | `ShortestPath.Triangle.fst` | `sp_dist_k_stabilize`, `sp_dist_triangle_ineq` |
| Pulse implementation + complexity | `BellmanFord.Impl.fst` + `.fsti` | Fused: `bellman_ford` + `bellman_ford_complexity` (ghost ticks) |
| Complexity (pure bound) | `BellmanFord.Complexity.fst` + `.fsti` | O(V³) = O(VE) for dense graphs |

### Dijkstra (CLRS §24.3)

| Component | File(s) | Notes |
|-----------|---------|-------|
| Shared shortest-path oracle | `ShortestPath.Spec.fst` | Same as BF |
| Stabilization / pigeonhole | `ShortestPath.Triangle.fst` | Same as BF |
| Greedy-choice property (Thm 24.6) | `Dijkstra.Correctness.fst` | Proof follows CLRS contradiction argument |
| Triangle inequality from relaxation | `Dijkstra.TriangleInequality.fst` + `.fsti` | Processing all vertices ⇒ triangle; tight interface |
| Pulse implementation + complexity | `Dijkstra.fst` → `Dijkstra.Impl.fst/fsti` | `dijkstra` + `dijkstra_complexity` (ghost ticks); Impl re-exports due to Pulse module-rename bug |
| Complexity (re-export) | `Dijkstra.Complexity.fst` + `.fsti` | Re-exports from `Dijkstra.fst`; O(V²) |

---

## Rubric Compliance Matrix

The canonical rubric (from `RUBRIC.md`) requires seven files per algorithm:

| Rubric Slot | Bellman-Ford | Dijkstra | Status |
|-------------|-------------|----------|--------|
| **Spec.fst** — Pure specification | ✅ `BellmanFord.Spec.fst` + shared `ShortestPath.Spec.fst` | ✅ `Dijkstra.Spec.fst` (re-exports shared `ShortestPath.Spec.fst`) | ✅ Both present |
| **Lemmas.fst** — Correctness proofs | ✅ `BellmanFord.Lemmas.fst` (re-exports `SpecBridge` + `TriangleInequality`) | ✅ `Dijkstra.Lemmas.fst` (re-exports `Correctness` + `TriangleInequality`) | ✅ Both present |
| **Lemmas.fsti** — Interface | ✅ `BellmanFord.Lemmas.fsti` | ✅ `Dijkstra.Lemmas.fsti` | ✅ Both present |
| **Complexity.fst** — Complexity proofs | ✅ `Complexity.fst` (pure) + fused in `Impl.fst` (ghost ticks) | ✅ `Dijkstra.Complexity.fst` (re-export from `Dijkstra.fst`) | ✅ Both present |
| **Complexity.fsti** — Interface | ✅ `BellmanFord.Complexity.fsti` | ✅ `Dijkstra.Complexity.fsti` | ✅ Both present |
| **Impl.fst** — Pulse implementation | ✅ `BellmanFord.Impl.fst` (fused: impl + complexity) | ✅ `Dijkstra.Impl.fst` (re-export) + `Dijkstra.fst` (core) | ✅ Both present |
| **Impl.fsti** — Public interface | ✅ `BellmanFord.Impl.fsti` | ✅ `Dijkstra.Impl.fsti` | ✅ Both present |

### Summary Counts

| Status | Count | Description |
|--------|------:|-------------|
| ✅ Full compliance | 14/14 | All rubric slots filled for both algorithms |
| 🔶 Substance present, naming/structure differs | 0/14 | — |
| ❌ Missing | 0/14 | — |

---

## Phase 2 Polish Notes

### BellmanFord.Impl.fst — Fully Fused

The old `BellmanFord.fst` (core implementation) and `BellmanFord.Complexity.Instrumented.fst`
(ghost-tick copy) have been merged into a single `BellmanFord.Impl.fst`. This module now
contains both `fn bellman_ford` (functional correctness) and `fn bellman_ford_complexity`
(with ghost tick counter proving O(V³)). The `.fsti` exposes both.

### Dijkstra.fst — Complexity Integrated (Pulse rename limitation)

The complexity-instrumented `dijkstra_complexity` function and all its helpers (ghost tick,
pure bounds) have been integrated directly into `Dijkstra.fst`. A Pulse elaboration bug
prevents renaming that module to `Dijkstra.Impl`, so `Dijkstra.Impl.fst` re-exports
both `dijkstra` and `dijkstra_complexity` from `Dijkstra.fst`. The bug manifests as an
"Ill-typed term / Assertion failed" at the `extend_tri_after_relax` call (line ~595) when
ANY module name change is made — even adding an `.fsti` for `ShortestPath.Triangle`
triggers it, since the Pulse elaborator's internal term construction depends on the full
module contents visible at elaboration time.

### Tight Interface Files

- `BellmanFord.TriangleInequality.fsti`: Exposes only `no_violations_implies_triangle`,
  `stable_distances_have_triangle`, `bellman_ford_stable_establishes_triangle` + types.
  Hides ~20 internal lemmas.
- `Dijkstra.TriangleInequality.fsti`: Exposes only `dijkstra_establishes_triangle_inequality`,
  `dijkstra_algorithm_establishes_triangle` + types. Hides ~30 internal lemmas.
- `ShortestPath.Triangle.fsti`: **Not created** — adding it breaks Pulse elaboration in
  `Dijkstra.fst` (see above).

### Dijkstra.Correctness — Retained

Contains CLRS Theorem 24.6 (greedy choice invariant). Used by `Dijkstra.Lemmas`. This is
substantive proof content, not superseded by other files.

---

## Quality Checks

### Proof Quality

| Check | Result |
|-------|--------|
| Zero `admit()` across all files | ✅ |
| Zero `assume` across all files | ✅ |
| Zero `ensures true` (trivial postconditions) | ✅ |
| Zero commented-out code | ✅ |
| All files verify (`make -j4` clean) | ✅ |

### CLRS Theorem Coverage

| CLRS Reference | Statement | Proven? |
|----------------|-----------|---------|
| Lemma 24.2 (Path relaxation) | After k rounds, dist ≤ sp\_dist\_k | ✅ `bf_correctness_inductive` |
| Corollary 24.3 (Upper bound) | dist[v] ≤ δ(s,v) | ✅ `triangle_ineq_implies_upper_bound` |
| Theorem 24.4 (BF correctness) | dist[v] = δ(s,v) when no neg cycles | ✅ `bf_convergence` |
| Corollary 24.5 (Neg-cycle detect) | BF returns FALSE ⟺ neg cycle reachable | ✅ `bf_negative_cycle_detection` |
| Theorem 24.6 (Dijkstra greedy) | Greedy choice yields δ(s,u) | ✅ `greedy_choice_invariant` |
| Lemma 24.10 (Triangle ineq) | δ(s,v) ≤ δ(s,u) + w(u,v) | ✅ `sp_dist_triangle_flat` |
| Lemma 24.11 (Upper bound) | Triangle ineq ⇒ upper bound | ✅ `triangle_ineq_implies_upper_bound` |

### Complexity Verification

| Algorithm | Exact Count | Asymptotic | Proven? | Integrated? |
|-----------|-------------|------------|---------|-------------|
| Bellman-Ford | n + n³ ticks | O(V³) ≤ 2n³ | ✅ | ✅ fused in `BellmanFord.Impl.fst` |
| Dijkstra | n + 2n² ticks | O(V²) ≤ 3n² | ✅ | ✅ integrated in `Dijkstra.fst` |

### Documentation

| Check | Result |
|-------|--------|
| All files have module-level doc headers | ✅ |
| README.md covers all files and properties | ✅ |
| Sentinel constraint documented | ✅ |
| SNIPPET markers in Impl files | ✅ |
| No stale comments | ✅ |

### Z3 Resource Limits

| File | Max rlimit | Notes |
|------|-----------|-------|
| BellmanFord.Impl.fst | 80 | Both `bellman_ford` and `bellman_ford_complexity` |
| Dijkstra.fst | 40 | Main `fn dijkstra` (split_queries always) |
| Dijkstra.TriangleInequality.fst | 60 | `find_improving_predecessor` |
| ShortestPath.Triangle.fst | 100 | `chain_B_property` |
| BellmanFord.SpecBridge.fst | 10 | All queries well under limit |

### Overall Assessment

| Dimension | Rating |
|-----------|--------|
| CLRS Fidelity | ★★★★☆ — faithful adj-matrix adaptation; missing predecessor π |
| Specification Strength | ★★★★★ — d[v]=δ(s,v) proven for both algorithms |
| Complexity | ★★★★★ — exact tick counts; asymptotic bounds verified; integrated with implementations |
| Proof Quality | ★★★★★ — zero admits/assumes across all files |
| Documentation | ★★★★★ — comprehensive headers; sentinel documented |
| **Rubric Structural Compliance** | **★★★★★** — all 14/14 rubric slots filled; tight interface files; complexity integrated with implementations |
