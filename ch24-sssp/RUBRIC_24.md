# Chapter 24: Single-Source Shortest Paths — Rubric Compliance

**Date:** 2025-07-17
**Scope:** `ch24-sssp/` — 12 `.fst` files, ~5 900 lines
**Verification:** All 12 `.fst.checked` files present — **all files verify**

---

## Current File Inventory

| # | File | Lines | Rubric Role | Algorithm |
|---|------|------:|-------------|-----------|
| 1 | `CLRS.Ch24.ShortestPath.Spec.fst` | 504 | **Spec** (shared) | — (shared by BF & Dijkstra) |
| 2 | `CLRS.Ch24.ShortestPath.Triangle.fst` | 330 | **Lemmas** (shared) | — (shared by BF & Dijkstra) |
| 3 | `CLRS.Ch24.BellmanFord.Spec.fst` | 1 040 | **Spec** | Bellman-Ford |
| 4 | `CLRS.Ch24.BellmanFord.fst` | 540 | **Impl** | Bellman-Ford |
| 5 | `CLRS.Ch24.BellmanFord.SpecBridge.fst` | 219 | **Lemmas** | Bellman-Ford |
| 6 | `CLRS.Ch24.BellmanFord.TriangleInequality.fst` | 339 | **Lemmas** | Bellman-Ford |
| 7 | `CLRS.Ch24.BellmanFord.Complexity.fst` | 101 | **Complexity** | Bellman-Ford |
| 8 | `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst` | 459 | **Complexity** (variant) | Bellman-Ford |
| 9 | `CLRS.Ch24.Dijkstra.fst` | 587 | **Impl** | Dijkstra |
| 10 | `CLRS.Ch24.Dijkstra.Correctness.fst` | 539 | **Lemmas** | Dijkstra |
| 11 | `CLRS.Ch24.Dijkstra.Complexity.fst` | 372 | **Complexity** | Dijkstra |
| 12 | `CLRS.Ch24.Dijkstra.TriangleInequality.fst` | 891 | **Lemmas** | Dijkstra |

---

## Algorithms Covered

### Bellman-Ford (CLRS §24.1)

| Component | File(s) | Notes |
|-----------|---------|-------|
| Pure spec (`sp_dist_k`, convergence, neg-cycle detection) | `BellmanFord.Spec.fst` | 1 040 lines; proves Lemma 24.2, Thm 24.4, Cor 24.5 |
| Shared shortest-path oracle (`sp_dist_k`, `sp_dist`) | `ShortestPath.Spec.fst` | Flat-weight formulation; `triangle_ineq_implies_upper_bound` (Cor 24.3) |
| Spec bridge (flat-weights ↔ adj_matrix) | `BellmanFord.SpecBridge.fst` | Mutual induction; zero admits |
| Triangle inequality from relaxation | `BellmanFord.TriangleInequality.fst` | BF fixpoint ⇒ triangle |
| Stabilization / pigeonhole | `ShortestPath.Triangle.fst` | `sp_dist_k_stabilize`, `sp_dist_triangle_ineq` |
| Pulse implementation | `BellmanFord.fst` | Adj-matrix; sentinel 1000000 |
| Complexity (pure bound) | `BellmanFord.Complexity.fst` | O(V³) = O(VE) for dense graphs |
| Complexity (ghost-tick instrumented) | `BellmanFord.Complexity.Instrumented.fst` | Exact count: n + n³ ticks |

### Dijkstra (CLRS §24.3)

| Component | File(s) | Notes |
|-----------|---------|-------|
| Shared shortest-path oracle | `ShortestPath.Spec.fst` | Same as BF |
| Stabilization / pigeonhole | `ShortestPath.Triangle.fst` | Same as BF |
| Greedy-choice property (Thm 24.6) | `Dijkstra.Correctness.fst` | Proof sketch follows CLRS contradiction argument |
| Triangle inequality from relaxation | `Dijkstra.TriangleInequality.fst` | Processing all vertices ⇒ triangle |
| Pulse implementation | `Dijkstra.fst` | Array-based EXTRACT-MIN; requires non-negative weights |
| Complexity (ghost-tick instrumented) | `Dijkstra.Complexity.fst` | Exact count: n + 2n²; O(V²) |

---

## Rubric Compliance Matrix

The canonical rubric (from `RUBRIC.md`) requires seven files per algorithm:

| Rubric Slot | Bellman-Ford | Dijkstra | Status |
|-------------|-------------|----------|--------|
| **Spec.fst** — Pure specification | ✅ `BellmanFord.Spec.fst` + shared `ShortestPath.Spec.fst` | 🔶 Uses shared `ShortestPath.Spec.fst` only; no `Dijkstra.Spec.fst` | BF ✅ / Dij 🔶 |
| **Lemmas.fst** — Correctness proofs | 🔶 Split across `SpecBridge.fst` + `TriangleInequality.fst` (not named `Lemmas`) | 🔶 Split across `Correctness.fst` + `TriangleInequality.fst` (not named `Lemmas`) | 🔶 Substance present, naming differs |
| **Lemmas.fsti** — Interface | ❌ Missing | ❌ Missing | ❌ Both missing |
| **Complexity.fst** — Complexity proofs | ✅ `Complexity.fst` + `Complexity.Instrumented.fst` | ✅ `Dijkstra.Complexity.fst` | ✅ Both present |
| **Complexity.fsti** — Interface | ❌ Missing | ❌ Missing | ❌ Both missing |
| **Impl.fst** — Pulse implementation | 🔶 `BellmanFord.fst` (not named `Impl`) | 🔶 `Dijkstra.fst` (not named `Impl`) | 🔶 Substance present, naming differs |
| **Impl.fsti** — Public interface | ❌ Missing | ❌ Missing | ❌ Both missing |

### Summary Counts

| Status | Count | Description |
|--------|------:|-------------|
| ✅ Full compliance | 3/14 | Spec (BF), Complexity (BF), Complexity (Dij) |
| 🔶 Substance present, naming/structure differs | 5/14 | Spec (Dij), Lemmas (BF), Lemmas (Dij), Impl (BF), Impl (Dij) |
| ❌ Missing | 6/14 | Lemmas.fsti ×2, Complexity.fsti ×2, Impl.fsti ×2 |

---

## Detailed Action Items

### Priority 1 — Structural Compliance (naming)

| # | Action | Current | Target | Effort |
|---|--------|---------|--------|--------|
| 1.1 | **Rename BellmanFord.fst → BellmanFord.Impl.fst** | `CLRS.Ch24.BellmanFord.fst` | `CLRS.Ch24.BellmanFord.Impl.fst` | Low — rename + update imports in `Complexity.Instrumented.fst` |
| 1.2 | **Rename Dijkstra.fst → Dijkstra.Impl.fst** | `CLRS.Ch24.Dijkstra.fst` | `CLRS.Ch24.Dijkstra.Impl.fst` | Low — rename + update imports |
| 1.3 | **Consolidate BF lemmas into BellmanFord.Lemmas.fst** | `SpecBridge.fst` + `TriangleInequality.fst` | Single `BellmanFord.Lemmas.fst` or keep split with a top-level re-export | Medium — may need to merge or create re-export module |
| 1.4 | **Consolidate Dijkstra lemmas into Dijkstra.Lemmas.fst** | `Correctness.fst` + `TriangleInequality.fst` | Single `Dijkstra.Lemmas.fst` or keep split with re-export | Medium |
| 1.5 | **Create Dijkstra.Spec.fst** (or document that `ShortestPath.Spec.fst` serves as shared spec) | No Dijkstra-specific spec | Either new file or explicit documentation that shared spec suffices | Low–Medium |

### Priority 2 — Missing Interface Files

| # | Action | Notes |
|---|--------|-------|
| 2.1 | **Create BellmanFord.Lemmas.fsti** | Expose `bf_convergence`, `bf_sp_equality`, `bf_negative_cycle_detection`, `stable_distances_have_triangle`, `sp_dist_k_equiv` |
| 2.2 | **Create Dijkstra.Lemmas.fsti** | Expose `greedy_choice_invariant`, `dijkstra_algorithm_establishes_triangle` |
| 2.3 | **Create BellmanFord.Complexity.fsti** | Expose `bellman_ford_cubic`, `bellman_ford_complexity_bounded` |
| 2.4 | **Create Dijkstra.Complexity.fsti** | Expose `dijkstra_quadratic_bound`, `dijkstra_complexity_bounded` |
| 2.5 | **Create BellmanFord.Impl.fsti** | Public signature for `bellman_ford` |
| 2.6 | **Create Dijkstra.Impl.fsti** | Public signature for `dijkstra` |

### Priority 3 — Feature Gaps (from Audit)

| # | Action | Status |
|---|--------|--------|
| 3.1 | Add predecessor (π) tracking to both implementations | ⏳ Deferred — requires new Pulse implementation |
| 3.2 | Add adjacency-list variants (O(VE) BF, O((V+E) lg V) Dijkstra) | ⏳ Deferred |

---

## Quality Checks

### Proof Quality

| Check | Result |
|-------|--------|
| Zero `admit()` across all 12 files | ✅ |
| Zero `assume` across all 12 files | ✅ |
| Zero `ensures true` (trivial postconditions) | ✅ (cleaned in audit) |
| Zero commented-out code | ✅ (cleaned in audit) |
| All `.fst.checked` files present | ✅ (12/12) |

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

| Algorithm | Exact Count | Asymptotic | Proven? |
|-----------|-------------|------------|---------|
| Bellman-Ford | n + n³ ticks | O(V³) | ✅ |
| Dijkstra | n + 2n² ticks | O(V²) | ✅ |

### Documentation

| Check | Result |
|-------|--------|
| All 12 files have module-level doc headers | ✅ |
| README.md covers all files and properties | ✅ |
| Sentinel constraint documented | ✅ |
| SNIPPET markers in Impl files | ✅ |
| No stale comments | ✅ |

### Z3 Resource Limits

| File | Max rlimit | Notes |
|------|-----------|-------|
| BellmanFord.fst | 80 | Main function |
| BellmanFord.Complexity.Instrumented.fst | 80 | Main function |
| Dijkstra.fst | 40 | Reduced from 200 after profiling |
| Dijkstra.Complexity.fst | default | — |
| Dijkstra.TriangleInequality.fst | 60 | `find_improving_predecessor` |
| ShortestPath.Triangle.fst | 100 | `chain_B_property` |
| BellmanFord.SpecBridge.fst | 10 | All queries well under limit |

### Overall Assessment

| Dimension | Rating |
|-----------|--------|
| CLRS Fidelity | ★★★★☆ — faithful adj-matrix adaptation; missing predecessor π |
| Specification Strength | ★★★★★ — d[v]=δ(s,v) proven for both algorithms |
| Complexity | ★★★★★ — exact tick counts; asymptotic bounds verified |
| Proof Quality | ★★★★★ — zero admits/assumes across 12 files |
| Documentation | ★★★★★ — comprehensive headers; sentinel documented |
| **Rubric Structural Compliance** | **★★★☆☆** — substance fully present; 6/14 interface files missing; naming diverges from rubric convention |
