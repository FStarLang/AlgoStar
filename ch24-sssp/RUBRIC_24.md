# Chapter 24: Single-Source Shortest Paths — Rubric Compliance

**Date:** 2025-07-17 (updated 2026-03-04)
**Scope:** `ch24-sssp/` — 17 `.fst` files + 6 `.fsti` files, ~6 500 lines
**Verification:** All 23 `.fst`/`.fsti` files verify — **all files verify**

---

## Current File Inventory

| # | File | Lines | Rubric Role | Algorithm |
|---|------|------:|-------------|-----------|
| 1 | `CLRS.Ch24.ShortestPath.Spec.fst` | 504 | **Spec** (shared) | — (shared by BF & Dijkstra) |
| 2 | `CLRS.Ch24.ShortestPath.Triangle.fst` | 330 | **Lemmas** (shared) | — (shared by BF & Dijkstra) |
| 3 | `CLRS.Ch24.BellmanFord.Spec.fst` | 1 040 | **Spec** | Bellman-Ford |
| 4 | `CLRS.Ch24.BellmanFord.fst` | 540 | **Impl** (core) | Bellman-Ford |
| 5 | `CLRS.Ch24.BellmanFord.Impl.fst` + `.fsti` | ~100 | **Impl** (rubric wrapper) | Bellman-Ford |
| 6 | `CLRS.Ch24.BellmanFord.SpecBridge.fst` | 219 | **Lemmas** (bridge) | Bellman-Ford |
| 7 | `CLRS.Ch24.BellmanFord.TriangleInequality.fst` | 339 | **Lemmas** (triangle) | Bellman-Ford |
| 8 | `CLRS.Ch24.BellmanFord.Lemmas.fst` + `.fsti` | ~80 | **Lemmas** (re-export) | Bellman-Ford |
| 9 | `CLRS.Ch24.BellmanFord.Complexity.fst` + `.fsti` | 101 | **Complexity** | Bellman-Ford |
| 10 | `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst` | 459 | **Complexity** (variant) | Bellman-Ford |
| 11 | `CLRS.Ch24.Dijkstra.fst` | 587 | **Impl** (core) | Dijkstra |
| 12 | `CLRS.Ch24.Dijkstra.Impl.fst` + `.fsti` | ~80 | **Impl** (rubric wrapper) | Dijkstra |
| 13 | `CLRS.Ch24.Dijkstra.Spec.fst` | ~40 | **Spec** (re-export) | Dijkstra |
| 14 | `CLRS.Ch24.Dijkstra.Correctness.fst` | 539 | **Lemmas** (greedy) | Dijkstra |
| 15 | `CLRS.Ch24.Dijkstra.TriangleInequality.fst` | 891 | **Lemmas** (triangle) | Dijkstra |
| 16 | `CLRS.Ch24.Dijkstra.Lemmas.fst` + `.fsti` | ~80 | **Lemmas** (re-export) | Dijkstra |
| 17 | `CLRS.Ch24.Dijkstra.Complexity.fst` + `.fsti` | 372 | **Complexity** | Dijkstra |

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
| **Spec.fst** — Pure specification | ✅ `BellmanFord.Spec.fst` + shared `ShortestPath.Spec.fst` | ✅ `Dijkstra.Spec.fst` (re-exports shared `ShortestPath.Spec.fst`) | ✅ Both present |
| **Lemmas.fst** — Correctness proofs | ✅ `BellmanFord.Lemmas.fst` (re-exports `SpecBridge` + `TriangleInequality`) | ✅ `Dijkstra.Lemmas.fst` (re-exports `Correctness` + `TriangleInequality`) | ✅ Both present |
| **Lemmas.fsti** — Interface | ✅ `BellmanFord.Lemmas.fsti` | ✅ `Dijkstra.Lemmas.fsti` | ✅ Both present |
| **Complexity.fst** — Complexity proofs | ✅ `Complexity.fst` + `Complexity.Instrumented.fst` | ✅ `Dijkstra.Complexity.fst` | ✅ Both present |
| **Complexity.fsti** — Interface | ✅ `BellmanFord.Complexity.fsti` | ✅ `Dijkstra.Complexity.fsti` | ✅ Both present |
| **Impl.fst** — Pulse implementation | ✅ `BellmanFord.Impl.fst` (wrapper) + `BellmanFord.fst` (core) | ✅ `Dijkstra.Impl.fst` (wrapper) + `Dijkstra.fst` (core) | ✅ Both present |
| **Impl.fsti** — Public interface | ✅ `BellmanFord.Impl.fsti` | ✅ `Dijkstra.Impl.fsti` | ✅ Both present |

### Summary Counts

| Status | Count | Description |
|--------|------:|-------------|
| ✅ Full compliance | 14/14 | All rubric slots filled for both algorithms |
| 🔶 Substance present, naming/structure differs | 0/14 | — |
| ❌ Missing | 0/14 | — |

---

## Detailed Action Items

### Priority 1 — Structural Compliance (naming) — ✅ DONE

| # | Action | Status |
|---|--------|--------|
| 1.1 | **Create BellmanFord.Impl.fst** — wrapper re-exporting `bellman_ford` from `BellmanFord.fst` | ✅ Done |
| 1.2 | **Create Dijkstra.Impl.fst** — wrapper re-exporting `dijkstra` from `Dijkstra.fst` | ✅ Done |
| 1.3 | **Create BellmanFord.Lemmas.fst** — re-export module combining `SpecBridge` + `TriangleInequality` | ✅ Done |
| 1.4 | **Create Dijkstra.Lemmas.fst** — re-export module combining `Correctness` + `TriangleInequality` | ✅ Done |
| 1.5 | **Create Dijkstra.Spec.fst** — re-export of `ShortestPath.Spec` for rubric compliance | ✅ Done |

### Priority 2 — Missing Interface Files — ✅ DONE

| # | Action | Status |
|---|--------|--------|
| 2.1 | **Create BellmanFord.Lemmas.fsti** | ✅ Done |
| 2.2 | **Create Dijkstra.Lemmas.fsti** | ✅ Done |
| 2.3 | **Create BellmanFord.Complexity.fsti** | ✅ Done |
| 2.4 | **Create Dijkstra.Complexity.fsti** | ✅ Done |
| 2.5 | **Create BellmanFord.Impl.fsti** | ✅ Done |
| 2.6 | **Create Dijkstra.Impl.fsti** | ✅ Done |

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
| Zero `admit()` across all files | ✅ |
| Zero `assume` across all files | ✅ |
| Zero `ensures true` (trivial postconditions) | ✅ (cleaned in audit) |
| Zero commented-out code | ✅ (cleaned in audit) |
| All `.fst.checked` / `.fsti.checked` files present | ✅ (23/23) |

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
| All files have module-level doc headers | ✅ |
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
| Proof Quality | ★★★★★ — zero admits/assumes across all files |
| Documentation | ★★★★★ — comprehensive headers; sentinel documented |
| **Rubric Structural Compliance** | **★★★★★** — all 14/14 rubric slots filled; interface files present; Impl/Lemmas/Spec/Complexity naming convention satisfied |
