# Chapter 24: Single-Source Shortest Paths — Rubric Compliance

**Date:** 2025-07-17 (updated 2026-03-06)
**Scope:** `ch24-sssp/` — 16 `.fst` files + 9 `.fsti` files, ~8 500 lines
**Verification:** All files verify — `make -j4` clean

---

## Current File Inventory

| # | File | Lines | Rubric Role | Algorithm |
|---|------|------:|-------------|-----------|
| 1 | `CLRS.Ch24.ShortestPath.Spec.fst` | ~860 | **Spec** (shared) | — (shared by BF & Dijkstra) |
| 2 | `CLRS.Ch24.ShortestPath.Triangle.fst` | 330 | **Lemmas** (shared) | — (shared by BF & Dijkstra) |
| 3 | `CLRS.Ch24.BellmanFord.Spec.fst` | 1 040 | **Spec** | Bellman-Ford |
| 4 | `CLRS.Ch24.BellmanFord.Impl.fst` + `.fsti` | ~610 | **Impl** (single fn: correctness + complexity) | Bellman-Ford |
| 5 | `CLRS.Ch24.BellmanFord.SpecBridge.fst` | 219 | **Lemmas** (bridge) | Bellman-Ford |
| 6 | `CLRS.Ch24.BellmanFord.TriangleInequality.fst` + `.fsti` | 340 | **Lemmas** (triangle) | Bellman-Ford |
| 7 | `CLRS.Ch24.BellmanFord.Lemmas.fst` + `.fsti` | ~80 | **Lemmas** (re-export) | Bellman-Ford |
| 8 | `CLRS.Ch24.BellmanFord.Complexity.fst` + `.fsti` | 101 | **Complexity** (pure bounds) | Bellman-Ford |
| 9 | `CLRS.Ch24.Dijkstra.fst` | ~870 | **Impl** (core: single fn with correctness + complexity + predecessor) | Dijkstra |
| 10 | `CLRS.Ch24.Dijkstra.Impl.fst` + `.fsti` | ~100 | **Impl** (re-export wrapper) | Dijkstra |
| 11 | `CLRS.Ch24.Dijkstra.Spec.fst` | ~40 | **Spec** (re-export) | Dijkstra |
| 12 | `CLRS.Ch24.Dijkstra.Correctness.fst` + `.fsti` | 539 | **Lemmas** (greedy, Thm 24.6) | Dijkstra |
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
| Shared shortest-path oracle (`sp_dist_k`, `sp_dist`) | `ShortestPath.Spec.fst` | Flat-weight formulation; `triangle_ineq_implies_upper_bound` (Cor 24.3); declarative characterisation (`sp_dist_optimal`, `sp_dist_achievable`) |
| Spec bridge (flat-weights ↔ adj_matrix) | `BellmanFord.SpecBridge.fst` | Mutual induction; zero admits |
| Triangle inequality from relaxation | `BellmanFord.TriangleInequality.fst` + `.fsti` | BF fixpoint ⇒ triangle; tight interface |
| Stabilization / pigeonhole | `ShortestPath.Triangle.fst` | `sp_dist_k_stabilize`, `sp_dist_triangle_ineq` |
| Pulse implementation + complexity | `BellmanFord.Impl.fst` + `.fsti` | **Single `bellman_ford` function** with ghost-tick complexity proof (O(V³)) |
| Complexity (pure bound) | `BellmanFord.Complexity.fst` + `.fsti` | O(V³) = O(VE) for dense graphs |

### Dijkstra (CLRS §24.3)

| Component | File(s) | Notes |
|-----------|---------|-------|
| Shared shortest-path oracle | `ShortestPath.Spec.fst` | Same as BF |
| Stabilization / pigeonhole | `ShortestPath.Triangle.fst` | Same as BF |
| Greedy-choice property (Thm 24.6) | `Dijkstra.Correctness.fst` + `.fsti` | Proof follows CLRS contradiction argument; tight interface |
| Triangle inequality from relaxation | `Dijkstra.TriangleInequality.fst` + `.fsti` | Processing all vertices ⇒ triangle; tight interface |
| Pulse implementation + complexity | `Dijkstra.fst` → `Dijkstra.Impl.fst/fsti` | **Single `dijkstra` function** with ghost-tick complexity proof (O(V²)), predecessor tree output; inner relax loop extracted into `dijkstra_relax_round` for SMT tractability |
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

### BellmanFord.Impl.fst — Single Unified Function

The old `BellmanFord.fst` (core implementation) and `BellmanFord.Complexity.Instrumented.fst`
(ghost-tick copy) have been merged into a single `BellmanFord.Impl.fst` with a single
`fn bellman_ford` that provides both correctness (dist[v] = δ(s,v)) and O(V³) complexity
guarantees via ghost tick counting threaded through all loop invariants.

### Dijkstra.Impl — Single Unified Function

`Dijkstra.fst` contains a single `fn dijkstra` with correctness (dist[v] = δ(s,v)),
O(V²) complexity guarantees, and a predecessor array output (pred[v] records the predecessor
of v on a shortest path from source, with `pred_consistent` in the postcondition). Ghost
tick counting is threaded through all loop invariants (init loop, find-min loop, relax loop
in the outer loop body). Individual ticks are counted per inner-loop iteration.

To work around an SMT scalability issue with Pulse nested loops (adding an extra
existential to an outer loop invariant causes inner-loop SMT blowup when the inner loop
has a complex invariant referencing outer `with`-bound variables), the inner relax loop +
bridge lemmas are extracted into a separate helper function `dijkstra_relax_round`. This
gives the inner loop its own Pulse elaboration scope, keeping SMT queries tractable.

`Dijkstra.Impl.fst` is a thin re-export wrapper under the rubric-required naming convention.

### Tight Interface Files

- `BellmanFord.TriangleInequality.fsti`: Exposes only `no_violations_implies_triangle`,
  `stable_distances_have_triangle`, `bellman_ford_stable_establishes_triangle` + types.
  Hides ~20 internal lemmas.
- `Dijkstra.TriangleInequality.fsti`: Exposes only `dijkstra_establishes_triangle_inequality`,
  `dijkstra_algorithm_establishes_triangle` + types. Hides ~30 internal lemmas.
- `Dijkstra.Correctness.fsti`: Exposes `greedy_choice_invariant` and
  `relax_establishes_triangle_inequality` + definitions used by `Dijkstra.Lemmas`.
- `ShortestPath.Triangle.fsti`: **Not created** — adding it breaks Pulse elaboration in
  `Dijkstra.fst` (same Pulse variable-numbering bug).

### Dijkstra.Correctness — Retained

Contains CLRS Theorem 24.6 (greedy choice invariant). Used by `Dijkstra.Lemmas`. This is
substantive proof content, not superseded by other files.

### ShortestPath.Spec — Declarative Characterisation of sp_dist

`sp_dist` is defined algorithmically (Bellman-Ford-style DP). Two new lemmas prove it IS
the shortest-path distance in a declarative sense:

- **Optimality** (`sp_dist_optimal`): For any valid path p from s to v with non-negative edge
  weights: `sp_dist(s,v) ≤ path_weight(p)`. (Every path is at least as long.)
- **Achievability** (`sp_dist_achievable`): If `sp_dist(s,v) < inf`, there exists a concrete
  valid path p whose weight equals `sp_dist(s,v)`. (The minimum is achieved.)

Together these establish: sp_dist(s,v) = min { path_weight(p) | p is a valid s→v path }.

Helper infrastructure: `path_prefix`, `path_penult`, `path_snoc` with weight decomposition
and validity preservation lemmas. The achievability proof constructs an explicit witnessing
path via `sp_dist_k_achieving_path` (a Pure function).

### Soundness of the Finite Sentinel (`weights_in_range`)

The sentinel constant `inf` is defined in `ShortestPath.Inf` with an abstract interface
that exposes only `val inf : i:int{i > 0}` — no proof can depend on the specific numeric
value. The `weights_in_range` predicate makes the representability constraint explicit:
each finite edge weight w must satisfy `|w| * (n-1) < inf`. Under this precondition:

- **`path_weight_bounded`**: any valid simple path (≤ n-1 edges) has total weight in [0, inf)
  (proven by induction with the stronger invariant `path_weight * (n-1) < path_edges * inf`).
- **`sp_dist_faithful`**: if vertex v is reachable from s via existing edges, then
  `sp_dist(s,v) < inf` — the spec faithfully represents the true shortest-path distance.

Both `Dijkstra.Impl` and `BellmanFord.Impl` now require `weights_in_range` as a precondition,
ensuring the algorithms operate within the representable domain.

### Dijkstra Predecessor Array (CLRS π)

The `dijkstra` function now outputs a predecessor array (`pred: A.array SZ.t`) in addition
to the shortest-path distances. The postcondition guarantees `pred_consistent`:

```
pred_consistent spred sdist sweights n source ≡
  pred[source] = source ∧
  ∀ v ≠ source with dist[v] < ∞:
    let p = pred[v] in
    dist[v] = dist[p] + w(p, v)
```

This establishes that `pred` encodes a shortest-path tree: for every reachable vertex v,
following the predecessor chain from v to source yields a shortest path.

Internal invariant `pred_ok` additionally tracks that each predecessor is a visited vertex,
which is needed to prove that predecessors' distances are frozen when the equation is checked.
The bridge lemma `relax_round_pred_ok` establishes preservation of `pred_ok` through each
relaxation round.

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
| **sp\_dist optimality** | ∀ valid path p: weight(p) ≥ δ(s,v) (non-neg weights) | ✅ `sp_dist_optimal` |
| **sp\_dist achievability** | δ(s,v) < ∞ ⟹ ∃ path p with weight(p) = δ(s,v) | ✅ `sp_dist_achievable` |

### Complexity Verification

| Algorithm | Exact Count | Asymptotic | Proven? | Integrated? |
|-----------|-------------|------------|---------|-------------|
| Bellman-Ford | n + n³ ticks | O(V³) ≤ 2n³ | ✅ | ✅ single `bellman_ford` fn in `BellmanFord.Impl.fst` |
| Dijkstra | n + 2n² ticks | O(V²) ≤ 3n² | ✅ | ✅ single `dijkstra` fn in `Dijkstra.Impl.fst` |

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
| **Dijkstra.fst** | **120** | `dijkstra_relax_round` (split_queries always); `dijkstra` at 60 |
| ShortestPath.Triangle.fst | 100 | `chain_B_property` |
| BellmanFord.Impl.fst | 80 | `bellman_ford` main function |
| ShortestPath.Spec.fst | 60 | `sp_dist_k_le_path_weight_exact`, `sp_dist_k_achieving_path`, `find_achieving_predecessor` |
| Dijkstra.TriangleInequality.fst | 60 | `find_improving_predecessor` |
| Dijkstra.Correctness.fst | 50 | `greedy_choice_invariant` |
| BellmanFord.SpecBridge.fst | 10 | All queries well under limit |

### Verification Time Profile (2026-03-16)

| File | Time (s) | Notes |
|------|----------|-------|
| **Dijkstra.fst** | **187** | Bottleneck: dijkstra_relax_round + dijkstra main |
| ShortestPath.Triangle.fst | 37 | Shared dependency: chain_B_property |
| BellmanFord.Impl.fst | 36 | Three nested loops with ghost invariants |
| ShortestPath.Spec.fst | 6 | |
| BellmanFord.Spec.fst | 6 | |
| Dijkstra.TriangleInequality.fst | 4 | |
| Dijkstra.Impl.fst | 4 | |
| Dijkstra.Complexity.fst | 4 | |
| BellmanFord.TriangleInequality.fst | 3 | |
| Dijkstra.Correctness.fst | 2 | |
| BellmanFord.SpecBridge.fst | 2 | |
| BellmanFord.Lemmas.fst | 2 | |
| BellmanFord.Complexity.fst | 1 | |
| Dijkstra.Lemmas.fst | 1 | |
| **Total (sequential)** | **~295** | ~5 min sequential; ~7 min with overhead |

### Overall Assessment

| Dimension | Rating |
|-----------|--------|
| CLRS Fidelity | ★★★★★ — faithful adj-matrix adaptation; predecessor array (π) output with `pred_consistent` |
| Specification Strength | ★★★★★ — d[v]=δ(s,v) proven; sp\_dist declaratively characterised (optimality + achievability) |
| Complexity | ★★★★★ — exact tick counts; asymptotic bounds verified; integrated with implementations |
| Proof Quality | ★★★★★ — zero admits/assumes across all files |
| Documentation | ★★★★★ — comprehensive headers; abstract inf; sentinel soundness proven |
| **Rubric Structural Compliance** | **★★★★★** — all 14/14 rubric slots filled; tight interface files; complexity integrated with implementations |
