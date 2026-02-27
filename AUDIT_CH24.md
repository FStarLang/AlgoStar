# Audit Report: Chapter 24 — Single-Source Shortest Paths

**Date:** 2025-02-26  
**Scope:** `ch24-sssp/` — 11 files, 5 702 lines  
**Verification status:** All 11 `.fst.checked` files present in `_cache/` — **all files verify**.

---

## 0. File Inventory

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch24.ShortestPath.Spec.fst` | 504 | Pure spec: `sp_dist_k`, `sp_dist`, triangle-inequality ⇒ upper-bound theorem |
| `CLRS.Ch24.ShortestPath.Triangle.fst` | 330 | `sp_dist_k` stabilization (pigeonhole), `sp_dist` triangle inequality for ≥0 weights |
| `CLRS.Ch24.BellmanFord.fst` | 540 | **Pulse implementation** of Bellman-Ford |
| `CLRS.Ch24.BellmanFord.Spec.fst` | 1 040 | Pure F* BF spec: convergence (Thm 24.4), neg-cycle detection (Cor 24.5) |
| `CLRS.Ch24.BellmanFord.TriangleInequality.fst` | 339 | BF fixpoint ⇒ triangle inequality |
| `CLRS.Ch24.BellmanFord.Complexity.fst` | 101 | Pure O(V³) bound for adjacency-matrix BF |
| `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst` | 459 | Ghost-tick instrumented BF proving exact tick count n+n³ |
| `CLRS.Ch24.Dijkstra.fst` | 587 | **Pulse implementation** of Dijkstra |
| `CLRS.Ch24.Dijkstra.Correctness.fst` | 539 | Greedy-choice property (Thm 24.6) |
| `CLRS.Ch24.Dijkstra.Complexity.fst` | 372 | Ghost-tick instrumented Dijkstra proving O(V²) |
| `CLRS.Ch24.Dijkstra.TriangleInequality.fst` | 891 | Triangle inequality as consequence of relaxation |

---

## 1. CLRS Fidelity

### 1.1 INITIALIZE-SINGLE-SOURCE

**CLRS** (p. 648):
```
INITIALIZE-SINGLE-SOURCE(G, s)
1  for each vertex v ∈ G.V
2      v.d = ∞
3      v.π = NIL
4  s.d = 0
```

**Implementation (BellmanFord.fst:320–342, Dijkstra.fst:396–419):**
Both algorithms implement initialization identically: a loop setting `dist[source] = 0` and `dist[v] = 1000000` for all other vertices.

| Aspect | CLRS | Implementation | Verdict |
|--------|------|----------------|---------|
| Distance init | ∞ for all, then s.d=0 | Loop: if source then 0 else 1000000 | ✅ Faithful |
| Predecessor π | Tracked | **Not tracked** | ⚠️ Omission — predecessor subgraph not computed |
| Sentinel value | ∞ (unbounded) | 1000000 (finite int) | ⚠️ Design choice — see §1.5 |

### 1.2 RELAX

**CLRS** (p. 649):
```
RELAX(u, v, w)
1  if v.d > u.d + w(u,v)
2      v.d = u.d + w(u,v)
3      v.π = u
```

**BellmanFord.fst:420–445:**
```fstar
let can_relax = (w_uv < 1000000 && dist_u < 1000000);
let sum = dist_u + w_uv;
let should_update = (can_relax && sum < old_dist_v && vv <> source);
let new_dist_v: int = (if should_update then sum else old_dist_v);
```

**Dijkstra.fst:536–541:**
```fstar
let can_relax = (visited_v = 0 && w < 1000000 && dist_u < 1000000);
let sum = dist_u + w;
let should_update = (can_relax && sum < old_dist);
let new_dist: int = (if should_update then sum else old_dist);
```

| Aspect | CLRS | Implementation | Verdict |
|--------|------|----------------|---------|
| Guard | `v.d > u.d + w` | Finiteness checks + `sum < old_dist_v` | ✅ Correct with sentinel encoding |
| Update | Set v.d and v.π | Set dist[v] only | ⚠️ No predecessor |
| BF: never relax source | Not in CLRS | `vv <> source` guard | ✅ Correct (preserves dist[s]=0) |
| Dijkstra: skip visited | Implicit (Q=V−S) | `visited_v = 0` guard | ✅ Faithful |

### 1.3 BELLMAN-FORD

**CLRS** (p. 651):
```
BELLMAN-FORD(G, w, s)
1  INITIALIZE-SINGLE-SOURCE(G, s)
2  for i = 1 to |V|−1
3      for each edge (u,v) ∈ E
4          RELAX(u, v, w)
5  for each edge (u,v) ∈ E
6      if v.d > u.d + w(u,v)
7          return FALSE
8  return TRUE
```

**BellmanFord.fst:318–540 structure:**
1. Init loop (lines 320–342) — ✅
2. Triple-nested relaxation: `round` 1..n−1, `u` 0..n−1, `v` 0..n−1 (lines 351–456) — ✅ (adjacency-matrix version iterates all V² entries per round, checking `w < 1000000` to identify real edges)
3. Neg-cycle detection: double-nested check pass (lines 463–527) — ✅

| CLRS Line | Implementation | Verdict |
|-----------|---------------|---------|
| Line 1 | Init loop | ✅ |
| Lines 2–4 | Triple nested loop, V−1 rounds × V × V | ✅ Correct (adjacency-matrix enumeration of E) |
| Lines 5–8 | Detection pass checking all V² entries | ✅ |
| Return bool | `result` ref set to `final_no_neg` | ✅ |

**Verdict:** ✅ **Faithful** to CLRS Bellman-Ford adapted for adjacency-matrix representation.

### 1.4 DIJKSTRA

**CLRS** (p. 658):
```
DIJKSTRA(G, w, s)
1  INITIALIZE-SINGLE-SOURCE(G, s)
2  S = ∅
3  Q = G.V
4  while Q ≠ ∅
5      u = EXTRACT-MIN(Q)
6      S = S ∪ {u}
7      for each vertex v ∈ G.Adj[u]
8          RELAX(u, v, w)
```

**Dijkstra.fst:362–587 structure:**
1. Init loop (lines 396–421) — ✅
2. `visited` vector (Vec.alloc 0 n) plays role of S — ✅
3. Main loop: n rounds (lines 435–567):
   - `find_min_unvisited` linear scan (lines 284–359) — EXTRACT-MIN via O(V) scan — ✅
   - Mark u visited (line 477) — S = S ∪ {u} — ✅
   - Inner loop relaxing all V edges from u (lines 488–544) — ✅

| CLRS Line | Implementation | Verdict |
|-----------|---------------|---------|
| Line 1 | Init loop | ✅ |
| Lines 2–3 | `visited` vector, all 0 | ✅ |
| Line 4 | `round < n` with count_ones tracking | ✅ |
| Line 5 | `find_min_unvisited` O(V) scan | ✅ (array-based, no binary heap) |
| Line 6 | `V.op_Array_Assignment visited u 1` | ✅ |
| Lines 7–8 | Inner v-loop, relaxing all neighbors | ✅ |

**Verdict:** ✅ **Faithful** to CLRS Dijkstra adapted for adjacency-matrix representation.

### 1.5 Sentinel / Infinity Encoding

Both algorithms use `1000000` as the infinity sentinel. This is a pragmatic choice for machine integers but introduces a semantic gap:

- **No overflow check**: The sum `dist_u + w_uv` is computed as `int` (unbounded in F*), so no arithmetic overflow occurs.
- **Guard `w < 1000000 && d < 1000000`**: Prevents adding ∞ + w, matching CLRS's convention ∞ + a = ∞.
- **BellmanFord.fst:49–52** explicitly requires `valid_distances`: every distance is either `< 1000000` or `== 1000000`.
- **Risk**: If edge weights sum to ≥ 1000000 on a valid shortest path, the algorithm would silently produce wrong results. However, F*'s `int` is mathematical (unbounded), so the only issue is the sentinel choice, not machine overflow.

**Recommendation:** Document the sentinel's implicit range constraint on edge weights.

---

## 2. Specification Strength

### 2.1 Shortest-Path Specification (`ShortestPath.Spec.fst`)

The spec defines shortest-path distance via Bellman-Ford-style dynamic programming:

```fstar
sp_dist_k weights n s v k  // min-weight path from s to v using ≤ k edges
sp_dist weights n s v = sp_dist_k weights n s v (n−1)
```

Key proven properties:
| Property | CLRS Reference | Status |
|----------|---------------|--------|
| `sp_dist_k_monotone`: more edges ⇒ ≤ distance | — | ✅ Proven |
| `sp_dist_k_bounded`: sp_dist_k ≤ inf | — | ✅ Proven |
| `sp_dist_source_nonpositive`: sp_dist(s,s) ≤ 0 | — | ✅ Proven |
| `sp_dist_k_triangle`: sp_dist_k(v,k) ≤ sp_dist_k(u,k−1)+w(u,v) | — | ✅ Proven |
| `triangle_ineq_implies_upper_bound`: triangle ineq ⇒ dist[v] ≤ sp_dist | Cor 24.3 | ✅ **Proven by induction on k** |
| `sp_dist_triangle_flat`: under no_neg_cycles, sp_dist satisfies triangle ineq | — | ✅ Proven |
| `no_neg_cycles_flat`: sp_dist_k(v,n) == sp_dist_k(v,n−1) | — | ✅ Defined |

### 2.2 Stabilization Lemma (`ShortestPath.Triangle.fst`)

The crucial lemma `sp_dist_k_stabilize`:
```fstar
sp_dist_k weights n s v n == sp_dist_k weights n s v (n−1)
```
for non-negative weights. This is the pigeonhole argument: if n-th iteration still improves, build a chain of n+1 predecessor vertices ⇒ pigeonhole gives a repeated vertex ⇒ non-negative cycle can be contracted ⇒ contradiction.

**Status:** ✅ **Fully proven** (lines 283–312). Uses `Fin.pigeonhole`, `chain_vertex`, `chain_telescoping`, and `build_chain_seq`. The earlier comment in `Dijkstra.fst:30` saying "One admit() in dependency: sp_dist_k_stabilize" is **stale/outdated** — the proof is complete.

### 2.3 d[v] = δ(s,v) Proven?

| Algorithm | Property | Status |
|-----------|----------|--------|
| **Bellman-Ford** | `dist[v] == sp_dist(s,v)` when no neg cycles AND detection passes | ✅ Proven (BellmanFord.fst:313–315, via `bf_sp_equality_cond`) |
| **Bellman-Ford (Spec)** | `bf_convergence`: after n−1 rounds, dist = sp_dist | ✅ Proven (Spec.fst:838–863) |
| **Dijkstra** | `dist[v] == sp_dist(s,v)` for all v | ✅ Proven (Dijkstra.fst:390–391, postcondition) |

### 2.4 Negative-Cycle Detection

| Property | File | Status |
|----------|------|--------|
| Detection returns false ⇒ `exists_violation` | BellmanFord.fst:307 | ✅ Proven |
| `exists_relaxable_edge ⟺ extra round changes distances` | BellmanFord.Spec.fst:921–969 | ✅ Proven |
| Dijkstra: no neg cycles (precondition requires non-negative weights) | Dijkstra.fst:378 | ✅ N/A — non-negative weights precondition |

### 2.5 Triangle Inequality

| Algorithm | Property | Status |
|-----------|----------|--------|
| **BF (Pulse)** | `triangle_inequality` when detection passes | ✅ Proven (postcondition line 301) |
| **BF (TriangleInequality.fst)** | BF fixpoint ⇒ triangle inequality | ✅ Proven (`stable_distances_have_triangle`) |
| **Dijkstra (Pulse)** | `triangle_inequality` unconditional | ✅ Proven (postcondition line 389) |
| **Dijkstra (TriangleInequality.fst)** | Processing all vertices ⇒ triangle inequality | ✅ Proven (`dijkstra_algorithm_establishes_triangle`) |

### 2.6 Summary Table of CLRS Theorems Proven

| CLRS | Statement | Proven? |
|------|-----------|---------|
| Lemma 24.2 (Path relaxation) | After k rounds, dist ≤ sp_dist_k | ✅ `bf_correctness_inductive` |
| Corollary 24.3 (Upper bound) | dist[v] ≤ δ(s,v) after BF | ✅ `bf_sp_upper_bound_cond` |
| Theorem 24.4 (BF correctness) | dist[v] = δ(s,v) when no neg cycles | ✅ `bf_convergence` / `bf_sp_equality` |
| Corollary 24.5 (Neg-cycle detection) | BF returns FALSE ⟺ neg cycle reachable | ✅ `bf_negative_cycle_detection` |
| Theorem 24.6 (Dijkstra greedy) | Greedy choice yields δ(s,u) | ✅ `greedy_choice_invariant` |
| Lemma 24.10 (Triangle inequality) | δ(s,v) ≤ δ(s,u) + w(u,v) | ✅ `sp_dist_triangle_flat` / `sp_dist_triangle_ineq` |
| Lemma 24.11 (Upper bound) | Triangle ineq ⇒ upper bound on dist | ✅ `triangle_ineq_implies_upper_bound` |

---

## 3. Complexity

### 3.1 Bellman-Ford

**CLRS:** O(VE). With adjacency list, E can be as small as V. With adjacency matrix, each "scan all edges" takes O(V²), so total is O(V³).

**Implementation:**
- `BellmanFord.Complexity.fst`: Pure proof that `bellman_ford_iterations(v) = v + v³` and `≤ 2v³` (i.e., O(V³)).
- `BellmanFord.Complexity.Instrumented.fst`: Ghost-tick instrumented version proving `cf - c0 == n + n³` exactly.

| Metric | Value | Proven? |
|--------|-------|---------|
| Init ticks | n | ✅ |
| Relaxation ticks | (n−1)·n² | ✅ |
| Detection ticks | n² | ✅ |
| Total | n + n³ | ✅ Exact count in postcondition |
| Asymptotic | O(V³) = O(VE) for dense graph | ✅ `bellman_ford_cubic` |

**Note:** The O(VE) claim in CLRS assumes adjacency-list representation. For the dense adjacency-matrix used here, E = Θ(V²), so O(VE) = O(V³). The complexity analysis correctly accounts for this. The documentation in `Complexity.fst:14` explicitly notes: "With adjacency list, this would be O(VE) since we only check actual edges."

### 3.2 Dijkstra

**CLRS:** O(V² ) with array-based priority queue; O((V+E) lg V) with binary-heap priority queue.

**Implementation:**
- `Dijkstra.Complexity.fst`: Ghost-tick instrumented version proving `cf - c0 == n + 2n²`.
- `dijkstra_quadratic_bound`: `n + 2n² ≤ 3n²` for n ≥ 1.

| Metric | Value | Proven? |
|--------|-------|---------|
| Init ticks | n | ✅ |
| find_min ticks | n per round × n rounds = n² | ✅ |
| Relaxation ticks | n per round × n rounds = n² | ✅ |
| Total | n + 2n² | ✅ Exact count |
| Asymptotic | O(V²) | ✅ `dijkstra_quadratic_bound` |

The implementation uses a linear-scan EXTRACT-MIN (O(V) per extraction), matching the array-based O(V²) analysis in CLRS. The (V+E) lg V bound with binary heap is **not applicable** to this implementation.

### 3.3 Complexity Instrumentation Design

Both complexity proofs use **ghost tick counters** (`Pulse.Lib.GhostReference.ref nat`):
- Ghost state is fully erased at runtime — zero overhead.
- Each "interesting operation" (vertex init, edge check, relaxation) increments the counter by 1.
- Loop invariants carry exact tick counts (e.g., `vc - c0 == n + (vround-1)·n·n + vu·n + vv`).
- Postcondition: `bellman_ford_complexity_bounded cf c0 n` / `dijkstra_complexity_bounded cf c0 n`.

**Verdict:** ✅ Excellent complexity proofs — exact operational counts with verified asymptotic bounds.

---

## 4. Code Quality

### 4.1 Architecture

The module structure is clean and well-separated:

```
ShortestPath.Spec          ← Pure shortest-path oracle
ShortestPath.Triangle      ← Stabilization / triangle ineq for non-neg weights
BellmanFord                ← Pulse implementation
BellmanFord.Spec           ← Pure BF correctness theory
BellmanFord.TriangleInequality  ← BF fixpoint ⇒ triangle
BellmanFord.Complexity     ← Pure complexity bounds
BellmanFord.Complexity.Instrumented  ← Ghost-tick BF
Dijkstra                   ← Pulse implementation
Dijkstra.Correctness       ← Greedy-choice property
Dijkstra.Complexity        ← Ghost-tick Dijkstra
Dijkstra.TriangleInequality  ← Relaxation ⇒ triangle
```

### 4.2 Strengths

1. **Complete separation of concerns**: Pure specs, implementation, correctness proofs, and complexity proofs are in separate modules.
2. **No admits in any file** (all verified — see §5).
3. **Unconditional-write pattern**: `let new_val = if should_update then sum else old_val; write dist vv new_val` avoids Pulse branch-joining difficulties.
4. **Ghost-state discipline**: Lower-bound invariant (`lower_bound_inv`) carried through all loops, conditioned on `no_neg_cycles_flat` to avoid circular reasoning.
5. **Dual specification approach**: BellmanFord.Spec uses `option int` (closer to mathematical spec), while the Pulse code uses `int` with sentinel — both are developed and connected.
6. **The BellmanFord.Spec.fst** module is an exceptionally thorough pure specification at 1040 lines, proving all four major CLRS BF theorems.

### 4.3 Weaknesses

1. **Duplicated definitions**: `triangle_inequality`, `valid_distances`, `no_violations`, etc. are re-defined identically in `BellmanFord.fst` and `BellmanFord.Complexity.Instrumented.fst`. The instrumented version should import from the main module.
2. **Dijkstra.Correctness.fst** has significant dead code: `dist_via_settled_optimal`, `first_unsettled_has_optimal_distance`, `greedy_choice_upper_bound`, `optimal_settled_implies_upper_bounds` are commented out or have trivial ensures (`ensures true`). Lines 170, 376, 432 — these lemmas' `ensures` clauses are `true`, providing no actual guarantees.
3. **No predecessor tracking**: Neither algorithm computes the predecessor subgraph π, which is part of the CLRS specification. This means shortest-path trees cannot be reconstructed.
4. **Two parallel sp_dist definitions**: `ShortestPath.Spec` uses flat `Seq.seq int` (weights), while `BellmanFord.Spec` uses `adj_matrix` (seq of seq). These are never formally connected.
5. **Stale comment**: `Dijkstra.fst:30` claims "One admit() in dependency: sp_dist_k_stabilize in ShortestPath.Triangle.fst" but the proof is now complete.
6. **`count_ones` utilities** in `Dijkstra.fst` (lines 220–270) are general-purpose and should be factored into `common/`.
7. **Dijkstra.TriangleInequality.fst summary** (lines 856–891) references "lines 325-393 in CLRS.Ch24.Dijkstra.fst" — these line numbers are incorrect (the actual Dijkstra.fst is 587 lines and has no separate verification pass — the triangle inequality is proven inline).

### 4.4 Z3 Resource Limits

| File | Max rlimit | Notes |
|------|-----------|-------|
| BellmanFord.fst | 80 | Main function |
| BellmanFord.Complexity.Instrumented.fst | 80 | Main function |
| Dijkstra.fst | 200 | Main function + `split_queries always` |
| Dijkstra.Complexity.fst | — (default) | |
| Dijkstra.TriangleInequality.fst | 60 | `find_improving_predecessor` |
| ShortestPath.Triangle.fst | 100 | `chain_B_property` |

The Dijkstra.fst's `--z3rlimit 200 --split_queries always` suggests proof fragility. Worth monitoring.

---

## 5. Proof Quality — Admits and Assumes

### 5.1 Admits

**Zero admits across all 11 files.** Verified by:
1. `grep -n 'admit' *.fst` — only matches in documentation comments ("NO admits").
2. All 11 `.fst.checked` files present in `_cache/`.

### 5.2 Assumes

**Zero assumes across all 11 files.** Verified by `grep -n 'assume' *.fst` — only matches in documentation comments ("NO assumes") and a natural-language usage in `ShortestPath.Spec.fst:383` within a comment block ("assume distances are reasonable").

### 5.3 Trivial Ensures Clauses

Several lemmas in `Dijkstra.Correctness.fst` have `ensures true` or otherwise trivial postconditions:

| File:Line | Lemma | Ensures |
|-----------|-------|---------|
| Correctness.fst:169 | `dist_via_settled_optimal` | `ensures true` |
| Correctness.fst:375 | `subpath_weight_monotone` | `ensures true` |

These are essentially stubs — they type-check but prove nothing. They are **not** used by any other proof, so they don't compromise soundness, but they clutter the codebase.

### 5.4 Commented-Out Code

`Dijkstra.Correctness.fst` has ~100 lines of commented-out lemmas:
- Lines 278–305: `optimal_settled_implies_upper_bounds`
- Lines 388–434: `first_unsettled_has_optimal_distance`
- Lines 458–509: `greedy_choice_upper_bound`

These were abandoned during proof development. The final proof uses a cleaner approach via `SP.has_triangle_inequality`.

### 5.5 Opaque-to-SMT Annotations

`ShortestPath.Triangle.fst:134`: `[@@"opaque_to_smt"]` on `find_improving_predecessor`. This is a sound proof engineering technique (forces explicit unfolding), not a proof hole.

### 5.6 Overall Proof Assessment

**Excellent.** The proof structure is:
- BF: Lower bound (dist ≥ sp_dist) via induction on relaxation + upper bound (dist ≤ sp_dist) via triangle inequality theorem ⇒ equality.
- Dijkstra: Lower bound via induction on relaxation (carried as ghost invariant) + upper bound via triangle inequality (proven from relaxation process) ⇒ equality.

The key insight connecting them is `triangle_ineq_implies_upper_bound` in `ShortestPath.Spec.fst` — a deep result proven by induction on `sp_dist_k`.

---

## 6. Documentation Accuracy

### 6.1 Module-Level Documentation

| File | Has doc header? | Accuracy |
|------|:---:|----------|
| BellmanFord.fst | ✅ | Accurate, comprehensive (lines 15–34) |
| BellmanFord.Spec.fst | ✅ | Accurate, references CLRS Lemma 24.2 |
| BellmanFord.Complexity.fst | ✅ | Accurate |
| BellmanFord.Complexity.Instrumented.fst | ✅ | Accurate |
| BellmanFord.TriangleInequality.fst | ✅ | Accurate |
| Dijkstra.fst | ✅ | ⚠️ **Stale**: claims "One admit() in dependency" (line 30) — now proven |
| Dijkstra.Correctness.fst | ✅ | Accurate proof sketch of Theorem 24.6 |
| Dijkstra.Complexity.fst | ✅ | Accurate |
| Dijkstra.TriangleInequality.fst | ✅ | ⚠️ **Stale line references** to Dijkstra.fst (lines 856–891) |
| ShortestPath.Spec.fst | Partial | Inline comments only |
| ShortestPath.Triangle.fst | Minimal | One-line module doc |

### 6.2 README.md

The README (`ch24-sssp/README.md`) is **incomplete**:
- Mentions only Bellman-Ford, not Dijkstra.
- Says "Postconditions: Contains shortest path distances from source" — undersells the actual verified properties.
- Does not mention the complexity proofs.
- Lists "4 nested loops total" — correct for BF but doesn't cover Dijkstra.

### 6.3 SNIPPET markers

Both `BellmanFord.fst` and `Dijkstra.fst` use `//SNIPPET_START:` / `//SNIPPET_END:` markers for documentation extraction — good practice.

---

## 7. Task List

### Priority 1 (High) — Correctness / Completeness

| # | Task | File(s) | Rationale |
|---|------|---------|-----------|
| 1.1 | **Fix stale "One admit()" comment** | Dijkstra.fst:30 | Misleads readers into thinking the proof has a gap |
| 1.2 | **Unify `sp_dist` definitions** | ShortestPath.Spec.fst, BellmanFord.Spec.fst | Two independent `sp_dist_k` / `sp_dist` definitions (flat-weights vs. adj_matrix) are never formally connected; this leaves BellmanFord.Spec's theorems disconnected from the Pulse implementation's spec |
| 1.3 | **Remove dead-code lemmas with `ensures true`** | Dijkstra.Correctness.fst:169,375 | `dist_via_settled_optimal` and `subpath_weight_monotone` prove nothing; remove or complete |
| 2.1 | **Deduplicate definitions** between BellmanFord.fst and BellmanFord.Complexity.Instrumented.fst | Both | `triangle_inequality`, `valid_distances`, `no_violations`, etc. are copy-pasted; instrumented file should import from main |
| 2.2 | **Clean up commented-out code** | Dijkstra.Correctness.fst | ~100 lines of abandoned proof attempts |
| 2.3 | **Factor `count_ones` utilities** | Dijkstra.fst → common/ | General-purpose lemmas about counting 1s in a seq |
| 2.4 | **Fix stale line-number references** | Dijkstra.TriangleInequality.fst:857,860,877 | References to "lines 325-393" in Dijkstra.fst don't correspond to current code |
| 2.5 | **Monitor Dijkstra.fst z3rlimit 200** | Dijkstra.fst:360 | High rlimit + `split_queries always` suggests proof fragility. Use SMTProfiling skill to stabilize |
| 3.1 | **Update README.md** | README.md | Should cover all 11 files, both algorithms, complexity proofs, and the full postcondition |
| 3.2 | **Add predecessor (π) tracking** | BellmanFord.fst, Dijkstra.fst | CLRS algorithms compute π for path reconstruction; currently omitted |
| 3.3 | **Document sentinel constraint** | BellmanFord.fst, Dijkstra.fst | Edge weights must satisfy `w(u,v) < 1000000` and shortest paths must be `< 1000000`; not documented |
| 3.5 | **Add module doc to ShortestPath.Spec/Triangle** | Both files | These are the mathematical foundation; deserve comprehensive headers |

## Defer
| 3.4 | **Add adjacency-list variant** | New files | Current O(V³) BF and O(V²) Dijkstra are for dense graphs; adjacency-list would achieve O(VE) and O((V+E)lg V) |

---

## 8. Summary Assessment

| Dimension | Rating | Notes |
|-----------|--------|-------|
| **CLRS Fidelity** | ★★★★☆ | Faithful adaptation for adjacency matrix; missing predecessor π |
| **Specification Strength** | ★★★★★ | d[v]=δ(s,v) proven for both algorithms; triangle inequality, neg-cycle detection, upper/lower bounds all verified |
| **Complexity** | ★★★★★ | Exact tick counts proven; asymptotic bounds verified; ghost-tick approach is exemplary |
| **Code Quality** | ★★★★☆ | Clean architecture; some duplication and dead code |
| **Proof Quality** | ★★★★★ | **Zero admits, zero assumes** across 5,702 lines; all files verified |
| **Documentation** | ★★★☆☆ | Good module headers but README incomplete; stale comments |

**Overall: This is an exceptionally strong verified implementation.** The complete absence of admits across 11 files totaling 5,702 lines — covering both algorithms, their correctness theorems, and complexity analyses — is remarkable. The key mathematical achievement is the fully-mechanized proof of `triangle_ineq_implies_upper_bound` and the pigeonhole-based `sp_dist_k_stabilize`, which together provide the core theoretical foundation for both algorithms.
