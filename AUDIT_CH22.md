# Audit Report: Chapter 22 — Elementary Graph Algorithms

**Scope:** BFS, DFS, Topological Sort (15 files, 13,059 lines)  
**Date:** 2025-07-14  
**All 15 files verified** (`.checked` files present in `_cache/`)

---

## 1. CLRS Fidelity

### BFS (§22.2) — Two Variants

| Aspect | CLRS | IterativeBFS | QueueBFS |
|--------|------|-------------|----------|
| Data structure | Queue | Iterative relaxation (n rounds) | Explicit queue (array-based) |
| Colors | WHITE/GRAY/BLACK | 0/non-zero (binary) | 0=WHITE, 1=GRAY, 2=BLACK |
| Distance | d[v] computed | d[v] computed | d[v] computed |
| Predecessor | π[v] | not tracked | π[v] tracked |
| Color transitions | W→G→B | W→visited | W→G→B |

**Why two variants?** `IterativeBFS` is a simpler, self-contained proof: it runs n relaxation rounds (Bellman-Ford-like level expansion) rather than queue-based exploration. This yields an easier verification at the cost of O(V³) work vs the optimal O(V²) of `QueueBFS`. `QueueBFS` faithfully follows the CLRS pseudocode, including ENQUEUE/DEQUEUE, GRAY/BLACK coloring, and predecessor tracking.

**Assessment:** `QueueBFS` is high-fidelity to CLRS §22.2. `IterativeBFS` is a correct but non-standard relaxation-based alternative. Both compute correct BFS distances. The documentation header in `IterativeBFS.fst` correctly warns it is iterative relaxation, not queue-based BFS. The `IterativeDFS.fst` header acknowledges this explicitly (line 17–22): "NOTE: This implements graph reachability exploration... A full CLRS DFS with discovery/finish timestamps... requires a stack-based implementation."

### DFS (§22.3) — Two Variants

| Aspect | CLRS | IterativeDFS | StackDFS |
|--------|------|-------------|----------|
| Structure | Recursive DFS-VISIT | Iterative relaxation (n rounds) | Explicit stack simulating recursion |
| Colors | WHITE/GRAY/BLACK | 0/non-zero (binary) | 0=WHITE, 1=GRAY, 2=BLACK |
| Timestamps | d[u], f[u] | None | d[u], f[u] |
| Predecessor | π[u] | None | π[u] |
| All-vertex loop | Yes (DFS outer) | Single source only | Yes (DFS outer loop) |

**Assessment:** `IterativeDFS` is essentially a copy of `IterativeBFS` with cosmetic differences — it is graph reachability, not DFS. `StackDFS` is the genuine CLRS DFS implementation with explicit stack, scan_idx per vertex (simulating the neighbor-scanning position saved in the recursive call stack), discovery/finish timestamps, and the outer loop visiting all vertices.

### DFS Specification (`DFS.Spec`) — 2,928 lines

This is the crown jewel of the chapter. Contains:
- Pure functional DFS (`dfs_visit`, `visit_neighbors`, `dfs_loop`, `dfs`)
- **Parenthesis Theorem** (CLRS Thm 22.7): Full proof via mutual induction on `dfs_visit_inv`/`visit_neighbors_inv`
- **Edge classification** (Tree/Back/Forward/Cross per CLRS §22.3)
- **All-edges invariant**: For every edge u→v with u Black: v non-White ∧ d[v] ≤ f[u]
- **DFS completeness**: After `dfs`, all vertices are non-White
- **Distinct finish times**: Proved via `all_f_distinct` invariant
- **Cycle detection**: Back edge ⟺ cycle (CLRS Thm 22.11)

### White-Path Theorem (`DFS.WhitePath`) — 1,104 lines

Proves CLRS Theorem 22.9 in both directions:
- **Forward**: `white_path_implies_descendant` — white path at time d[u] ⟹ dfs_ancestor
- **Backward**: `descendant_implies_white_path` — dfs_ancestor ⟹ white path exists
- Combined as `white_path_theorem` with the biconditional (line 926)

### Topological Sort (§22.4) — Kahn's Algorithm, Not CLRS's

| Aspect | CLRS §22.4 | This Library |
|--------|-----------|-------------|
| Algorithm | DFS + decreasing finish time | Kahn's (BFS-based in-degree reduction) |
| Specification | Finish-time ordering | `is_topological_order`: ∀ edges (u,v), u before v |
| DAG proof | Via back-edge detection | `topo_order_implies_dag` (Spec line 188) |
| Completeness | Not addressed | `lemma_non_output_implies_cycle` proves Kahn's processes all vertices in DAG |

**Assessment:** CLRS §22.4 describes TOPOLOGICAL-SORT via DFS (line 35651 of clrs_3e_2009.txt: "call DFS(G) to compute finishing times v.f for each vertex v"). This library instead implements **Kahn's algorithm** (not in CLRS Ch22 — the textbook mentions it briefly as "Another way" on line 35708). This is a valid alternative but a fidelity deviation. The DFS-based topological sort would follow naturally from the finish-time ordering already proved in `DFS.Spec`.

---

## 2. Specification Strength

### BFS Specifications

| Property | Status | File | Details |
|----------|--------|------|---------|
| Source distance = 0 | ✅ Proved | BFS.Spec:127, QueueBFS:482, IterativeBFS:88 | |
| Edge property (CLRS Lemma 22.1) | ✅ Proved | BFS.Spec:155 (`edge_implies_next_visited`) | |
| Reachability completeness | ✅ Proved | IterativeBFS:89, QueueBFS:481 | Reachable vertices visited |
| Distance soundness | ✅ Proved | IterativeBFS:92 (`reachable_in(source,v,dist[v])`) | |
| **Shortest-path optimality (Thm 22.5)** | ⚠️ Partial | BFS.DistanceSpec:9 | Easy direction proved; optimality ("no shorter path exists") explicitly **admitted** in the documentation |
| Distance non-negativity | ✅ Proved | QueueBFS:485 (`dist_ok`) | |
| Predecessor tree structure | ❌ Not specified | — | π[v] stored but no tree property proved |

**Key gap:** The BFS shortest-path optimality theorem (CLRS Thm 22.5) is not proved. `BFS.DistanceSpec` has the machinery (path definitions, `has_path_of_length`, `shortest_path_dist`) but the hard direction — that no shorter path exists — is missing. The file is 1,116 lines of infrastructure without the actual optimality lemma.

### DFS Specifications

| Property | Status | File | Details |
|----------|--------|------|---------|
| Parenthesis theorem (Thm 22.7) | ✅ Proved | DFS.Spec:1181 (`dfs_parenthesis_property`) | |
| White-path theorem (Thm 22.9) | ✅ Proved | DFS.WhitePath:913 (`white_path_theorem`) | |
| Edge classification | ✅ Defined | DFS.Spec:1197 | Tree/Back/Forward/Cross |
| All vertices visited (completeness) | ✅ Proved | DFS.Spec:1290 (`dfs_loop_visits_all`) | |
| d[u] < f[u] for Black vertices | ✅ Proved | DFS.Spec:60–69 (`valid_state`) | |
| Timestamps in range | ✅ Proved | DFS.Spec:442–498 | |
| d[u]=first, f[u]=last in visit | ✅ Proved | DFS.Spec:574 (`dfs_visit_du_fu`) | |
| Distinct finish times | ✅ Proved | DFS.Spec:2055+ | |
| Cycle ⟺ back edge (Thm 22.11) | ✅ Proved | DFS.Spec:1840+ | Via `all_edges_inv` |
| StackDFS: all BLACK at exit | ✅ Proved | StackDFS:1105 | Via `final_postcondition_lemma` |
| StackDFS: d > 0, f > 0, d < f | ✅ Proved | StackDFS:947–952 | |

### Topological Sort Specifications

| Property | Status | File | Details |
|----------|--------|------|---------|
| Definition of topological order | ✅ Proved | TopologicalSort.Spec:48 | |
| Topological order ⟹ DAG | ✅ Proved | TopologicalSort.Spec:188 | |
| Strong ordering invariant | ✅ Proved | TopologicalSort.Verified:294 | |
| Pigeonhole / permutation | ✅ Proved | TopologicalSort.Verified:253 | Fully proved (no admits) |
| Kahn's outputs valid topo order | ✅ Proved | TopologicalSort.Verified:439 | |
| DAG completeness (all vertices output) | ✅ Proved | TopologicalSort.Verified:584 | |

---

## 3. Complexity

### Proved Complexity Bounds

| Algorithm | Bound | File | Notes |
|-----------|-------|------|-------|
| QueueBFS | ≤ 2·V² ticks | QueueBFS:489 | Ghost tick counter, one per dequeue + one per edge check |
| StackDFS | ≤ 2·V² ticks | StackDFS:955 | Ghost tick counter, outer loop + scan_idx amortization |
| KahnTopologicalSort | ≤ V² ticks | KahnTopologicalSort.fst | Inner loop counted |

All complexity bounds are O(V²) because the graph uses adjacency-matrix representation (scanning V columns per vertex). `Graph.Complexity.fst` (69 lines) proves the meta-result: with adjacency matrix, O(V+E) ≤ O(V²).

**Assessment:** The bounds are tight for adjacency-matrix representation. The code correctly notes (Graph.Complexity:35–38) that adjacency-list representation would give O(V+E). The ghost-tick approach is sound: `GR.ref nat` is erased at extraction time.

### Complexity Proofs

- `QueueBFS`: Invariant `vc - c0 ≤ vhead * (n+1)`, discharged by `lemma_bfs_complexity_bound` (line 278)
- `StackDFS`: Amortized via `sum_scan_idx`: each scan step ticks once, and `scan_idx[u] ≤ n` for all u. Total = outer_loops + sum_scan_idx ≤ n + n² ≤ 2n². Discharged by `lemma_dfs_bound_correct` (line 300)
- `IterativeBFS`, `IterativeDFS`: No complexity tracking (no ghost counter)

---

## 4. Code Quality

### File Organization

The 15 files organize into a clear layered architecture:

```
Specifications (Pure F*)          Implementations (Pulse)
─────────────────────────────     ─────────────────────────
BFS.Spec (166 lines)              IterativeBFS (257 lines)
BFS.DistanceSpec (1,116 lines)    QueueBFS (677 lines)
DFS.Spec (2,928 lines)            IterativeDFS (213 lines)
DFS.WhitePath (1,104 lines)       StackDFS (1,112 lines)
TopologicalSort.Spec (243 lines)  KahnTopologicalSort (763 lines)
TopologicalSort.Lemmas (692 lines)
TopologicalSort.Verified (602 lines)
KahnTopologicalSort.Defs (fst+fsti: 1,827+1,290 lines)
Graph.Complexity (69 lines)
```

### Duplication Assessment

**Significant duplication between IterativeBFS and IterativeDFS:**
- `IterativeDFS` (213 lines) is structurally identical to `IterativeBFS` (257 lines) — both use the same n-round relaxation approach. The only differences: IterativeBFS also tracks `dist[]`, IterativeDFS only tracks color. The `has_edge`, `reachable_in`, and `reachable_in_succ_witness` definitions are copy-pasted identically.
- `IterativeDFS` adds no DFS-specific behavior (no timestamps, no stack structure). It is graph reachability, not DFS.

**Duplicated definitions across Pulse files:**
- `has_edge` is defined 5 times with slightly different types:
  - `BFS.Spec`: `(n:nat) → (adj: Seq.seq int) → (u v:nat) → bool` (flat int matrix)
  - `DFS.Spec`: `(n:nat) → (adj: Seq.seq (Seq.seq int)) → (u v:nat) → bool` (2D int matrix)
  - `IterativeBFS/IterativeDFS/QueueBFS/StackDFS`: `(adj: Seq.seq int) → (n:nat) → (u v:nat) → prop` (arg order differs; prop not bool)
  - `BFS.DistanceSpec`: `(n:nat) → (adj: Seq.seq bool) → (u v:nat) → bool` (bool matrix)
  - `TopologicalSort.Spec`: `(n:nat) → (adj: Seq.seq int) → (u v:nat) → bool`
- This inconsistency is a source of friction. Pulse files use `prop` (existential/propositional); spec files use `bool` (decidable). The `DFS.Spec` uniquely uses `Seq.seq (Seq.seq int)` (adjacency list of lists) while all others use flat matrix.
- `reachable_in` is copy-pasted 4 times (IterativeBFS, QueueBFS, IterativeDFS, StackDFS)
- `incr_nat` + ghost `tick` are copy-pasted 3 times (QueueBFS, StackDFS, KahnTopologicalSort)
- `product_strict_bound` is defined twice (QueueBFS:119, StackDFS:159)
- `count_ones` (StackDFS) and `count_nonwhite` (QueueBFS) are structurally identical with different names

**Recommendation:** Extract shared definitions into a common `Graph.Common` module.

### Helper Function Design

`QueueBFS` and `StackDFS` both use the pattern of extracting mutation sequences into helper functions (`discover_vertex`, `finish_vertex`, `maybe_discover`, `maybe_dfs_visit`) to work around Pulse's limitations with conditional branches that perform multiple array mutations. This is well-documented and idiomatic.

### Predicate Abstraction

Both `QueueBFS` and `StackDFS` use named predicate abstractions (`source_ok`, `dist_ok`, `queue_ok`, `stack_ok`, `dfs_ok`, `gray_ok`, `nonwhite_below`, `scan_ok`) with associated preservation lemmas. This is excellent practice that makes the invariants readable and maintainable.

---

## 5. Proof Quality

### Admits / Assumes

**Zero `admit()`, `admit_()`, `assume_()`, or `assume()` calls in any file.**

All 15 files are verified without proof holes. This is exceptional for a codebase of this size and complexity.

### Notable Proof Gaps (Not Admits, But Missing Theorems)

| Gap | Impact | Priority |
|-----|--------|----------|
| BFS shortest-path optimality (Thm 22.5) | The hard direction of Thm 22.5 is not stated as a lemma | Medium |
| BFS.DistanceSpec: `has_path_of_length` ↔ `path_from_to` connection | Infrastructure built but bridge lemma missing | Low |
| StackDFS postcondition lacks reachability | Only proves "all BLACK with valid timestamps", not "reachable vertices visited" | Low (proved in DFS.Spec) |
| QueueBFS postcondition lacks reachability | Only proves "visited ⟹ dist ≥ 0", not "reachable ⟹ visited" | Low |

### Proof Techniques

- **Mutual induction**: `dfs_visit`/`visit_neighbors` use `%[count_white_vertices st; ...]` termination measures extensively in `DFS.Spec` (12 mutually recursive lemma pairs)
- **Ghost counters**: `GR.ref nat` with `tick` for complexity accounting
- **Predicate-preservation lemma pattern**: Each state transition (discover/finish/blacken) gets dedicated preservation lemmas for each predicate cluster
- **Amortized complexity**: `StackDFS` uses `sum_scan_idx` to amortize scan work across DFS-VISIT calls — elegant

### Z3 Resource Usage

- Highest rlimit: `StackDFS:600`, `QueueBFS:600`
- Typical: 200 for helper functions, 30–50 for spec lemmas
- Fuel settings: consistently `--fuel 2 --ifuel 1` for Pulse code

### TIMESTAMP_TRACKING_NOTES.md

This file documents an abandoned attempt to prove stronger timestamp invariants in `StackDFS` — specifically proving "all vertices BLACK" from the loop invariant rather than using `final_postcondition_lemma`. The notes reveal real pain points with Pulse quantifier handling. The final solution (using `count_ones` + `nonwhite_below` + `dfs_ok` via `final_postcondition_lemma`) is clean.

---

## 6. Documentation Accuracy

| Claim | File:Line | Verdict |
|-------|-----------|---------|
| "Zero admits" | BFS.Spec:9 | ✅ Accurate |
| "NO admits. NO assumes." | IterativeBFS:18 | ✅ Accurate |
| "NO admits. NO assumes." | IterativeDFS:23 | ✅ Accurate |
| "Zero admits" | TopologicalSort.Spec:9 | ✅ Accurate |
| "Zero admits: all correctness arguments fully proved including pigeonhole" | TopologicalSort.Verified:16 | ✅ Accurate |
| "Note: We admit two standard lemmas" | TopologicalSort.Verified:431 | ⚠️ **Inaccurate** — the pigeonhole and position lemmas are now fully proved (lines 253–270, 377–400). The comment is stale. |
| "No shorter path exists (harder — admitted)" | BFS.DistanceSpec:9 | ✅ Accurate — this property is genuinely not proved |
| "Zero admits. The forward/backward directions use assume val predicates" | DFS.WhitePath:1098–1100 | ⚠️ **Misleading** — says "assume val predicates" but the grep finds zero `assume val` declarations in the file. The comment may be stale from an earlier revision. |
| IterativeDFS header says "DFS" | IterativeDFS:1 | ⚠️ Module name is misleading; it's reachability, not DFS. The NOTE at line 17 correctly clarifies. |

---

## 7. Task List

### Priority 1 (High) — Specification Gaps

| # | Task | Impact | Effort |
|---|------|--------|--------|
| 1.1 | **Prove BFS shortest-path optimality (CLRS Thm 22.5)** — the hard direction in BFS.DistanceSpec. The infrastructure (1,116 lines) is already built; the key missing lemma is "if v visited at step k, no shorter path exists". | Core BFS correctness | High |
| 1.2 | **Add reachability postcondition to QueueBFS** — currently only proves "visited ⟹ dist ≥ 0", not "reachable ⟹ visited". IterativeBFS proves the stronger property. | Spec completeness | Medium |
| 1.3 | **Add DFS-based topological sort** — CLRS §22.4 describes TOPOLOGICAL-SORT via finish-time ordering, not Kahn's. The finish-time machinery is already in DFS.Spec; just need to connect it to TopologicalSort.Spec. | CLRS fidelity | Medium |

### Priority 2 (Medium) — Code Quality

| # | Task | Impact | Effort |
|---|------|--------|--------|
| 2.1 | **Extract common definitions** — `has_edge`, `reachable_in`, `tick`, `product_strict_bound` into `Graph.Common.fst`. 5 redundant copies of `has_edge` with incompatible signatures is a maintenance hazard. | Maintainability | Medium |
| 2.2 | **Rename IterativeDFS → IterativeReachability** — the module name is misleading. The header already clarifies but the name in the module system persists. | Clarity | Low |
| 2.3 | **Unify graph representation** — `DFS.Spec` uses `Seq.seq (Seq.seq int)` (2D) while all Pulse files use flat `Seq.seq int`. This prevents direct linkage between the spec-level DFS and the imperative StackDFS. | Architecture | High |
| 2.4 | **Delete `DFS.WhitePath.fst.bak`** — backup file in the directory. | Hygiene | Trivial |

### Priority 3 (Low) — Documentation

| # | Task | Impact | Effort |
|---|------|--------|--------|
| 3.1 | **Fix stale comment in TopologicalSort.Verified:431** — says "we admit two standard lemmas" but both are now proved. | Accuracy | Trivial |
| 3.2 | **Fix stale comment in DFS.WhitePath:1099** — references "assume val predicates" that no longer exist. | Accuracy | Trivial |
| 3.3 | **Add cross-reference between DFS.Spec and StackDFS** — spec uses 2D adjacency list, imperative uses flat matrix; document the relationship. | Clarity | Low |
| 3.4 | **Document the BFS/DFS variant design decision** — why two BFS variants, why two DFS variants, and which is canonical. | Clarity | Low |

---

## Summary

**Strengths:**
- **Zero admits across 13,059 lines** — remarkable proof quality
- Complete proof of the parenthesis theorem (CLRS Thm 22.7) — a non-trivial result
- Complete proof of the white-path theorem (CLRS Thm 22.9) in both directions
- Sound complexity accounting via ghost tick counters
- Well-structured predicate abstraction pattern in Pulse implementations
- Topological sort correctness fully verified including pigeonhole principle

**Weaknesses:**
- BFS shortest-path optimality (CLRS Thm 22.5 hard direction) not proved despite 1,116 lines of infrastructure
- CLRS's DFS-based topological sort not implemented; only Kahn's (non-CLRS) algorithm
- Significant code duplication (5 copies of `has_edge`, 4 copies of `reachable_in`)
- Graph representation mismatch between spec (2D) and implementation (flat matrix)
- `IterativeDFS` is not DFS; it's a copy of the BFS relaxation approach

**Overall Assessment:** The DFS specification layer (`DFS.Spec` + `DFS.WhitePath`) is outstanding — it mechanizes the deep structural theorems of CLRS Ch22 (parenthesis, white-path, edge classification, cycle detection) with zero admits. The Pulse implementations (`QueueBFS`, `StackDFS`, `KahnTopologicalSort`) are well-engineered with verified complexity. The main gaps are the BFS optimality proof and the absence of the CLRS-style DFS-based topological sort.
