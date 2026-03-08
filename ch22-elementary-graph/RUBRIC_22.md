# Chapter 22: Elementary Graph Algorithms — Rubric

**Date:** 2025-07-14 (updated 2026-07-17)

---

## File Inventory

### BFS (CLRS §22.2)

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch22.BFS.Spec.fst` | 166 | Pure level-set BFS specification. Graph as flat `seq int`. Proves CLRS Lemma 22.1 (edge ⟹ visited at next level), source distance = 0. |
| `CLRS.Ch22.BFS.DistanceSpec.fst` | 1,116 | Shortest-path specification via BFS state machine. Graph as `seq bool`. Proves CLRS Thm 22.5 (`bfs_correctness`: BFS distances = shortest-path distances). |
| `CLRS.Ch22.BFS.Impl.fst` | ~750 | Pulse queue-based BFS (CLRS §22.2 pseudocode). Graph as flat `seq int` via `Graph.Common`. Ghost tick counter proves ≤ 2V² operations. **Postcondition includes reachability: every discovered vertex v satisfies `reachable_in adj n source v dist[v]`.** |
| `CLRS.Ch22.BFS.Impl.fsti` | ~88 | Interface exposing `queue_bfs` signature with pre/postconditions including reachability. |
| `CLRS.Ch22.IterativeBFS.fst` | 265 | Alternative relaxation-based BFS (Bellman-Ford-like, O(V³)). Self-contained. |

**Architecture note:** BFS.Spec, BFS.DistanceSpec, and BFS.Impl are three independent developments using different graph representations. Impl does not depend on Spec or DistanceSpec — it proves its own invariants inline. All three are fully proved (zero admits).

### DFS (CLRS §22.3)

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch22.DFS.Spec.fst` | 2,929 | Pure functional DFS with discovery/finish timestamps. Graph as 2D `seq (seq int)`. Proves parenthesis theorem (Thm 22.7), edge classification (tree/back/forward/cross), cycle ⟺ back edge (Thm 22.11). |
| `CLRS.Ch22.DFS.WhitePath.fst` | 1,103 | White-path theorem (Thm 22.9) — both directions. Depends on DFS.Spec. |
| `CLRS.Ch22.DFS.TopologicalSort.fst` | 731 | Proves DFS finish-time ordering is a valid topological order. Bridges DFS.Spec (2D) ↔ TopologicalSort.Spec (1D) via `adj_equiv` + `has_edge_equiv`. |
| `CLRS.Ch22.DFS.Impl.fst` | ~1,170 | Pulse stack-based DFS (CLRS §22.3). Graph as flat `seq int` via `Graph.Common`. Ghost tick counter proves ≤ 2V² operations. **Postcondition includes `pred_edge_ok`: for every vertex v with pred[v] ≥ 0, there is an edge from pred[v] to v and d[pred[v]] < d[v], proving the predecessor tree is a valid subgraph.** |
| `CLRS.Ch22.DFS.Impl.fsti` | ~97 | Interface exposing `stack_dfs` signature with pre/postconditions including pred_edge_ok. |

**Architecture note:** DFS.Spec (2D adjacency) and DFS.Impl (flat 1D) are disconnected — Impl does not depend on Spec. DFS.TopologicalSort bridges the two representations. All files fully proved (zero admits).

### Topological Sort (CLRS §22.4)

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch22.TopologicalSort.Spec.fst` | 243 | Core definitions: `is_topological_order`, `has_cycle`, `is_dag`, `all_distinct`. Proves topological order ⟹ DAG. |
| `CLRS.Ch22.TopologicalSort.Lemmas.fst` | ~670 | Invariant predicates for Kahn's algorithm: `strong_order_inv`, `queue_preds_in_output`, `indeg_correct`. ~38 lemmas about invariant preservation under enqueue/dequeue/output-extend operations. |
| `CLRS.Ch22.TopologicalSort.Lemmas.fsti` | ~300 | Interface: definitions exposed as `let`, proofs hidden as `val`. |
| `CLRS.Ch22.TopologicalSort.Verified.fst` | 608 | Bridge: proves Kahn's `strong_order_inv` ⟹ `is_topological_order`. Converts int↔nat representations. Includes pigeonhole principle for completeness and `non_output_implies_cycle` for termination. |
| `CLRS.Ch22.TopologicalSort.Impl.Defs.fst` | 1,827 | Named predicates for Kahn's loop invariants (Pulse-facing): `partial_distinct`, `queue_fresh`, `zero_indeg_accounted`, etc. |
| `CLRS.Ch22.TopologicalSort.Impl.Defs.fsti` | 1,293 | Interface for Impl.Defs. |
| `CLRS.Ch22.TopologicalSort.Impl.fst` | 751 | Pulse implementation of Kahn's algorithm. Full verification chain: Spec → Lemmas → Verified → Impl.Defs → Impl. |
| `CLRS.Ch22.TopologicalSort.Impl.fsti` | ~60 | Interface exposing `topological_sort` signature. |

**Architecture note:** Unlike BFS/DFS, TopologicalSort has a complete verification chain from spec to implementation. The DFS-based topological sort (CLRS §22.4 canonical algorithm) is proved correct in `DFS.TopologicalSort.fst`.

### Shared Infrastructure

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch22.Graph.Common.fst` | ~93 | `has_edge` (flat matrix), `reachable_in`, `pred_edge_ok` (opaque, predecessor tree validity), ghost counter helpers (`tick`, `incr_nat`), `product_strict_bound`. Used by BFS.Impl and DFS.Impl. |

---

## Proof Quality

- **Zero admits** across all ~13,800 lines — no `admit()`, `admit_()`, `assume()`, `assume_()`
- **CLRS theorems proved:**
  - Parenthesis Theorem (Thm 22.7) — `DFS.Spec`
  - White-Path Theorem (Thm 22.9) — `DFS.WhitePath`
  - Edge Classification — `DFS.Spec`
  - Cycle ⟺ Back Edge (Thm 22.11) — `DFS.Spec`
  - BFS Shortest-Path Optimality (Thm 22.5) — `BFS.DistanceSpec`
  - DFS-based topological sort correctness — `DFS.TopologicalSort`
  - Kahn's correctness + completeness — `TopologicalSort.Verified`
- **Functional correctness (Impl ↔ graph structure):**
  - BFS.Impl: discovered vertex v ⟹ `reachable_in adj n source v dist[v]`
  - DFS.Impl: `pred_edge_ok` — pred[v] ≥ 0 ⟹ edge(pred[v],v) ∧ d[pred[v]] < d[v]
- **Complexity:** Ghost tick counters prove BFS.Impl ≤ 2V², DFS.Impl ≤ 2V², TopologicalSort.Impl ≤ V²

## Known Architectural Debt

1. **Spec↔Impl disconnect (BFS, DFS):** The pure specs and Pulse implementations use different graph representations and don't share code. Each proves things independently. Connecting them would require bridging lemmas similar to what DFS.TopologicalSort does.
2. **Graph representation proliferation:** `has_edge` appears with 4+ signatures across files — flat `seq int`, flat `seq bool`, 2D `seq (seq int)`, prop vs bool returns.
3. **Code duplication:** `reachable_in`, `incr_nat`/`tick` duplicated locally in some files due to Z3 proof sensitivity (documented in `Graph.Common` header).
