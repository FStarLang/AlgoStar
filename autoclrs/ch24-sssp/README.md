# CLRS Chapter 24: Single-Source Shortest Paths

## Overview

This directory contains formally verified implementations of two classic SSSP algorithms from CLRS Chapter 24:

- **Bellman-Ford** (§24.1) — handles graphs with negative edge weights; detects negative-weight cycles
- **Dijkstra** (§24.3) — requires non-negative edge weights; uses linear-scan EXTRACT-MIN (O(V²)); outputs predecessor tree

Both operate on an adjacency-matrix representation (flat `n×n` array, row-major order) with an abstract infinity sentinel (`ShortestPath.Inf.inf`).

## File Inventory (16 `.fst` + 9 `.fsti`, ~6 800 lines)

### Shared Infrastructure

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch24.ShortestPath.Inf.fsti` + `.fst` | 15 | Abstract infinity sentinel (`val inf : i:int{i > 0}`) |
| `CLRS.Ch24.ShortestPath.Spec.fst` | 1 060 | Pure spec: `sp_dist_k`, `sp_dist`, optimality, achievability, sentinel soundness |
| `CLRS.Ch24.ShortestPath.Triangle.fst` | 347 | `sp_dist_k` stabilization (pigeonhole), `sp_dist` triangle inequality for ≥0 weights |

### Bellman-Ford (§24.1)

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch24.BellmanFord.Impl.fsti` | 146 | **Public interface**: correctness + O(V³) complexity |
| `CLRS.Ch24.BellmanFord.Impl.fst` | 610 | Pulse implementation (fused correctness + complexity) |
| `CLRS.Ch24.BellmanFord.Spec.fst` | 1 040 | Pure spec: convergence (Thm 24.4), neg-cycle detection (Cor 24.5) |
| `CLRS.Ch24.BellmanFord.SpecBridge.fst` | 219 | Bridge: flat-weight ↔ adj-matrix equivalence |
| `CLRS.Ch24.BellmanFord.TriangleInequality.fst/fsti` | 384 | BF fixpoint ⇒ triangle inequality |
| `CLRS.Ch24.BellmanFord.Lemmas.fst/fsti` | 122 | Re-export interface for all BF lemmas |
| `CLRS.Ch24.BellmanFord.Complexity.fst/fsti` | 129 | Pure O(V³) complexity bounds |

### Dijkstra (§24.3)

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch24.Dijkstra.Impl.fsti` | 145 | **Public interface**: correctness + O(V²) complexity + predecessor tree |
| `CLRS.Ch24.Dijkstra.Impl.fst` | 116 | Wrapper: strengthens pred_consistent → shortest_path_tree |
| `CLRS.Ch24.Dijkstra.fst` | 888 | Core Pulse implementation (correctness + complexity + predecessor) |
| `CLRS.Ch24.Dijkstra.Spec.fst` | 42 | Re-exports shared `ShortestPath.Spec` definitions |
| `CLRS.Ch24.Dijkstra.Correctness.fst/fsti` | 420 | Greedy-choice property (CLRS Thm 24.6) |
| `CLRS.Ch24.Dijkstra.TriangleInequality.fst/fsti` | 931 | Processing all vertices ⇒ triangle inequality |
| `CLRS.Ch24.Dijkstra.Lemmas.fst/fsti` | 129 | Re-export interface for all Dijkstra lemmas |
| `CLRS.Ch24.Dijkstra.Complexity.fst/fsti` | 59 | Re-exports complexity bounds from `Dijkstra.fst` |

## Verified Properties

### Bellman-Ford
- **dist[v] = δ(s,v)** when no negative-weight cycles (CLRS Theorem 24.4)
- **Negative-cycle detection**: returns `false` iff a negative-weight cycle is reachable (CLRS Corollary 24.5)
- **Triangle inequality**: dist[v] ≤ dist[u] + w(u,v) for all finite edges when no negative cycle
- **Upper bound**: dist[v] ≤ sp\_dist(s,v) (CLRS Corollary 24.3)

### Dijkstra
- **dist[v] = δ(s,v)** for all vertices (postcondition)
- **Triangle inequality**: holds unconditionally (proven from relaxation process)
- **Greedy-choice property**: when u is extracted, dist[u] = δ(s,u) (CLRS Theorem 24.6)
- **Predecessor tree**: `pred` encodes a shortest-path tree with `pred_consistent` postcondition
- **Unreachability**: sp\_dist(s,v) = inf ⟹ ¬reachable(s, v)

### Complexity (Ghost-Tick Proofs)
| Algorithm | Exact Ticks | Asymptotic |
|-----------|------------|------------|
| Bellman-Ford | n + n³ | O(V³) = O(VE) for dense graph |
| Dijkstra | n + 2n² | O(V²) |

Ghost tick counters (`Pulse.Lib.GhostReference.ref nat`) are fully erased at runtime — zero overhead.

### Specification Strength
- **sp\_dist optimality**: ∀ valid path p: weight(p) ≥ δ(s,v) (non-negative weights)
- **sp\_dist achievability**: δ(s,v) < ∞ ⟹ ∃ path p with weight(p) = δ(s,v)
- **Sentinel soundness**: `weights_in_range` ⟹ sp\_dist faithfully represents shortest-path distances

## Proof Quality

- **Zero admits** across all 25 source files
- **Zero assumes** across all 25 source files
- All files verify with `make -j4` — clean build

## Building

```bash
make          # parallel build (default: -j4)
make -j1      # sequential build (~7 min)
```

## Sentinel Constraint

Both algorithms require `weights_in_range`: each finite edge weight `w` satisfies `|w|*(n-1) < inf`. The infinity sentinel is abstracted behind `ShortestPath.Inf.fsti` — proofs cannot depend on the specific numeric value. This guarantees that all simple-path weights are representable, so `sp_dist` faithfully captures true shortest-path distances.

## Reviews

- [Bellman-Ford Review](CLRS.Ch24.BellmanFord.Review.md) — detailed review with profiling and checklist
- [Dijkstra Review](CLRS.Ch24.Dijkstra.Review.md) — detailed review with profiling and checklist
