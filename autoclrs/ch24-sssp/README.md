# CLRS Chapter 24: Single-Source Shortest Paths

## Overview

This directory contains formally verified implementations of two classic SSSP algorithms from CLRS Chapter 24:

- **Bellman-Ford** — handles graphs with negative edge weights; detects negative-weight cycles
- **Dijkstra** — requires non-negative edge weights; uses linear-scan EXTRACT-MIN (O(V²))

Both operate on an adjacency-matrix representation (flat `n×n` array, row-major order) with `1000000` as the infinity sentinel.

## File Inventory (11 files, ~5 700 lines)

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch24.ShortestPath.Spec.fst` | 504 | Pure spec: `sp_dist_k`, `sp_dist`, triangle-inequality ⇒ upper-bound theorem |
| `CLRS.Ch24.ShortestPath.Triangle.fst` | 330 | `sp_dist_k` stabilization (pigeonhole), `sp_dist` triangle inequality for ≥0 weights |
| `CLRS.Ch24.BellmanFord.fst` | 540 | **Pulse implementation** of Bellman-Ford |
| `CLRS.Ch24.BellmanFord.Spec.fst` | 1 040 | Pure F\* BF spec: convergence (Thm 24.4), neg-cycle detection (Cor 24.5) |
| `CLRS.Ch24.BellmanFord.TriangleInequality.fst` | 339 | BF fixpoint ⇒ triangle inequality |
| `CLRS.Ch24.BellmanFord.Complexity.fst` | 101 | Pure O(V³) bound for adjacency-matrix BF |
| `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst` | 459 | Ghost-tick instrumented BF proving exact tick count n+n³ |
| `CLRS.Ch24.Dijkstra.fst` | 587 | **Pulse implementation** of Dijkstra |
| `CLRS.Ch24.Dijkstra.Correctness.fst` | 539 | Greedy-choice property (Thm 24.6) |
| `CLRS.Ch24.Dijkstra.Complexity.fst` | 372 | Ghost-tick instrumented Dijkstra proving O(V²) |
| `CLRS.Ch24.Dijkstra.TriangleInequality.fst` | 891 | Triangle inequality as consequence of relaxation |

## Verified Properties

### Bellman-Ford
- **dist[v] = δ(s,v)** when no negative-weight cycles (CLRS Theorem 24.4)
- **Negative-cycle detection**: returns `false` iff a negative-weight cycle is reachable (CLRS Corollary 24.5)
- **Triangle inequality**: dist[v] ≤ dist[u] + w(u,v) for all finite edges when no negative cycle
- **Upper bound**: dist[v] ≤ sp_dist(s,v) (CLRS Corollary 24.3)

### Dijkstra
- **dist[v] = δ(s,v)** for all vertices (postcondition)
- **Triangle inequality**: holds unconditionally (proven from relaxation process)
- **Greedy-choice property**: when u is extracted, dist[u] = δ(s,u) (CLRS Theorem 24.6)

### Complexity (Ghost-Tick Proofs)
| Algorithm | Exact Ticks | Asymptotic |
|-----------|------------|------------|
| Bellman-Ford | n + n³ | O(V³) = O(VE) for dense graph |
| Dijkstra | n + 2n² | O(V²) |

Ghost tick counters (`Pulse.Lib.GhostReference.ref nat`) are fully erased at runtime — zero overhead.

## Proof Quality

- **Zero admits** across all 11 files
- **Zero assumes** across all 11 files
- All 11 `.fst.checked` files present in `_cache/`

## Building

```bash
make verify
```

## Sentinel Constraint

Both algorithms use `1000000` as the infinity sentinel. Edge weights and all valid shortest-path distances must be strictly less than `1000000`. F\*'s `int` is mathematical (unbounded), so arithmetic overflow is not a concern — only the sentinel comparison matters.
