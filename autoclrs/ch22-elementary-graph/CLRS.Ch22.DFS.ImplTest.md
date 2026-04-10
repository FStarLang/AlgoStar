# CLRS.Ch22.DFS.ImplTest — Spec Validation Report

**Date:** 2026-03-18
**Status:** ✅ Verified (zero admits, zero assumes)
**Concrete Execution:** ✅ Extracted to C, compiled, and executed successfully (latest: 2026-04-10)

## Test Instance

3-vertex graph with edges 0→1 and 1→2.

```
Adjacency matrix (flat 3×3):
  [0, 1, 0,   -- vertex 0: edge to 1
   0, 0, 1,   -- vertex 1: edge to 2
   0, 0, 0]   -- vertex 2: no edges
```

## What Is Proven

| Property | Proven? | Method |
|----------|---------|--------|
| Precondition satisfiable | ✅ | Concrete array setup, `assert_norm (SZ.fits 9)` |
| All vertices BLACK (`scolor'[u] == 2`) | ✅ | Postcondition universal ∀u |
| Discovery times positive (`sd'[u] > 0`) | ✅ | Postcondition universal ∀u |
| Finish times positive (`sf'[u] > 0`) | ✅ | Postcondition universal ∀u |
| Parenthesis: `d[u] < f[u]` | ✅ | Postcondition universal ∀u |
| Timestamp bounds: `d[u] ≤ 2n`, `f[u] ≤ 2n` | ✅ | Postcondition universal ∀u |
| `pred_edge_ok` holds | ✅ | Direct from postcondition |
| **Predecessor finish ordering: `f[v] < f[pred[v]]`** | ✅ | NEW: Postcondition |
| **Predecessor values: `pred[1]=0`, `pred[2]=1`** | ✅ | NEW: Derived from pred_edge_ok + graph structure |
| Complexity bound (`cf ≤ 2·n²`) | ✅ | Direct from postcondition |

### Postcondition Strength Analysis

The DFS postcondition now captures:
- **Complete coverage:** all vertices finish BLACK (color == 2)
- **Timestamp validity:** d, f are positive, properly ordered, bounded by 2n
- **Predecessor tree:** `pred_edge_ok` — valid subgraph with d[pred[v]] < d[v]
- **Finish ordering:** `f[v] < f[pred[v]]` — children finish before parents

### Predecessor Values Derivation (NEW)

Using `pred_edge_ok` on the concrete graph: `adj[pred[v]*3+v] ≠ 0`. Since
only `adj[0*3+1]=1` and `adj[1*3+2]=1` are nonzero:
- `pred[1]` must be `0` (only vertex with edge to 1)
- `pred[2]` must be `1` (only vertex with edge to 2)

### Timestamp Ordering Derivation (NEW)

Combined postcondition properties determine the full DFS execution trace:
1. `pred_edge_ok` with `pred[1]=0`: d[0] < d[1]
2. `pred_edge_ok` with `pred[2]=1`: d[1] < d[2]
3. `pred_finish_ok` with `pred[2]=1`: f[2] < f[1]
4. `pred_finish_ok` with `pred[1]=0`: f[1] < f[0]
5. `d[u] < f[u]` for all u

Combined: **d[0] < d[1] < d[2] < f[2] < f[1] < f[0]**

With bounds [1, 2n] = [1, 6] and 6 strictly ordered integers:
**d[0]=1, d[1]=2, d[2]=3, f[2]=4, f[1]=5, f[0]=6**

The postcondition is now **Precise** — it uniquely determines all timestamps
for this concrete graph.

## What Is NOT Proven

| Property | Status | Reason |
|----------|--------|--------|
| Timestamp distinctness (formal) | ❌ | Derived implicitly via ordering chain |
| Edge classification | ❌ | Spec↔Impl disconnect (2D vs 1D adjacency) |
| White-path theorem | ❌ | Not exposed in Impl.fsti |

## Concrete Execution Results (2026-03-22)

The DFS test was extracted to C via KaRaMeL and executed:

```
$ make test
Ch22 ImplTest: running BFS, DFS, TopologicalSort tests...
Ch22 ImplTest: all tests passed.
```

The extracted C code:
- Allocates adjacency matrix, color, discovery time, finish time, predecessor, stack, and scan index arrays
- Sets edges 0→1 and 1→2 in the adjacency matrix
- Calls `stack_dfs` (the verified iterative DFS implementation)
- Frees all allocated memory
- Completes without errors, confirming the verified algorithm runs correctly on concrete data
