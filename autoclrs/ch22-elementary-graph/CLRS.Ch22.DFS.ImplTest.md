# CLRS.Ch22.DFS.ImplTest — Spec Validation Report

**Date:** 2026-03-17
**Status:** ✅ Verified (zero admits, zero assumes)

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
| **Timestamp bounds: `d[u] ≤ 2n`** | ✅ | NEW: Postcondition universal ∀u |
| **Timestamp bounds: `f[u] ≤ 2n`** | ✅ | NEW: Postcondition universal ∀u |
| `pred_edge_ok` holds | ✅ | Direct from postcondition |
| Complexity bound (`cf ≤ 2·n²`) | ✅ | Direct from postcondition |

### Postcondition Strength Analysis

The DFS postcondition captures:
- **Complete coverage:** all vertices finish BLACK (color == 2)
- **Timestamp validity:** discovery and finish times are positive, properly ordered,
  and bounded by 2n (d[u] ∈ [1, 2n], f[u] ∈ [1, 2n])
- **Predecessor tree:** `pred_edge_ok` ensures the predecessor tree is a valid subgraph
  (for each v with pred[v] ≥ 0: edge(pred[v], v) exists and d[pred[v]] < d[v])

### Timestamp Bounds (NEW)

The strengthened DFS postcondition now includes:
```
∀u. u < n ⟹ d[u] ≤ 2·n ∧ f[u] ≤ 2·n
```

Combined with `d[u] > 0` and `f[u] > 0`, this gives `d[u] ∈ [1, 2n]` and
`f[u] ∈ [1, 2n]`. For our 3-vertex test graph, timestamps are in [1, 6].

The bound is tight: DFS assigns exactly 2n distinct timestamps (n discoveries
+ n finishes), so the maximum timestamp is exactly 2n.

## What Is NOT Proven

| Property | Status | Reason |
|----------|--------|--------|
| Exact discovery/finish timestamps | ❌ | Timestamps are implementation-dependent |
| Timestamp distinctness (all 2n unique) | ❌ | Not exposed in Impl.fsti |
| Edge classification (tree/back/forward/cross) | ❌ | Not exposed in Impl.fsti |
| White-path theorem | ❌ | Proven in DFS.WhitePath but not in Impl.fsti |
| DFS forest structure | ❌ | Not exposed in Impl.fsti |

### FINDING: Spec↔Impl Disconnect

The DFS specification (`DFS.Spec.fst`) proves major CLRS theorems:
- Parenthesis Theorem (Thm 22.7)
- White-Path Theorem (Thm 22.9)
- Edge Classification (tree/back/forward/cross)
- Cycle ⟺ Back Edge (Thm 22.11)

None of these are exposed through `DFS.Impl.fsti`. The implementation
interface only exposes:
1. All vertices colored BLACK
2. Timestamp ordering (d < f)
3. Predecessor tree validity (`pred_edge_ok`)
4. Complexity bound

This is the Spec↔Impl disconnect noted in REVIEW.md. The Spec uses 2D
`seq (seq int)` adjacency while the Impl uses flat `seq int`, making
it difficult to bridge the gap without representation-conversion lemmas.

**Impact:** The postcondition is sufficient to verify basic structural
properties but cannot prove any DFS-specific graph-theoretic results
(edge classification, white-path theorem, etc.).

**Recommendation:** Add bridging lemmas connecting DFS.Spec to DFS.Impl,
similar to what `DFS.TopologicalSort.fst` does for the topological sort case.
