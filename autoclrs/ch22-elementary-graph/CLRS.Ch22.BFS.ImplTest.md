# CLRS.Ch22.BFS.ImplTest — Spec Validation Report

**Date:** 2026-03-17
**Status:** ✅ Verified (zero admits, zero assumes)

## Test Instance

3-vertex graph with edges 0→1 and 1→2, source vertex 0.

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
| Source is visited (`scolor'[0] ≠ 0`) | ✅ | Direct from postcondition |
| Source distance = 0 (`sdist'[0] == 0`) | ✅ | Direct from postcondition |
| All 3 vertices discovered | ✅ | Reachability witnesses + completeness postcondition |
| Distance soundness (`sdist'[w] ≥ 0`) | ✅ | Direct from postcondition (universal ∀w) |
| Complexity bound (`cf ≤ 2·n²`) | ✅ | Direct from postcondition |

### Reachability Witnesses

Three auxiliary lemmas prove each vertex is reachable from source 0:

- **Vertex 0:** `reachable_in adj 3 0 0 0` — trivial (base case, 0 steps)
- **Vertex 1:** `reachable_in adj 3 0 1 1` — via edge 0→1 (1 step)
- **Vertex 2:** `reachable_in adj 3 0 2 2` — via 0→1→2 (2 steps)

The completeness postcondition (`∀v k. reachable_in ⟹ scolor'[v] ≠ 0`) then
implies all three vertices are discovered.

## What Is NOT Proven

| Property | Status | Reason |
|----------|--------|--------|
| `dist[1] == 1` | ❌ Not provable | Postcondition lacks shortest-path guarantee |
| `dist[2] == 2` | ❌ Not provable | Same: no shortest-path in Impl.fsti |

### FINDING: Missing Shortest-Path Property

The BFS postcondition states:
```
reachable_in sadj n source w (Seq.index sdist' w)
```
This says there **exists** a path of `dist[w]` steps. It does **not** say `dist[w]`
is the **minimum** path length. The shortest-path property is:
```
∀k. reachable_in sadj n source w k ⟹ dist[w] ≤ k
```

This property **is** proven in `BFS.DistanceSpec.fst` (Theorem 22.5) but is
**not** exposed through `BFS.Impl.fsti`. This is a spec weakness: the
implementation interface does not capture BFS's fundamental guarantee of
computing shortest-path distances.

**Impact:** For our concrete test graph (unique shortest paths: 0→1 length 1,
0→1→2 length 2), the postcondition cannot determine exact distance values.

**Recommendation:** Add a shortest-path postcondition clause to `BFS.Impl.fsti`:
```
// Shortest-path optimality
(forall (w: nat) (k: nat).
  w < SZ.v n /\ Seq.index scolor' w <> 0 /\ reachable_in sadj (SZ.v n) (SZ.v source) w k ==>
  Seq.index sdist' w <= k)
```
