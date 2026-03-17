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
| **dist[1] == 1** | ✅ | Distance uniqueness lemma + postcondition reachability |
| **dist[2] == 2** | ✅ | Distance uniqueness lemma + postcondition reachability |
| Complexity bound (`cf ≤ 2·n²`) | ✅ | Direct from postcondition |

### Distance Uniqueness Proofs

Three auxiliary lemmas prove that for our concrete graph, each vertex's
distance from source 0 is uniquely determined by the `reachable_in` predicate:

- **`lemma_only_0_steps_to_0`:** `reachable_in adj 3 0 0 k ⟹ k == 0`
  No vertex has an edge to vertex 0, so 0 is unreachable from itself in >0 steps.

- **`lemma_only_1_step_to_1`:** `reachable_in adj 3 0 1 k ⟹ k == 1`
  Only vertex 0 has an edge to 1. A k≥2 step path would require returning
  to 0 (impossible by the first lemma).

- **`lemma_only_2_steps_to_2`:** `reachable_in adj 3 0 2 k ⟹ k == 2`
  Only vertex 1 has an edge to 2. A k=1 path requires edge 0→2 (absent).
  A k≥3 path would require a path of length k-1 to vertex 1 with k-1≥2
  (impossible by the second lemma).

Combined with the postcondition's `reachable_in sadj 3 0 w (dist[w])`, these
prove `dist[0]=0, dist[1]=1, dist[2]=2` exactly.

## What Is NOT Proven

| Property | Status | Reason |
|----------|--------|--------|
| (all target properties proven) | ✅ | — |

## Spec Precision Analysis

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
**not** exposed through `BFS.Impl.fsti`.

### Why Distance Precision Succeeds for This Test

For our specific graph (linear chain 0→1→2), each vertex has a **unique**
path from source 0. The `reachable_in` predicate determines a unique path
length, so the postcondition IS precise enough to determine exact distances.

However, for graphs with **multiple paths** (e.g., 0→1 and 0→2→1), the
postcondition would admit `dist[1] = 1` or `dist[1] = 2` — it couldn't
determine the shortest-path distance.

**Impact:** The BFS spec is precise for DAGs with unique paths but imprecise
for general graphs. Adding shortest-path optimality to `BFS.Impl.fsti` would
make the spec universally precise.

**Recommendation:** Add a shortest-path postcondition clause to `BFS.Impl.fsti`:
```
// Shortest-path optimality
(forall (w: nat) (k: nat).
  w < SZ.v n /\ Seq.index scolor' w <> 0 /\ reachable_in sadj (SZ.v n) (SZ.v source) w k ==>
  Seq.index sdist' w <= k)
```
