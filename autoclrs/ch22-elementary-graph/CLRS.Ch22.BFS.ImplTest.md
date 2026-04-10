# CLRS.Ch22.BFS.ImplTest — Spec Validation Report

**Date:** 2026-03-17
**Status:** ✅ Verified (zero admits, zero assumes)
**Concrete Execution:** ✅ Extracted to C, compiled, and executed successfully (latest: 2026-04-10)

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
| **Predecessor distance consistency** | ✅ | NEW: `dist[v] = dist[pred[v]] + 1` from postcondition |

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

### Predecessor Distance Consistency (NEW)

The strengthened BFS postcondition now includes:
```
∀v. v < n ∧ scolor'[v] ≠ 0 ∧ spred'[v] ≥ 0 ∧ spred'[v] < n ⟹
  scolor'[spred'[v]] ≠ 0 ∧ sdist'[v] == sdist'[spred'[v]] + 1
```

This says the BFS predecessor tree has consistent distances: each vertex's
distance is exactly one more than its predecessor's. This provides an
alternative way to verify distance relationships through the predecessor
chain, complementing the reachability-based proofs.

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
**not** exposed through `BFS.Impl.fsti`. Adding it to the Impl interface would
require threading a queue-ordering invariant through the BFS loop — a
significant proof engineering task.

### Why Distance Precision Succeeds for This Test

For our specific graph (linear chain 0→1→2), each vertex has a **unique**
path from source 0. The `reachable_in` predicate determines a unique path
length, so the postcondition IS precise enough to determine exact distances.

For graphs with **multiple paths**, the predecessor distance consistency
postcondition provides additional constraints that help determine distances
(through the BFS tree structure), even without full shortest-path optimality.

## Concrete Execution Results (2026-03-22)

The BFS test was extracted to C via KaRaMeL and executed:

```
$ make test
Ch22 ImplTest: running BFS, DFS, TopologicalSort tests...
Ch22 ImplTest: all tests passed.
```

The extracted C code:
- Allocates adjacency matrix, color, distance, predecessor, and queue arrays
- Sets edges 0→1 and 1→2 in the adjacency matrix
- Calls `queue_bfs` (the verified BFS implementation)
- Frees all allocated memory
- Completes without errors, confirming the verified algorithm runs correctly on concrete data
