# Dijkstra's Single-Source Shortest Paths (CLRS §24.3)

## Top-Level Signature

Here is the top-level signature proven about Dijkstra in
`CLRS.Ch24.Dijkstra.Impl.fsti`:

```fstar
fn dijkstra
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (pred: A.array SZ.t)
  (ctr: GR.ref nat)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#spred: erased (Seq.seq SZ.t))
  (#c0: erased nat)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    A.pts_to pred spred **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length spred == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      all_weights_non_negative sweights /\
      weights_in_range sweights (SZ.v n)
    )
  ensures exists* sdist' spred' (cf: nat).
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    A.pts_to pred spred' **
    GR.pts_to ctr cf **
    pure (
      Seq.length sdist' == SZ.v n /\
      (forall (v: nat). v < SZ.v n ==>
        Seq.index sdist' v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v) /\
      shortest_path_tree spred' sweights (SZ.v n) (SZ.v source) /\
      dijkstra_complexity_bounded cf (reveal c0) (SZ.v n)
    )
```

### Parameters

* `weights` is a flat adjacency-matrix representation (n×n row-major array).
  Edge weight `w(u,v)` is stored at index `u*n + v`. The sentinel value
  `SP.inf` represents no edge / infinity. All weights must be non-negative.

* `n` is the number of vertices (machine-sized `SZ.t`, must be > 0).

* `source` is the source vertex index (must be < n).

* `dist` is a mutable output array of size n. On return, `dist[v]` holds the
  shortest-path distance `δ(s,v)` from `source` to `v`.

* `pred` is a mutable output array of size n. On return, `pred[v]` encodes
  the predecessor of `v` on a shortest path from `source` — the
  shortest-path tree (CLRS's π array).

* `ctr` is a ghost counter for complexity tracking. Ghost values are erased at
  runtime — zero overhead.

### Preconditions

* `SZ.v n > 0`: At least one vertex.
* `SZ.v source < SZ.v n`: Source is a valid vertex.
* `Seq.length sweights == SZ.v n * SZ.v n`: Weight matrix is n×n.
* `Seq.length sdist == SZ.v n`: Distance array has n entries.
* `Seq.length spred == SZ.v n`: Predecessor array has n entries.
* `SZ.fits (SZ.v n * SZ.v n)`: n² fits in machine-sized integers.
* `all_weights_non_negative sweights`: All edge weights ≥ 0 (Dijkstra requirement).
* `weights_in_range sweights (SZ.v n)`: Each finite weight `w` satisfies
  `w*(n-1) < inf`, ensuring representability.

### Postcondition

The `ensures` clause guarantees:

* **Shortest-path equality**: `dist[v] == sp_dist(source, v)` for all v —
  the strongest possible correctness property.

* **Shortest-path tree**: `pred` encodes a shortest-path tree:
  - `pred[source] == source`
  - For reachable v ≠ source: `sp_dist(s,v) == sp_dist(s, pred[v]) + w(pred[v], v)`

* **Unreachability**: `sp_dist(s,v) == inf` implies no valid path from source
  to v exists (proven via `sp_dist_inf_means_unreachable`).

* **O(V²) complexity**: `dijkstra_complexity_bounded cf c0 n`.

## Auxiliary Definitions

### `shortest_path_tree` (from `Dijkstra.Impl.fsti`)

```fstar
let shortest_path_tree (spred: Seq.seq SZ.t) (sweights: Seq.seq int)
  (n source: nat) : prop =
  Seq.length spred == n /\
  source < n /\
  SZ.v (Seq.index spred source) == source /\
  (forall (v: nat). v < n /\ v <> source /\ SP.sp_dist sweights n source v < SP.inf ==>
    (let p = SZ.v (Seq.index spred v) in
     p < n /\
     SP.sp_dist sweights n source v ==
       SP.sp_dist sweights n source p + Seq.index sweights (p * n + v)))
```

States that `pred` encodes actual shortest-path predecessors — for every
reachable vertex v ≠ source, following `pred[v]` yields a vertex whose
distance plus the connecting edge weight equals `δ(s,v)`.

### `pred_consistent` (from `Dijkstra.fst`)

```fstar
let pred_consistent (spred: Seq.seq SZ.t) (sdist sweights: Seq.seq int) (n source: nat) : prop =
  ...
  (forall (v: nat). v < n /\ v <> source /\ Seq.index sdist v < SP.inf ==>
    (let p = SZ.v (Seq.index spred v) in
     p < n /\
     Seq.index sdist v == Seq.index sdist p + Seq.index sweights (p * n + v)))
```

The weaker internal invariant: relates pred to the `dist` array rather than
to `sp_dist`. The wrapper `Dijkstra.Impl.fst` chains
`pred_consistent + (dist == sp_dist) ⟹ shortest_path_tree`.

### `all_weights_non_negative`

```fstar
let all_weights_non_negative (sweights: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sweights ==> Seq.index sweights i >= 0
```

### `dijkstra_complexity_bounded`

```fstar
let dijkstra_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == dijkstra_iterations n   -- where dijkstra_iterations n = n + 2n²
```

The ghost counter proves exactly `n + 2n²` ticks, yielding O(V²).

## What Is Proven

The postcondition is the **strongest possible correctness specification** for
Dijkstra on dense graphs with non-negative weights:

1. **Shortest-path equality**: `dist[v] == δ(s,v)` for all vertices — proven by
   combining the upper bound (from triangle inequality via
   `dijkstra_sp_upper_bound`) with the lower bound (`dist_ge_sp_dist` preserved
   through relaxation rounds).

2. **CLRS Theorem 24.6** (Greedy choice): When vertex u is extracted from the
   priority queue (minimum unvisited), `dist[u] == δ(s,u)`. Proven in
   `Dijkstra.Correctness.fst` via the standard contradiction argument.

3. **Triangle inequality**: Established incrementally — `tri_from_visited` is
   maintained for all visited vertices, and when all vertices are visited, this
   becomes the full triangle inequality.

4. **Predecessor tree**: `pred[v]` encodes an actual shortest-path tree, with
   unreachability proven separately.

5. **O(V²) complexity**: Exact tick count `n + 2n²` proven via ghost counter.
   Uses linear-scan EXTRACT-MIN (no priority queue), matching the array-based
   Dijkstra in CLRS.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F* and Z3.

## Specification Gaps and Limitations

1. **Adjacency matrix only.** Uses a flat n×n array, giving O(V²) complexity.
   With a binary heap and adjacency lists, CLRS achieves O((V+E) log V). This
   would require a verified priority queue data structure.

2. **Sentinel value.** Same as Bellman-Ford — the `weights_in_range` constraint
   is a precondition, not checked at runtime.

3. **No shortest-path reconstruction.** While `pred` encodes the tree, there is
   no verified function to reconstruct an explicit path from `pred`. The
   `shortest_path_tree` postcondition proves the structural property but not
   path extraction.

## Profiling (2026-03-16)

| File | Verification Time | Z3 Options |
|------|-------------------|------------|
| **`Dijkstra.fst`** | **~187s** | `--z3rlimit 120 --split_queries always` (max, `dijkstra_relax_round`) |
| `Dijkstra.TriangleInequality.fst` | ~4s | varies per lemma (max rlimit 60) |
| `Dijkstra.Impl.fst` | ~4s | `--z3rlimit 20` |
| `Dijkstra.Complexity.fst` | ~4s | defaults |
| `Dijkstra.Correctness.fst` | ~2s | `--z3rlimit 50` (max) |
| `Dijkstra.Lemmas.fst` | ~1s | defaults |
| `ShortestPath.Spec.fst` | ~6s | `--z3rlimit 60` (max) |
| `ShortestPath.Triangle.fst` | ~37s | `--z3rlimit 100` (max for `chain_B_property`) |

**Bottleneck:** `Dijkstra.fst` at **~187s** dominates the entire chapter's
verification time. The `dijkstra_relax_round` function requires `--z3rlimit 120
--split_queries always` and has a complex loop invariant with ~20 conjuncts
spanning the relax loop, bridge lemma applications, and ghost invariant
maintenance. The main `dijkstra` function adds another `--z3rlimit 60
--split_queries always` scope.

## Complexity

| Metric | Exact Count | Asymptotic | Linked? |
|--------|-------------|------------|---------|
| Iterations | n + 2n² | O(V²) ≤ 3n² | ✅ Ghost counter in `Dijkstra.fst` |

Breakdown: n ticks for initialization, n iterations × (n ticks find-min + n
ticks relax) = n + 2n² total.

## Proof Structure

### Architecture

The implementation splits across two files for SMT tractability:

* **`Dijkstra.fst`** — Core implementation: `find_min_unvisited` helper +
  `dijkstra_relax_round` helper + `fn dijkstra` main function. Contains all
  ghost invariants, bridge lemmas, and `count_ones` utilities.

* **`Dijkstra.Impl.fst`** — Thin re-export wrapper that calls `D.dijkstra`
  and strengthens the postcondition from `pred_consistent` (relates pred to
  dist) to `shortest_path_tree` (relates pred to sp_dist directly).

The inner relax loop is extracted into `dijkstra_relax_round` to give it its
own Pulse elaboration scope, keeping SMT queries tractable. This works around
a Pulse nested-loop scalability issue where adding existentials to outer-loop
invariants causes inner-loop SMT blowup.

### Main Loop Invariants

The outer loop maintains:
- `tri_from_visited`: Triangle inequality for edges from visited vertices
- `visited_le_unvisited`: Visited vertices have smaller distances
- `dist_ge_sp_dist`: No underestimates (lower bound)
- `pred_ok`: Predecessor consistency + predecessors are visited
- `count_ones == round`: Exactly `round` vertices have been visited
- Ghost tick tracking: `vc == c0 + n + 2 * round * n`

### Key Correctness Chain

1. `find_min_unvisited` → selects u with min dist among unvisited
2. Mark u as visited → `count_ones_mark`
3. `dijkstra_relax_round` → relax all (u,v) edges, update pred
4. `extend_tri_after_relax` → extend triangle inequality to include u
5. `relax_round_lb_post` → preserve lower bound
6. `relax_round_pred_ok` → preserve predecessor consistency
7. After n rounds: `count_ones_full` → all visited → `all_visited_tri_is_full`
8. `dijkstra_sp_upper_bound` → triangle ineq + dist[s]=0 → upper bound
9. Upper bound + lower bound → equality

## Key Lemmas

* `greedy_choice_invariant` (Dijkstra.Correctness): CLRS Theorem 24.6 — when u
  is extracted, dist[u] = δ(s,u).
* `extend_tri_after_relax`: After relaxation from u, triangle inequality extends
  to include u and visited-ordering is preserved.
* `relax_round_pred_ok`: Predecessor consistency is preserved through relaxation.
* `dijkstra_sp_upper_bound`: Triangle inequality + dist[source]=0 → upper bound.
* `pred_consistent_implies_spt`: pred_consistent + dist==sp_dist → shortest_path_tree.
* `sp_dist_inf_means_unreachable`: sp_dist==inf → no valid path exists.

## Files

| File | Role |
|------|------|
| `CLRS.Ch24.Dijkstra.Impl.fsti` | **Public interface** (this signature) |
| `CLRS.Ch24.Dijkstra.Impl.fst` | Wrapper: strengthens pred_consistent → shortest_path_tree |
| `CLRS.Ch24.Dijkstra.fst` | Core Pulse implementation (fused correctness + complexity + pred) |
| `CLRS.Ch24.Dijkstra.Spec.fst` | Re-exports shared `ShortestPath.Spec` definitions |
| `CLRS.Ch24.Dijkstra.Correctness.fst/fsti` | Greedy-choice property (CLRS Thm 24.6) |
| `CLRS.Ch24.Dijkstra.TriangleInequality.fst/fsti` | Processing all vertices ⇒ triangle inequality |
| `CLRS.Ch24.Dijkstra.Lemmas.fst/fsti` | Re-export interface for all Dijkstra lemmas |
| `CLRS.Ch24.Dijkstra.Complexity.fst/fsti` | Re-exports complexity bounds from `Dijkstra.fst` |
| `CLRS.Ch24.ShortestPath.Spec.fst` | Shared spec: `sp_dist_k`, `sp_dist`, triangle ineq theorem |
| `CLRS.Ch24.ShortestPath.Triangle.fst` | Shared: `sp_dist_k` stabilization, `sp_dist` triangle ineq |
| `CLRS.Ch24.ShortestPath.Inf.fst/fsti` | Abstract infinity sentinel |

## Priority Checklist

Items in priority order for reaching a fully proven, high-quality implementation:

- [x] Zero admits, zero assumes — fully proven
- [x] Rubric-conformant file structure (Spec, Lemmas, Impl, Complexity split)
- [x] Public interface (`Impl.fsti`) with full postcondition
- [x] Shortest-path equality (dist[v] == sp_dist(v)) proven
- [x] CLRS Theorem 24.6 (greedy choice) proven
- [x] Predecessor tree output with `shortest_path_tree` postcondition
- [x] Unreachability proven (`sp_dist_inf_means_unreachable`)
- [x] Complexity bound proven and linked via ghost counter
- [x] `weights_in_range` precondition with sentinel soundness proof
- [x] Tight interface files hiding internal lemmas
- [x] Inner relax loop extracted for SMT tractability
- [x] Profiling data recorded (2026-03-16)
- [ ] **Reduce Dijkstra.fst verification time** (~144-187s) — the dominant
      bottleneck for the entire chapter; `dijkstra_relax_round` at z3rlimit 120
      with split_queries always is the main cost. Attempted optimizations:
      - z3rlimit 80: invariant re-establishment fails
      - z3rlimit 100: invariant re-establishment fails
      - Helper assertions (new_dist bounds): no improvement / regression
      - z3rlimit 120 is genuinely tight; future work should consider:
        - Factoring the ~20-conjunct invariant into a named predicate
        - Splitting the bridge lemma applications into a separate `ghost fn`
        - Profiling individual query times with `--log_queries`
- [ ] **Reduce ShortestPath.Triangle.fst verification time** (~37s) — shared
      dependency; `chain_B_property` at z3rlimit 100
- [ ] **Extract count_ones utilities** — `Dijkstra.fst` contains ~50 lines of
      `count_ones` utilities noted as "also available in CLRS.Common.CountOnes";
      consider importing from the common module to reduce duplication
- [ ] **Priority queue variant** — implement O((V+E) log V) with binary heap
