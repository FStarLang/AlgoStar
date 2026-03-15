# Kruskal's MST Algorithm (CLRS §23.2)

## Top-Level Signature

Here is the top-level signature proven about Kruskal's algorithm in
`CLRS.Ch23.Kruskal.Impl.fsti`:

```fstar
fn kruskal
  (adj: A.array int)
  (#p: perm) (#sadj: Ghost.erased (Seq.seq int))
  (edge_u edge_v: A.array int)
  (#sedge_u #sedge_v: Ghost.erased (Seq.seq int))
  (edge_count: R.ref SZ.t)
  (n: SZ.t)
  requires
    A.pts_to adj #p sadj **
    A.pts_to edge_u sedge_u **
    A.pts_to edge_v sedge_v **
    R.pts_to edge_count 0sz **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sedge_u == SZ.v n /\
      Seq.length sedge_v == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _: unit
  ensures exists* vec sedge_u' sedge_v'.
    A.pts_to adj #p sadj **
    A.pts_to edge_u sedge_u' **
    A.pts_to edge_v sedge_v' **
    R.pts_to edge_count vec **
    pure (result_is_forest_adj sadj sedge_u' sedge_v' (SZ.v n) (SZ.v vec))
```

### Parameters

* `adj` is a flat `n×n` adjacency matrix (read-only, borrowed via fractional
  permission `#p`). Ghost variable `sadj` captures its contents.

* `edge_u`, `edge_v` are output arrays for the selected edge endpoints.

* `edge_count` is a mutable reference tracking how many edges were selected.

* `n` is the number of vertices, of type `SZ.t`.

### Preconditions

* `SZ.v n > 0`: At least one vertex.
* `Seq.length sadj == SZ.v n * SZ.v n`: Adjacency matrix is properly sized.
* `Seq.length sedge_u == SZ.v n` and `Seq.length sedge_v == SZ.v n`: Output
  arrays can hold up to `n` edges (a tree has `n−1`).
* `SZ.fits (SZ.v n * SZ.v n)`: No `SZ.t` overflow.

### Postcondition

The `ensures` clause states that there exist final sequences `sedge_u'`,
`sedge_v'` and edge count `vec` such that:

* `result_is_forest_adj sadj sedge_u' sedge_v' (SZ.v n) (SZ.v vec)` — The
  selected edges form a forest and each edge corresponds to a positive entry
  in the adjacency matrix.

## Auxiliary Definitions

### `result_is_forest_adj` (from `CLRS.Ch23.Kruskal.Impl`)

```fstar
val result_is_forest_adj (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat) : prop
```

This is an opaque `val` combining two properties:
* `result_is_forest seu sev n ec` — the selected edges form a forest (acyclic).
* `edges_adj_pos sadj seu sev n ec` — each selected edge has a positive entry
  in the adjacency matrix (edges come from the input graph).

### `is_forest` (from `CLRS.Ch23.Kruskal.Components`)

```fstar
let is_forest (edges: list edge) (n: nat) : prop =
  acyclic n edges
```

A forest is an acyclic edge set, using `acyclic` from `CLRS.Ch23.MST.Spec`.

### `pure_kruskal` (from `CLRS.Ch23.Kruskal.Spec`)

```fstar
let pure_kruskal (g: graph) : list edge =
  let sorted = sort_edges g.edges in
  kruskal_process sorted [] g.n
```

The pure functional specification: sort edges by weight, then greedily add
each edge that doesn't create a cycle.

### `theorem_kruskal_produces_mst` (from `CLRS.Ch23.Kruskal.Spec`)

```fstar
val theorem_kruskal_produces_mst (g: graph)
  : Lemma (requires g.n > 0 /\
                    all_connected g.n g.edges /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v) /\
                    (exists (mst: list edge). is_mst g mst))
          (ensures is_mst g (pure_kruskal g))
```

The pure spec is proven to produce an MST. This is the strongest possible
correctness statement for the functional algorithm.

## MST Bridging

### `kruskal_result_is_mst` (from `CLRS.Ch23.Kruskal.Impl`)

```fstar
val kruskal_result_is_mst
    (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires
      n > 0 /\ Seq.length sadj == n * n /\
      ec <= Seq.length seu /\ ec <= Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
                                    Seq.index seu k < n /\ Seq.index sev k < n) /\
      result_is_forest_adj sadj seu sev n ec /\
      symmetric_adj sadj n /\
      no_self_loops_adj sadj n /\
      is_spanning_tree (adj_array_to_graph sadj n) (weighted_edges_from_arrays sadj seu sev n ec 0) /\
      (exists (t: list edge). is_mst (adj_array_to_graph sadj n) t /\
        subset_edges (weighted_edges_from_arrays sadj seu sev n ec 0) t) /\
      Bridge.noRepeats_edge (weighted_edges_from_arrays sadj seu sev n ec 0) /\
      (forall (e: edge). mem_edge e (adj_array_to_graph sadj n).edges ==>
        e.u < n /\ e.v < n /\ e.u <> e.v))
    (ensures
      is_mst (adj_array_to_graph sadj n) (weighted_edges_from_arrays sadj seu sev n ec 0))
```

This is the **end-to-end MST theorem** for the imperative implementation. It
requires substantial preconditions beyond what `kruskal` alone proves — the
caller must establish that the result is a spanning tree, is safe (subset of
some MST), and has no duplicate edges. The bridge uses
`Bridge.safe_spanning_tree_is_mst`.

### `greedy_step_safe` (from `CLRS.Ch23.Kruskal.Bridge`)

```fstar
val greedy_step_safe (g: graph) (forest: list edge) (e: edge)
  : Lemma
    (requires
      g.n > 0 /\
      (forall (e': edge). mem_edge e' g.edges ==> e'.u < g.n /\ e'.v < g.n) /\
      (exists (t: list edge). is_mst g t /\ subset_edges forest t) /\
      mem_edge e g.edges /\
      e.u < g.n /\ e.v < g.n /\
      ~(reachable forest e.u e.v) /\
      (forall (e': edge). mem_edge e' g.edges ==>
        e'.u < g.n /\ e'.v < g.n ==>
        ~(reachable forest e'.u e'.v) ==>
        e.w <= e'.w))
    (ensures
      (exists (t: list edge). is_mst g t /\ subset_edges (e :: forest) t))
```

Each greedy step preserves safety via the cut property: define the cut as
"vertices reachable from `e.u` in the current forest". The minimum-weight
cross-component edge is a light edge for this cut.

### Union-Find (`CLRS.Ch23.Kruskal.UF`)

```fstar
let uf_inv (sparent: Seq.seq SZ.t) (edges: list edge) (n: nat) (ec: nat) : prop =
  valid_parents sparent n /\ ec < n /\
  (forall (v: nat). v < n ==> find_pure sparent v n n < n) /\
  (forall (v: nat). v < n ==>
    SZ.v (Seq.index sparent (find_pure sparent v n n)) = find_pure sparent v n n) /\
  (forall (v: nat). v < n ==> find_pure sparent v ec n = find_pure sparent v n n) /\
  (forall (u v: nat). u < n /\ v < n /\ reachable edges u v ==>
    find_pure sparent u n n = find_pure sparent v n n)
```

The union-find invariant ties the parent array to edge-list reachability:
connected vertices have the same root. Key lemmas:
* `uf_inv_init`: Identity parent establishes initial invariant.
* `uf_inv_union`: Union preserves invariant when adding a cross-component edge.
* `uf_inv_unreachable`: Different roots ⟹ not reachable (soundness).

## What Is Proven

1. **Pure correctness:** `pure_kruskal` produces an MST
   (`theorem_kruskal_produces_mst`). This is the strongest possible result.

2. **Imperative forest:** The Pulse `kruskal` function produces a forest whose
   edges come from the adjacency matrix (`result_is_forest_adj`).

3. **Bridge to MST:** `kruskal_result_is_mst` proves the imperative result is
   an MST, given additional preconditions about spanning and safety.

4. **Cut property link:** `greedy_step_safe` connects each greedy step to the
   cut property (CLRS Theorem 23.1).

5. **Union-find correctness:** `uf_inv_union` and `uf_inv_unreachable` prove
   the union-find correctly tracks connected components.

**Zero admits, zero assumes** across `Impl.fst`, `Spec.fst`, `Bridge.fst`,
`UF.fst`, `Components.fst`, `Helpers.fst`, `EdgeSorting.fst`, `SortedEdges.fst`,
and `Lemmas.fst`.

## Specification Gaps and Limitations

1. **Imperative postcondition is weak.** The `kruskal` function only proves
   `result_is_forest_adj` — it does not directly prove `is_spanning_tree` or
   `is_mst`. The full MST result requires calling `kruskal_result_is_mst` with
   additional preconditions (spanning, safety, no duplicates) that are not
   established by the Pulse function alone.

2. **Bridge preconditions are heavy.** `kruskal_result_is_mst` requires the
   caller to provide: `symmetric_adj`, `no_self_loops_adj`, `is_spanning_tree`,
   `subset_edges ... t` for some MST `t`, and `noRepeats_edge`. These are
   reasonable but not all automatically discharged.

3. ~~**MST existence assumed.**~~ **PARTIALLY RESOLVED.**
   `theorem_kruskal_produces_spanning_tree` no longer requires MST existence
   (it now uses `acyclic_connected_length` directly for the edge count).
   `theorem_kruskal_produces_mst` and `greedy_step_safe` still require MST
   existence as a precondition, but this is now dischargeable via
   `CLRS.Ch23.MST.Existence.mst_exists`.

4. **Complexity not linked to implementation.** The complexity module
   (`Kruskal.Complexity`) is explicitly **disconnected** from `Kruskal.Impl` —
   it re-implements Kruskal from scratch with ghost tick counters and only
   proves `valid_endpoints` and `complexity_bounded_kruskal`, not forest/MST
   properties.

5. **Adjacency matrix representation only.** The implementation uses a flat
   `n×n` array. No edge-list or adjacency-list variant is provided.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Operations | O(V³) = 4·V³ | ⚠️ Separate module | Upper bound only |

The complexity bound `cf - c0 ≤ 4·V³` is proven in `Kruskal.Complexity.fsti`
but is **not connected** to the main `Kruskal.Impl` — it uses a separate
reimplementation. The `MST.Complexity` module also proves `kruskal_iterations v
≤ v * v * v` algebraically.

## Proof Structure

The proof has three layers:

1. **Pure spec layer** (`Kruskal.Spec`): Defines `pure_kruskal` = sort + greedy
   process. Proves it produces a spanning tree and MST using induction over
   sorted edges and the cut property.

2. **Imperative layer** (`Kruskal.Impl`): Pulse implementation with union-find.
   Maintains `uf_inv` linking the parent array to the evolving forest. Proves
   `result_is_forest_adj` as the postcondition.

3. **Bridge layer** (`Kruskal.Bridge`): `greedy_step_safe` (cut property per
   step) and `safe_spanning_tree_is_mst` (safe spanning tree = MST) connect the
   imperative result to MST correctness.

## Files

| File | Role |
|------|------|
| `CLRS.Ch23.Kruskal.Impl.fsti` | Public interface (this signature) |
| `CLRS.Ch23.Kruskal.Impl.fst` | Pulse implementation |
| `CLRS.Ch23.Kruskal.Spec.fsti` | Pure spec: `pure_kruskal`, `theorem_kruskal_produces_mst` |
| `CLRS.Ch23.Kruskal.Spec.fst` | Pure spec proofs |
| `CLRS.Ch23.Kruskal.Bridge.fsti` | `greedy_step_safe`, `safe_spanning_tree_is_mst` |
| `CLRS.Ch23.Kruskal.Bridge.fst` | Bridge proofs |
| `CLRS.Ch23.Kruskal.UF.fsti` | Union-find invariant and lemmas |
| `CLRS.Ch23.Kruskal.UF.fst` | Union-find proofs |
| `CLRS.Ch23.Kruskal.Components.fst` | BFS reachability, `is_forest`, `same_component` |
| `CLRS.Ch23.Kruskal.Helpers.fst` | Forest invariant maintenance |
| `CLRS.Ch23.Kruskal.EdgeSorting.fst` | Sort permutation, weight independence |
| `CLRS.Ch23.Kruskal.SortedEdges.fst` | Kruskal over pre-sorted input |
| `CLRS.Ch23.Kruskal.Lemmas.fsti` | Façade re-exporting key lemma signatures |
| `CLRS.Ch23.Kruskal.Lemmas.fst` | Lemma proof delegations |
| `CLRS.Ch23.Kruskal.Complexity.fsti` | Complexity interface (disconnected) |
| `CLRS.Ch23.Kruskal.Complexity.fst` | Complexity proofs (disconnected) |
| `CLRS.Ch23.MST.Spec.fsti` | Graph defs, cut property, MST defs |
