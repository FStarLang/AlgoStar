# MST Theory — Cut Property (CLRS §23.1)

## Overview

This is **not an algorithm implementation** — it is the theoretical foundation
for Chapters 23's MST algorithms. It formalizes graph definitions, spanning
trees, minimum spanning trees, cuts, light edges, and the **Cut Property**
(CLRS Theorem 23.1). Both Kruskal and Prim rely on this module.

## Key Definitions

### `edge`, `graph` (from `CLRS.Ch23.MST.Spec`)

```fstar
noeq type edge = {
  u: nat;
  v: nat;
  w: int;
}

noeq type graph = {
  n: nat;  // number of vertices
  edges: list edge;
}
```

Edges are undirected: `edge_eq` treats `{u;v;w}` and `{v;u;w}` as equal.

### `is_spanning_tree` (from `CLRS.Ch23.MST.Spec`)

```fstar
let is_spanning_tree (g: graph) (es: list edge) : prop =
  g.n > 0 /\
  subset_edges es g.edges /\
  length es = g.n - 1 /\
  all_connected g.n es /\
  acyclic g.n es
```

A spanning tree must: (1) have positive vertex count, (2) use only graph edges,
(3) have exactly `n−1` edges, (4) connect all vertices to vertex 0, and
(5) be acyclic. This is a **complete characterization** — the `n−1` edge count
combined with connectivity and acyclicity is the standard tree equivalence.

### `is_mst` (from `CLRS.Ch23.MST.Spec`)

```fstar
let is_mst (g: graph) (mst: list edge) : prop =
  is_spanning_tree g mst /\
  (forall (t: list edge). 
    is_spanning_tree g t ==> total_weight mst <= total_weight t)
```

An MST is a spanning tree with minimum total weight among all spanning trees.
This is the standard global optimality definition.

### `is_light_edge` (from `CLRS.Ch23.MST.Spec`)

```fstar
let is_light_edge (e: edge) (s: cut) (g: graph) : prop =
  mem_edge e g.edges /\
  crosses_cut e s /\
  (forall (e': edge). 
    mem_edge e' g.edges /\ crosses_cut e' s ==> e.w <= e'.w)
```

A light edge crossing cut `s` is a graph edge that crosses the cut and has
minimum weight among all cut-crossing edges.

### `respects` (from `CLRS.Ch23.MST.Spec`)

```fstar
let rec respects (a: list edge) (s: cut) : bool =
  match a with
  | [] -> true
  | e :: rest -> not (crosses_cut e s) && respects rest s
```

Edge set `a` respects cut `s` if no edge in `a` crosses the cut.

## Main Theorem: Cut Property

### `cut_property` (from `CLRS.Ch23.MST.Spec`)

```fstar
val cut_property:
  g: graph ->
  a: list edge ->
  e: edge ->
  s: cut ->
  Lemma (requires 
          (exists (t: list edge). is_mst g t /\ subset_edges a t) /\
          is_light_edge e s g /\
          respects a s /\
          e.u < g.n /\ e.v < g.n /\
          (forall (e': edge). mem_edge e' g.edges ==> e'.u < g.n /\ e'.v < g.n))
        (ensures 
          (exists (t: list edge). is_mst g t /\ subset_edges (e :: a) t))
```

**Statement:** If edge set `A` is a subset of some MST `T`, `(S, V−S)` is a
cut respecting `A`, and `e` is a light edge crossing the cut, then `A ∪ {e}`
is contained in some MST.

**Proof strategy:** Edge exchange. If `e ∈ T`, done. Otherwise, adding `e` to
`T` creates a cycle; by `lemma_cycle_crosses_cut_twice`, the cycle contains
another edge `e'` crossing the cut. Since `e` is light, `e.w ≤ e'.w`. Swapping
`e'` for `e` yields a new spanning tree (`exchange_is_spanning_tree`) with
weight ≤ T's weight, hence an MST (`lemma_exchange_preserves_mst`).

## Supporting Theorems

### Edge Exchange

* `lemma_exchange_preserves_mst`: Swapping `e_add` for `e_rem` in an MST
  (when `e_add.w ≤ e_rem.w`) produces an MST or equal-weight spanning tree.

* `exchange_is_spanning_tree`: Adding `e_add` and removing `e_rem` from a
  spanning tree preserves the spanning tree property when `e_rem` lies on
  the unique path between `e_add`'s endpoints.

### Cycle and Path Theory

* `cycle_must_use_e`: A simple cycle in `e :: t` must use `e` if `t` is acyclic.
* `lemma_cycle_crosses_cut_twice`: A cycle containing a cut-crossing edge must
  contain at least one other cut-crossing edge.
* `acyclic_when_unreachable`: Adding edge `e` to acyclic `t` preserves
  acyclicity when `e`'s endpoints are disconnected in `t`.
* `lemma_adding_edge_creates_cycle`: If adding `e` to acyclic `t` breaks
  acyclicity, then `e`'s endpoints were already connected.

### Graph Infrastructure

* `acyclic_connected_length`: Acyclic + connected ⟹ exactly `n−1` edges.
* `reachable_symmetric`, `reachable_transitive`: Reachability is an
  equivalence relation (reflexivity is immediate from empty path).
* `reachable_simple`: Any reachability witness can be refined to a simple
  (edge-distinct) path.

## What Is Proven

The **full cut property** (CLRS Theorem 23.1) is mechanically verified. This
is the foundational theorem underpinning both Kruskal's and Prim's correctness.
The proof requires ~50 supporting lemmas covering path manipulation, cycle
detection, edge exchange, and weight arithmetic.

**Zero admits, zero assumes.** All proof obligations in `CLRS.Ch23.MST.Spec.fst`
are discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Undirected graphs only.** Edges are unordered pairs (`edge_eq` is
   symmetric). Directed MST (minimum spanning arborescence) is not modeled.

2. **Connectivity via vertex 0.** `all_connected` requires all vertices to be
   reachable from vertex 0 specifically. This is equivalent to full connectivity
   for undirected graphs but is an asymmetric definition.

3. **List-based edge sets.** Edges are `list edge`, not a set type. Duplicate
   edges are possible. The `all_edges_distinct` predicate is used where needed
   but is not enforced globally.

4. ~~**No MST existence proof.**~~ **RESOLVED.** The new module
   `CLRS.Ch23.MST.Existence` proves both `spanning_tree_exists` and
   `mst_exists` for connected graphs with valid edges. The spanning tree
   existence follows from the strengthened `theorem_kruskal_produces_spanning_tree`
   (which no longer requires MST existence). MST existence uses weight-based
   strong induction. Zero admits, zero assumes.

5. **Weight type is `int`.** Edge weights are signed integers. Negative weights
   are permitted, which is unusual for MST but mathematically valid.

## Files

| File | Role |
|------|------|
| `CLRS.Ch23.MST.Spec.fsti` | All definitions, lemma signatures, cut property statement |
| `CLRS.Ch23.MST.Spec.fst` | All proofs (~95 KB) |
| `CLRS.Ch23.MST.Existence.fsti` | MST existence theorem: `spanning_tree_exists`, `mst_exists` |
| `CLRS.Ch23.MST.Existence.fst` | MST existence proofs (weight-based strong induction) |
| `CLRS.Ch23.MST.Complexity.fsti` | Asymptotic complexity signatures for Kruskal/Prim |
| `CLRS.Ch23.MST.Complexity.fst` | Complexity proofs: Kruskal O(V³), Prim O(V²) |
