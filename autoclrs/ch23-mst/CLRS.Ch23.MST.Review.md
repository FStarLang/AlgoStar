# MST Theory — Cut Property (CLRS §23.1)

**Last reviewed**: 2026-03-16

## Overview

This is **not an algorithm implementation** — it is the theoretical foundation
for Chapter 23's MST algorithms. It formalizes graph definitions, spanning
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

### MST Existence (`CLRS.Ch23.MST.Existence`)

* `spanning_tree_exists`: Every connected graph with valid edges has a spanning
  tree. Follows from the strengthened `theorem_kruskal_produces_spanning_tree`.
* `mst_exists`: Every connected graph with valid edges has a minimum spanning
  tree. Uses weight-based strong induction over spanning trees.

## What Is Proven

The **full cut property** (CLRS Theorem 23.1) is mechanically verified. This
is the foundational theorem underpinning both Kruskal's and Prim's correctness.
The proof requires ~50 supporting lemmas covering path manipulation, cycle
detection, edge exchange, and weight arithmetic.

**MST existence** is fully proven: `mst_exists` shows every connected graph
with valid edges has an MST, closing the key gap that previously required MST
existence as a precondition.

**Zero admits, zero assumes.** All proof obligations in `CLRS.Ch23.MST.Spec.fst`,
`CLRS.Ch23.MST.Existence.fst`, and `CLRS.Ch23.MST.Complexity.fst` are
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Undirected graphs only.** Edges are unordered pairs (`edge_eq` is
   symmetric). Directed MST (minimum spanning arborescence) is not modeled.

2. **Connectivity via vertex 0.** `all_connected` requires all vertices to be
   reachable from vertex 0 specifically. This is equivalent to full connectivity
   for undirected graphs but is an asymmetric definition.

3. **List-based edge sets.** Edges are `list edge`, not a set type. Duplicate
   edges are possible. The `all_edges_distinct` predicate is used where needed
   but is not enforced globally.

4. **Weight type is `int`.** Edge weights are signed integers. Negative weights
   are permitted, which is unusual for MST but mathematically valid.

## Profiling & Proof Stability

| File | Size | Checked size | Max z3rlimit | Notes |
|------|------|-------------|-------------|-------|
| `MST.Spec.fst` | 2212 lines | 2467 KB | 400 | Largest file; `cut_property` proof at rlimit 400 |
| `MST.Spec.fsti` | 458 lines | 439 KB | — | Interface only |
| `MST.Existence.fst` | 215 lines | 217 KB | 80 | Clean, moderate rlimits |
| `MST.Complexity.fst` | 102 lines | 65 KB | — | Arithmetic only, fast |

**Stability concerns:**
- `MST.Spec.fst` line 2053: `z3rlimit 400` for `cut_property` — high but
  stable (the core exchange argument is complex). Consider `--split_queries`
  to improve resilience.
- `MST.Spec.fst` line 2185: `z3rlimit 200` for `exchange_is_spanning_tree` —
  moderately high.
- All other lemmas use rlimit ≤ 100.

## Checklist

- [x] Cut property (Theorem 23.1) fully proven
- [x] MST existence proven (`mst_exists`)
- [x] Spanning tree existence proven (`spanning_tree_exists`)
- [x] Edge exchange argument verified
- [x] Graph infrastructure lemmas (reachability, acyclicity, paths)
- [x] Zero admits / zero assumes
- [x] Complexity bounds proven (algebraic: Kruskal O(V³), Prim O(V²))
- [ ] Reduce z3rlimit 400 in `cut_property` proof (stability)
- [ ] Reduce z3rlimit 200 in `exchange_is_spanning_tree` (stability)

## Files

| File | Role |
|------|------|
| `CLRS.Ch23.MST.Spec.fsti` | All definitions, lemma signatures, cut property statement |
| `CLRS.Ch23.MST.Spec.fst` | All proofs (~95 KB, 2212 lines) |
| `CLRS.Ch23.MST.Existence.fsti` | MST existence theorem: `spanning_tree_exists`, `mst_exists` |
| `CLRS.Ch23.MST.Existence.fst` | MST existence proofs (weight-based strong induction) |
| `CLRS.Ch23.MST.Complexity.fsti` | Asymptotic complexity signatures for Kruskal/Prim |
| `CLRS.Ch23.MST.Complexity.fst` | Complexity proofs: Kruskal O(V³), Prim O(V²) |
