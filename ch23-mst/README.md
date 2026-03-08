# Chapter 23: Minimum Spanning Trees — Kruskal & Prim

Verified implementations and specifications for MST algorithms from CLRS
Chapter 23 in F* and Pulse.  The formalization covers the cut property
(Theorem 23.1), Kruskal's algorithm (§23.2) with union-find, and Prim's
algorithm (§23.2) with adjacency-matrix linear-scan extract-min.

**Verification status:** All 25 source files verify with **zero admits,
zero assumes, zero `--admit_smt_queries`**.

---

## Summary Table

| Property | Status | Notes |
|---|---|---|
| Cut property (Theorem 23.1) | ✅ Fully proven | Edge-exchange argument in `MST.Spec` |
| Kruskal pure MST correctness | ✅ Fully proven | `theorem_kruskal_produces_mst` |
| Kruskal greedy bridge | ✅ Fully proven | `greedy_step_safe` + `safe_spanning_tree_is_mst` via cut property |
| Kruskal Impl forest + acyclicity | ✅ Proven | `result_is_forest` with UF invariant tracking |
| Kruskal Impl → MST | ⚠️ Gap | Bridge provides math; inner scan invariant needs strengthening |
| Prim pure MST correctness | ✅ Fully proven | `prim_spec` — edges ⊆ MST, connected, n−1 edges |
| Prim Impl `prim_correct` | ✅ Proven | key[source]=0, keys bounded, parent[source]=source |
| Prim Impl → MST | ⚠️ Gap | `prim_correct` is weak; no bridge to `prim_spec` |
| Kruskal complexity O(V³) | ✅ Proven | `kruskal_cubic` — but complexity module disconnected from Impl |
| Prim complexity O(V²) | ✅ Proven | `prim_quadratic` — but complexity module disconnected from Impl |
| Acyclic + connected → n−1 edges | ✅ Proven | `acyclic_connected_length` |
| MST existence from connectivity | ❌ Assumed | `∃ t. is_mst g t` is a precondition, not derived |
| Admits / Assumes | **0 / 0** | |

---

## File Inventory

| File | Language | Role |
|---|---|---|
| `CLRS.Ch23.MST.Spec.fsti` | F* | Graph, spanning tree, MST, cut, light edge definitions; cut property signature |
| `CLRS.Ch23.MST.Spec.fst` | F* | Full proofs: cut property (Theorem 23.1), edge exchange, path manipulation, MST existence infrastructure |
| `CLRS.Ch23.MST.Complexity.fsti` | F* | Complexity interface: `kruskal_cubic`, `prim_quadratic` |
| `CLRS.Ch23.MST.Complexity.fst` | F* | Arithmetic O(V³) Kruskal / O(V²) Prim bounds |
| `CLRS.Ch23.Kruskal.Spec.fsti` | F* | Kruskal spec interface: `pure_kruskal`, MST theorem signatures |
| `CLRS.Ch23.Kruskal.Spec.fst` | F* | Pure Kruskal: insertion sort, `pure_kruskal`, MST theorem proof |
| `CLRS.Ch23.Kruskal.Components.fst` | F* | BFS-based connected components, reachability, path properties |
| `CLRS.Ch23.Kruskal.EdgeSorting.fst` | F* | `sort_edges` permutation proof and MST weight independence |
| `CLRS.Ch23.Kruskal.SortedEdges.fst` | F* | Kruskal over sorted input: subset/forest proven |
| `CLRS.Ch23.Kruskal.UF.fsti` | F* | Union-find interface: `find_pure`, `uf_inv`, `uf_inv_union` |
| `CLRS.Ch23.Kruskal.UF.fst` | F* | Union-find correctness: soundness, completeness |
| `CLRS.Ch23.Kruskal.Helpers.fst` | F* | Forest invariant maintenance lemmas |
| `CLRS.Ch23.Kruskal.Lemmas.fsti` | F* | Lemmas façade: re-exports from Components, EdgeSorting, SortedEdges, UF |
| `CLRS.Ch23.Kruskal.Lemmas.fst` | F* | Lemmas façade module |
| `CLRS.Ch23.Kruskal.Impl.fst` | Pulse | Imperative Kruskal: adj-matrix, union-find, cross-component scan |
| `CLRS.Ch23.Kruskal.Bridge.fsti` | F* | Greedy MST bridge interface: `greedy_step_safe`, `safe_spanning_tree_is_mst` |
| `CLRS.Ch23.Kruskal.Bridge.fst` | F* | Bridge proofs: cut-property-based greedy MST correctness |
| `CLRS.Ch23.Kruskal.Complexity.fsti` | Pulse | Kruskal complexity interface: ticks ≤ 4·V³ (⚠️ disconnected from Impl) |
| `CLRS.Ch23.Kruskal.Complexity.fst` | Pulse | Ghost-tick instrumented Kruskal, proves ticks ≤ 4·V³ |
| `CLRS.Ch23.Prim.Spec.fsti` | F* | Prim spec interface: `pure_prim`, `prim_spec` |
| `CLRS.Ch23.Prim.Spec.fst` | F* | Pure Prim: adj-matrix, connectivity, safety via cut property |
| `CLRS.Ch23.Prim.Impl.fsti` | Pulse | Imperative Prim interface: `prim` function signature |
| `CLRS.Ch23.Prim.Impl.fst` | Pulse | Imperative Prim: key + parent + in_mst arrays |
| `CLRS.Ch23.Prim.Complexity.fsti` | Pulse | Prim complexity interface: ticks ≤ 3·V² (⚠️ disconnected from Impl) |
| `CLRS.Ch23.Prim.Complexity.fst` | Pulse | Ghost-tick instrumented Prim, proves ticks ≤ 3·V² |

---

## MST Theory (`MST.Spec`)

### Graph and MST Definitions

A graph is a vertex count `n` and an edge list.  Edges are undirected
(`edge_eq` treats `(u,v)` and `(v,u)` as identical):

```fstar
noeq type edge = { u: nat; v: nat; w: int; }
noeq type graph = { n: nat; edges: list edge; }
```

A spanning tree requires: (1) edges from the graph, (2) exactly `n−1`
edges, (3) all vertices reachable, and (4) acyclicity.  An MST adds
weight minimality:

```fstar
let is_spanning_tree (g: graph) (es: list edge) : prop =
  g.n > 0 /\ subset_edges es g.edges /\ length es = g.n - 1 /\
  all_connected g.n es /\ acyclic g.n es

let is_mst (g: graph) (mst: list edge) : prop =
  is_spanning_tree g mst /\
  (forall (t: list edge). is_spanning_tree g t ==> total_weight mst <= total_weight t)
```

### Cut Property (Theorem 23.1)

A *cut* partitions vertices; a *light edge* is the minimum-weight
crossing edge; a cut *respects* edge set `A` when no edge in `A`
crosses it.  The cut property theorem:

> If `A ⊆` some MST `T`, and `e` is a light edge crossing a cut that
> respects `A`, then `A ∪ {e} ⊆` some MST.

The proof uses edge exchange: if `e ∉ T`, adding `e` creates a cycle in
`T ∪ {e}` that must contain another crossing edge `e'` with
`w(e) ≤ w(e')`.  Removing `e'` yields a new spanning tree of weight ≤
`T`, hence also an MST.

This is **fully verified** with zero admits.

---

## Kruskal's Algorithm (§23.2)

### Pure Specification (`Kruskal.Spec`)

```fstar
let pure_kruskal (g: graph) : list edge =
  let sorted = sort_edges g.edges in
  kruskal_process sorted [] g.n
```

`kruskal_step` adds edge `e` to the forest if its endpoints are in
different components (checked via BFS-based `same_component_dec`).
`kruskal_process` iterates this over sorted edges.

### Correctness Theorems

```fstar
val theorem_kruskal_produces_spanning_tree (g: graph)
  : Lemma (requires g.n > 0 /\ all_connected g.n g.edges /\ ...)
          (ensures is_spanning_tree g (pure_kruskal g))

val theorem_kruskal_produces_mst (g: graph)
  : Lemma (requires g.n > 0 /\ all_connected g.n g.edges /\ ...)
          (ensures is_mst g (pure_kruskal g))
```

The MST proof uses the cut property: at each step, the current forest
defines a cut (vertices reachable from `e.u` vs. the rest), and the
lightest crossing edge is safe.

### Greedy Bridge (`Kruskal.Bridge`)

Two key lemmas bridge any greedy MST algorithm to MST correctness:

1. **`greedy_step_safe`**: Adding the min-weight cross-component edge
   to a safe forest (⊆ some MST) preserves the safe-edge property,
   using the cut property with the cut defined by the adding vertex's
   component.

2. **`safe_spanning_tree_is_mst`**: A spanning tree that is safe
   (⊆ some MST) is itself an MST.

### Union-Find for Kruskal (`Kruskal.UF`)

A separate union-find model tracks component connectivity:

```fstar
val uf_inv_union
    (sparent sparent': Seq.seq SZ.t) (edges: list edge) (n ec: nat)
    (u_val v_val root_u root_v: nat) (new_edge: edge)
  : Lemma (requires uf_inv sparent edges n ec /\ root_u <> root_v /\ ...)
          (ensures uf_inv sparent' (new_edge :: edges) n (ec + 1))
```

Key invariant: `uf_inv` relates the parent array to edge-list
reachability — `find(u) = find(v)` iff `reachable(edges, u, v)`.

### Imperative Implementation (`Kruskal.Impl`)

The Pulse implementation uses a flat `n × n` adjacency matrix and a
union-find parent array.  Each round scans all V² entries for the
minimum-weight cross-component edge.

**Postcondition:** `result_is_forest` — edge count ≤ n−1, all endpoints
valid, result forms an acyclic forest via `is_forest`.

### Strongest Guarantee (Pure Spec)

The pure `theorem_kruskal_produces_mst` is the strongest guarantee:
given a connected graph with an MST, `pure_kruskal` outputs an MST.
This covers spanning tree structure, weight minimality, and edge
subset.

### Impl → MST Gap

The imperative Kruskal proves the result is a forest but does **not**
directly prove it is an MST.  The `Kruskal.Bridge` provides the
mathematical machinery (`greedy_step_safe`), but the imperative inner
scan invariant would need strengthening to track minimum
cross-component weight per round.

---

## Prim's Algorithm (§23.2)

### Pure Specification (`Prim.Spec`)

```fstar
val pure_prim (adj: adj_matrix) (n: nat) (start: nat) : list edge

val prim_spec (adj: adj_matrix) (n: nat) (start: nat)
  : Pure (list edge)
    (requires n > 0 /\ start < n /\ well_formed_adj adj n /\ ...)
    (ensures fun result ->
      let g = adj_to_graph adj n in
      length result = n - 1 /\
      (exists (t: list edge). is_mst g t /\ subset_edges result t) /\
      all_connected n result)
```

Each step selects the minimum-weight edge from tree vertices to non-tree
vertices (CLRS Corollary 23.2).  Safety follows from the cut property
with the cut `(tree, non-tree)`.

### Imperative Implementation (`Prim.Impl`)

The Pulse implementation uses an `n × n` weight matrix stored as a
flat `SZ.t` array with 64-bit index arithmetic:

```fstar
fn prim (#p: perm) (weights: array SZ.t) (...) (n source: SZ.t)
  returns res: (V.vec SZ.t & V.vec SZ.t)
  ensures exists* (key_seq parent_seq: ...).
    pure (prim_correct key_seq parent_seq weights_seq (SZ.v n) (SZ.v source))
```

**`prim_correct` postcondition:**
- `key[source] = 0`
- All keys bounded by `infinity` (65535)
- `parent[source] = source`
- Array lengths correct

### Strongest Guarantee (Pure Spec)

The pure `prim_spec` is the strongest guarantee: result has n−1 edges,
is connected, and is a subset of some MST.

### Limitation: `prim_correct` Is Weak

**`prim_correct` does NOT directly prove the output is an MST.** It
only establishes local properties (key values, parent validity).  To
prove MST optimality from the imperative output would require:

1. Connecting the loop invariant to the pure specification's
   `prim_spec` via a bridge similar to `Kruskal.Bridge`.
2. Extracting edges via `edges_from_parent_key` and proving they
   match the cut-property argument.

This bridging is not yet implemented.

---

## Complexity

| Algorithm | Proven Bound | Module | Connected to Impl? |
|---|---|---|---|
| Kruskal (adj-matrix V²-scan) | O(V³) — `ticks ≤ 4·V³` | `Kruskal.Complexity` | ❌ Disconnected |
| Kruskal (arithmetic) | V³ — `kruskal_cubic` | `MST.Complexity` | N/A (arithmetic only) |
| Prim (adj-matrix linear extract-min) | O(V²) — `ticks ≤ 3·V²` | `Prim.Complexity` | ❌ Disconnected |
| Prim (arithmetic) | 2V² — `prim_quadratic` | `MST.Complexity` | N/A (arithmetic only) |
| Prim beats Kruskal for V ≥ 4 | ✅ | `MST.Complexity` | N/A |

The complexity modules (`Kruskal.Complexity`, `Prim.Complexity`) are
**fully verified internally** but **re-implement** the algorithms from
scratch with ghost tick counters.  They do NOT reference the main
`Impl` modules or the spec/bridge modules.

**Kruskal:** O(E lg E) is the textbook bound, equivalently O(E lg V).
With the adjacency-matrix variant (V² edges), each of V−1 rounds scans
V² entries, giving O(V³).  The proven bound is `4·V³`.

**Prim:** O(V²) with adjacency matrix and linear-scan extract-min
(matching CLRS adj-matrix variant).  The proven bound is `3·V²`.

---

## Limitations

1. **MST existence assumed, not derived.** The precondition
   `∃ t. is_mst g t` appears in both `Kruskal.Spec` and `Prim.Spec`.
   Deriving MST existence from connectivity alone is not done.

2. **Kruskal Impl → MST gap.** The imperative Kruskal proves forest +
   acyclicity but not MST optimality.  The `Bridge` module provides the
   mathematical machinery, but connecting it to the imperative loop
   requires strengthening the inner scan invariant.

3. **Prim Impl → MST gap.** `prim_correct` is a relatively weak
   postcondition (local key/parent properties).  No bridge connects
   the imperative output to `prim_spec` or MST theory.

4. **Complexity modules disconnected.** Both `Kruskal.Complexity` and
   `Prim.Complexity` re-implement algorithms from scratch for ghost-tick
   analysis.  They prove tick bounds internally but share no code or
   invariants with the main `Impl` modules.

5. **Prim uses two infinity values.** The Pulse implementation uses
   `65535sz` (SizeT constraint); the pure spec uses `1000000000`.
   These are not unified.

6. **BFS-based component checking in pure spec.** Kruskal's
   `same_component_dec` uses BFS, which is expensive but total and
   decidable.  Soundness (`same_component_dec_sound`) bridges the
   decidable check to the propositional `same_component` (existential
   path).

---

## CLRS Section Mapping

| CLRS Section | Content | Module |
|---|---|---|
| §23.1 | Overview / safe edges | `MST.Spec` |
| Theorem 23.1 | Cut property | `MST.Spec` (`cut_property`) |
| §23.2 (Kruskal) | Kruskal's algorithm | `Kruskal.Spec`, `Kruskal.Impl` |
| §23.2 (Prim) | Prim's algorithm | `Prim.Spec`, `Prim.Impl` |
| Corollary 23.2 | Greedy MST correctness | `Kruskal.Bridge` |

---

## Build Instructions

```bash
cd ch23-mst
make          # verify all 25 files
```

## Technical Notes

1. **Matrix Indexing**: Flat array `weights[u*n+v]` with proven overflow
   safety when `n² < 2⁶⁴`.
2. **Platform Requirement**: Requires 64-bit SizeT (`SZ.fits_u64`).
3. **Edge equality**: Undirected — `edge_eq` treats `(u,v)` and `(v,u)`
   as identical.
