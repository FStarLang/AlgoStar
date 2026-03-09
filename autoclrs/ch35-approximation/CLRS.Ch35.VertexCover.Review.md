# Vertex Cover 2-Approximation (CLRS §35.1)

## Top-Level Signature

Here is the top-level signature proven about the vertex cover approximation
algorithm in `CLRS.Ch35.VertexCover.Impl.fsti`:

```fstar
fn approx_vertex_cover
  (#p: perm)
  (adj: array int)
  (#s_adj: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires 
    A.pts_to adj #p s_adj ** 
    pure (
      SZ.v n > 0 /\ 
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length s_adj == SZ.v n * SZ.v n
    )
  returns cover: V.vec int
  ensures exists* s_cover.
    A.pts_to adj #p s_adj **
    V.pts_to cover s_cover **
    pure (
      Seq.length s_cover == SZ.v n /\
      Spec.is_cover s_adj s_cover (SZ.v n) (SZ.v n) 0 /\
      (forall (i: nat). i < SZ.v n ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
      (forall (opt: nat). Spec.min_vertex_cover_size s_adj (SZ.v n) opt ==>
        Spec.count_cover (Spec.seq_to_cover_fn s_cover (SZ.v n)) (SZ.v n) <= 2 * opt)
    )
```

### Parameters

* `adj` is a read-only adjacency matrix stored as a flat array of `int`,
  with `adj[u*n + v] ≠ 0` indicating an edge between vertices `u` and `v`.
  The ghost variable `s_adj` captures the initial contents.

* `n` is the number of vertices (`SZ.t`). The matrix has `n × n` entries.

* `cover` is a freshly allocated `V.vec int` of length `n` returned by the
  function. Entry `cover[i] = 1` means vertex `i` is in the cover;
  `cover[i] = 0` means it is not.

### Preconditions

* `SZ.v n > 0`: At least one vertex.
* `SZ.fits (SZ.v n * SZ.v n)`: The matrix size fits in machine arithmetic.
* `Seq.length s_adj == SZ.v n * SZ.v n`: The adjacency matrix has the
  expected size.

### Postconditions

The `ensures` clause states that there exists a final cover sequence
`s_cover` such that:

* `Seq.length s_cover == SZ.v n` — The cover has one entry per vertex.

* `Spec.is_cover s_adj s_cover (SZ.v n) (SZ.v n) 0` — The cover is valid:
  every edge has at least one endpoint in the cover.

* `forall (i: nat). i < SZ.v n ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)` —
  Cover entries are binary (0 or 1).

* `forall (opt: nat). Spec.min_vertex_cover_size s_adj (SZ.v n) opt ==>
  Spec.count_cover (Spec.seq_to_cover_fn s_cover (SZ.v n)) (SZ.v n) <= 2 * opt` —
  **The 2-approximation guarantee**: the cover size is at most twice the
  optimal cover size.

## Auxiliary Definitions

### `is_cover` (from `CLRS.Ch35.VertexCover.Spec`)

```fstar
let is_cover (s_adj s_cover: seq int) (n: nat) (bound_u bound_v: nat) : prop =
  Seq.length s_adj == n * n /\
  Seq.length s_cover == n /\
  (forall (u v: nat). (u < bound_u \/ (u == bound_u /\ v < bound_v)) ==>
    u < n ==> v < n ==> u < v ==>
    Seq.index s_adj (u * n + v) <> 0 ==>
    (Seq.index s_cover u <> 0 \/ Seq.index s_cover v <> 0))
```

This tracks which edges have been processed during the nested loop. With
`bound_u = n` and `bound_v = 0` (the final state), it says: for every edge
(u, v) with u < v, at least one endpoint is in the cover. This is the
standard definition of a vertex cover, restricted to upper-triangular
entries to avoid double-counting in undirected graphs.

### `min_vertex_cover_size` (from `CLRS.Ch35.VertexCover.Spec`)

```fstar
let min_vertex_cover_size (adj: seq int) (n: nat) (opt: nat) : Type0 =
  exists (c_min: cover_fn). 
    is_minimum_vertex_cover adj n c_min /\ 
    count_cover c_min n = opt
```

This asserts that `opt` is the size of a minimum vertex cover. It is
existentially quantified: there exists some cover function `c_min` that
(a) covers all edges and (b) has the smallest possible count among all
valid covers, and its count equals `opt`.

### `is_minimum_vertex_cover` (from `CLRS.Ch35.VertexCover.Spec`)

```fstar
let is_minimum_vertex_cover (adj: seq int) (n: nat) (c_min: cover_fn) : Type0 =
  is_valid_graph_cover adj n c_min /\
  (forall (c': cover_fn). is_valid_graph_cover adj n c' ==>
    count_cover c_min n <= count_cover c' n)
```

A cover is minimum if it is valid and no valid cover has fewer vertices.

### `count_cover` (from `CLRS.Ch35.VertexCover.Spec`)

```fstar
let rec count_cover (c: cover_fn) (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0
  else (if c (n - 1) then 1 else 0) + count_cover c (n - 1)
```

Counts the number of vertices in a cover function by summing over
`[0, n)`.

### `seq_to_cover_fn` (from `CLRS.Ch35.VertexCover.Spec`)

```fstar
let seq_to_cover_fn (s_cover: seq int) (n: nat{Seq.length s_cover = n}) : cover_fn =
  fun (i: nat) -> i < n && Seq.index s_cover i <> 0
```

Converts the Pulse output sequence (0/1 integers) to a boolean cover
function for use in the pure specification.

### `pairwise_disjoint` (from `CLRS.Ch35.VertexCover.Spec`)

```fstar
let rec pairwise_disjoint (m: list edge) : Type0 =
  match m with
  | [] -> True
  | e :: rest ->
      (forall (e': edge). memP e' rest ==> ~(edges_share_vertex e e')) /\
      pairwise_disjoint rest
```

A matching is pairwise disjoint if no two edges share a vertex. This is the
key structural property of the maximal matching built by the algorithm.

## What Is Proven

The postcondition establishes three properties:

1. **Valid cover** (`is_cover`): Every edge (u, v) with `u < v` and
   `adj[u*n+v] ≠ 0` has at least one endpoint marked in the cover.

2. **Binary output**: All cover entries are exactly 0 or 1.

3. **2-approximation guarantee**: `count_cover(cover) ≤ 2 × OPT`, where
   OPT is the size of the minimum vertex cover.

The 2-approximation proof follows the structure of CLRS Theorem 35.1:

* The algorithm builds a maximal matching `M` (a set of edges with no
  shared vertices). A ghost reference tracks `M` during execution.
* The cover consists of exactly the endpoints of `M`, so `|cover| = 2|M|`.
* Any valid cover must include at least one endpoint of every edge in `M`,
  so `OPT ≥ |M|`.
* Therefore `|cover| = 2|M| ≤ 2 × OPT`.

The key lemmas in `CLRS.Ch35.VertexCover.Lemmas` are:

* **`matching_lower_bound`**: Any valid cover of a pairwise-disjoint
  matching has count ≥ the matching size. Proven by decomposing the cover
  count via `sum_le_count` (each matching edge contributes at least 1 to
  any cover) and `sum_ge_length` (each covered edge contributes ≥ 1).

* **`matching_cover_size`**: The cover consisting of all matching endpoints
  has count = 2 × matching size. Proven by induction on the matching list,
  using `matching_cover_add_two` to show each new edge adds exactly 2 to
  the count (since pairwise disjointness ensures no overlap).

* **`theorem_35_1`**: Combines the above: `count_cover(c_alg) = 2|M|`,
  `count_cover(c_opt) ≥ |M|`, hence `count_cover(c_alg) ≤ 2 × count_cover(c_opt)`.

* **`pulse_cover_is_valid`**: Connects the Pulse `is_cover` predicate to
  the pure `is_valid_graph_cover` via `extract_edges`.

* **`approximation_ratio_theorem`**: The final bridge lemma that connects
  the Pulse implementation's output to the CLRS theorem, using
  `count_cover_ext` to equate the sequence-based cover with the
  matching-based cover.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **O(V²) with adjacency matrix, not O(V+E).** The implementation uses a
   flat adjacency matrix (`n × n` array) and scans all upper-triangular
   entries in a nested loop. CLRS achieves O(V+E) using adjacency lists.
   For sparse graphs, this implementation is asymptotically slower.

2. **No `n = 0` support.** The precondition requires `n > 0`. An empty
   graph trivially has an empty vertex cover, but this degenerate case is
   not handled.

3. **Adjacency matrix must be symmetric.** The specification scans only
   upper-triangular entries (`u < v`), which is correct for undirected
   graphs where `adj[u*n+v] = adj[v*n+u]`. The precondition does not
   enforce symmetry — if the matrix is asymmetric, edges in the lower
   triangle are silently ignored.

4. **No edge-weight or weighted cover.** The specification handles only
   unweighted vertex cover. CLRS §35.2 discusses weighted variants, which
   are not addressed.

5. **`min_vertex_cover_size` is existentially quantified.** The
   2-approximation bound is stated as: for all `opt` such that
   `min_vertex_cover_size s_adj n opt`, the cover is ≤ `2 * opt`. The
   predicate `min_vertex_cover_size` itself requires the existence of a
   minimum cover function. This is logically correct but means the bound
   is vacuously true if no minimum cover exists (which cannot happen for
   finite graphs, but is not proven).

6. **Unconditional writes.** The Pulse implementation unconditionally writes
   `cover[u]` and `cover[v]` on every iteration (computing `new_cu` and
   `new_cv` and writing them), even when no update is needed. This
   simplifies the proof but means the cover array is written O(n²) times
   instead of O(E) times.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Iterations | O(V²) = V(V−1)/2 | ❌ Not linked | Exact (spec only) |

The complexity is defined in `CLRS.Ch35.VertexCover.Complexity`:

```fstar
let vertex_cover_iterations (v: nat) : nat = v * (v - 1) / 2

let vertex_cover_quadratic (v: nat)
  : Lemma (ensures vertex_cover_iterations v <= v * v) = ()
```

This is correct for the adjacency-matrix implementation but is not linked
to the Pulse code via ghost counters. The CLRS algorithm with adjacency
lists achieves O(V+E).

## Proof Structure

The proof uses a **ghost matching** technique:

1. A `GR.ref (list Spec.edge)` ghost reference `matching_ref` tracks the
   set of edges whose endpoints were added to the cover during execution.

2. The `matching_inv` invariant states:
   - The matching is pairwise disjoint (no shared vertices).
   - The cover entries are exactly the matching endpoints:
     `(s_cover[x] ≠ 0) ↔ existsb (edge_uses_vertex · x) matching`.
   - Each matching edge is a valid graph edge with `u < v`.

3. The nested loop maintains both `is_cover` (all processed edges are
   covered) and `matching_inv`. When an uncovered edge `(u, v)` is found
   (`has_edge ≠ 0 && cu = 0 && cv = 0`), both endpoints are added to the
   cover and the edge is added to the ghost matching.

4. After the loop, `apply_approximation_bound` applies
   `Lemmas.approximation_ratio_theorem` to connect the ghost matching to
   the 2-approximation guarantee.

Key implementation details:
* `is_cover_step`: Proves that processing one edge preserves `is_cover`.
* `is_cover_binary_step`: Proves that writing 0/1 values preserves the
  binary property.
* `matching_inv_step`: Proves that updating the cover and matching
  preserves `matching_inv`. Uses `existsb_false_means_all_false` to
  establish that newly added vertices are not already in the matching.
* `is_cover_skip_to` and `is_cover_next_row`: Handle the transitions
  between inner/outer loop iterations.

## Files

| File | Role |
|------|------|
| `CLRS.Ch35.VertexCover.Impl.fsti` | Public interface (this signature) |
| `CLRS.Ch35.VertexCover.Impl.fst` | Pulse implementation with ghost matching |
| `CLRS.Ch35.VertexCover.Spec.fst` | Pure specifications and type definitions |
| `CLRS.Ch35.VertexCover.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch35.VertexCover.Lemmas.fst` | Lemma proofs (CLRS Theorem 35.1) |
| `CLRS.Ch35.VertexCover.Complexity.fsti` | Complexity definitions (signatures) |
| `CLRS.Ch35.VertexCover.Complexity.fst` | Complexity proofs (O(V²) bound) |
