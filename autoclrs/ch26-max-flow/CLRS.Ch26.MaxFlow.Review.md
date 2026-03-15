# Edmonds-Karp Maximum Flow (CLRS §26.2–26.3)

## Top-Level Signature

Here is the top-level signature proven about Edmonds-Karp in
`CLRS.Ch26.MaxFlow.Impl.fsti`:

```fstar
fn max_flow
  (capacity: A.array int)
  (#cap_seq: Ghost.erased (Seq.seq int))
  (flow: A.array int)
  (#flow_contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (source: SZ.t)
  (sink: SZ.t)
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_contents **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      valid_caps cap_seq (SZ.v n)
    )
  returns completed: bool
  ensures exists* flow_seq'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq' **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_seq' == SZ.v n * SZ.v n /\
      imp_valid_flow flow_seq' cap_seq (SZ.v n) (SZ.v source) (SZ.v sink) /\
      no_augmenting_path #(SZ.v n) cap_seq flow_seq' (SZ.v source) (SZ.v sink)
    )
```

### Parameters

* `capacity` is a flat `n×n` capacity matrix (read-only). Ghost variable
  `cap_seq` captures its contents.

* `flow` is a flat `n×n` flow matrix (output, overwritten with the max flow).

* `n` is the number of vertices, of type `SZ.t`.

* `source`, `sink` are the source and sink vertex indices.

### Preconditions

* `SZ.v n > 0`: At least one vertex.
* `SZ.v source < SZ.v n` and `SZ.v sink < SZ.v n`: Source and sink are valid.
* `SZ.v source <> SZ.v sink`: Source and sink are distinct.
* `Seq.length cap_seq == SZ.v n * SZ.v n`: Capacity matrix is properly sized.
* `Seq.length flow_contents == SZ.v n * SZ.v n`: Flow matrix is properly sized.
* `SZ.fits (SZ.v n * SZ.v n)`: No `SZ.t` overflow.
* `valid_caps cap_seq (SZ.v n)`: All capacities are non-negative.

### Postcondition

The `ensures` clause states that there exists a final flow sequence `flow_seq'`
such that:

* `imp_valid_flow flow_seq' cap_seq (SZ.v n) (SZ.v source) (SZ.v sink)` —
  The output is a valid flow (capacity constraints + flow conservation).

* `no_augmenting_path #(SZ.v n) cap_seq flow_seq' (SZ.v source) (SZ.v sink)` —
  No augmenting path exists in the residual graph. This is the optimality
  condition: by the max-flow min-cut theorem, this implies the flow is maximum.

## Auxiliary Definitions

### `valid_flow` (from `CLRS.Ch26.MaxFlow.Spec`)

```fstar
let valid_flow (#n: nat) (flow: flow_matrix n) (cap: capacity_matrix n)
               (source: nat{source < n}) (sink: nat{sink < n}) : prop =
  (forall (u: nat{u < n}) (v: nat{v < n}). 
    0 <= get flow n u v /\ get flow n u v <= get cap n u v) /\
  (forall (u: nat{u < n /\ u <> source /\ u <> sink}).
    sum_flow_into flow n u n == sum_flow_out flow n u n)
```

CLRS Definition 26.1: capacity constraint (`0 ≤ f(u,v) ≤ c(u,v)` for all
`u,v`) and flow conservation (inflow = outflow for all vertices except source
and sink).

### `no_augmenting_path` (from `CLRS.Ch26.MaxFlow.Spec`)

```fstar
let no_augmenting_path (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                        (source: nat{source < n}) (sink: nat{sink < n}) : prop =
  forall (path: list nat).
    Cons? path /\ L.hd path = source /\ L.last path = sink /\
    (forall (v: nat). L.mem v path ==> v < n) ==>
    bottleneck cap flow n path <= 0
```

Every source-to-sink path has non-positive bottleneck in the residual graph.
This is the key precondition of the max-flow min-cut theorem.

### `imp_valid_flow` and Bridge Lemma (from `CLRS.Ch26.MaxFlow.Impl`)

```fstar
val imp_valid_flow (flow_seq cap_seq: Seq.seq int) (n source sink: nat) : prop

val imp_valid_flow_implies_valid_flow (flow_seq cap_seq: Seq.seq int) (n source sink: nat)
  : Lemma
    (requires imp_valid_flow flow_seq cap_seq n source sink)
    (ensures
      n > 0 /\ source < n /\ sink < n /\
      Seq.length flow_seq == n * n /\ Seq.length cap_seq == n * n /\
      valid_flow #n flow_seq cap_seq source sink)
```

`imp_valid_flow` is the imperative-level flow validity predicate.
`imp_valid_flow_implies_valid_flow` is the **bridge lemma** connecting the
imperative postcondition to the spec-level `valid_flow`. This enables callers
to invoke the max-flow min-cut theorem on the output of `max_flow`.

## Max-Flow Min-Cut Theorem

### `max_flow_min_cut_theorem` (from `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut`)

```fstar
val max_flow_min_cut_theorem (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                              (source: nat{source < n}) (sink: nat{sink < n})
  : Lemma
    (requires
      valid_flow flow cap source sink /\
      no_augmenting_path cap flow source sink)
    (ensures
      (exists (s_set: nat -> bool).
        is_st_cut s_set n source sink /\
        flow_value flow n source == cut_capacity cap s_set))
```

CLRS Theorem 26.6 (strong duality): when no augmenting path exists, the flow
value equals the capacity of some s-t cut. Combined with weak duality
(`flow_value ≤ cut_capacity` for any cut), this proves the flow is maximum.

### Supporting Theorems

* `lemma_flow_value_eq_net_flow` (Lemma 26.4): Flow value = net flow across any
  s-t cut.
* `weak_duality` (Corollary 26.5): `flow_value ≤ cut_capacity` for any valid
  flow and any s-t cut.

## Augmentation Lemmas (from `CLRS.Ch26.MaxFlow.Lemmas`)

* `augment_preserves_valid`: Augmenting along a simple path preserves flow
  validity.
* `augment_increases_value`: Augmentation strictly increases flow value (when
  bottleneck > 0).
* `zero_flow_valid`: Zero flow is valid for any network with non-negative
  capacities.
* `lemma_augment_aux_last_first`: Edge augmentation is order-independent for
  distinct-vertex paths.

## What Is Proven

1. **Imperative max flow:** `max_flow` computes a valid flow with no augmenting
   path. This is the **strongest possible postcondition** — it directly implies
   optimality via the MFMC theorem.

2. **Max-flow min-cut theorem:** `max_flow_min_cut_theorem` proves strong
   duality: flow value = min cut capacity when no augmenting path exists.

3. **Bridge lemma:** `imp_valid_flow_implies_valid_flow` connects the
   imperative result to the spec-level theorem.

4. **Augmentation correctness:** `augment_preserves_valid` and
   `augment_increases_value` prove each BFS augmentation step is correct.

5. **Termination:** Proved without fuel. Each augmentation increases
   `flow_value` by ≥ 1 (integer capacities), bounded by
   `cap_sum = Σ cap[source][v]`.

**Zero admits, zero assumes** across `Impl.fst`, `Spec.fst`, `Lemmas.fst`,
`Lemmas.MaxFlowMinCut.fst`, `Complexity.fst`, and `Test.fst`. No `assume_`,
`admit`, or `assume val` in any file.

## Specification Gaps and Limitations

1. **No path reconstruction.** The postcondition proves a max flow exists
   (as a flow matrix) but does not extract or return the augmenting paths used.

2. **Integer capacities only.** Capacities and flows are `int`. The
   augmentation increases flow by integer bottleneck ≥ 1, which is essential
   for termination. Rational or real capacities would require a different
   termination argument.

3. **Adjacency matrix representation.** Both capacity and flow are flat `n×n`
   arrays. No sparse representation is provided. Memory usage is Θ(V²)
   regardless of edge count.

4. **`valid_caps` is a runtime precondition.** The caller must ensure all
   capacities are non-negative. A `check_valid_caps_fn` is provided for
   runtime validation, and `valid_caps_intro` bridges the runtime check
   result to the abstract `valid_caps` predicate.

5. **`imp_valid_flow` is opaque.** The imperative validity predicate is a `val`
   without an exposed definition. Callers must use the bridge lemma to access
   the spec-level `valid_flow`.

6. **Complexity module uses algebraic bounds, not ghost counters.** Unlike
   Floyd-Warshall, the O(VE²) complexity bound is proven algebraically over
   a ghost tick model, not by instrumenting the actual Pulse implementation
   with a ghost counter.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Total operations | O(VE²) | ✅ Algebraic proof | Upper bound |
| Augmentations | O(VE) | ✅ Edge criticality | Upper bound |
| Per augmentation | O(E) | ✅ BFS + path walk | Upper bound |
| Dense graph | O(V⁵) | ✅ Corollary | Upper bound |
| Sparse graph (E=O(V)) | O(V³) | ✅ Corollary | Upper bound |

The complexity analysis in `Complexity.fst` is **fully proven** with zero
admits and zero assume vals. Key proven results:

* `lemma_edge_critical_bound`: Each edge becomes critical ≤ `n+1` times in a
  BFS augmentation trace (CLRS Lemma 26.8).
* `distances_nondecreasing`: BFS distances are monotonically non-decreasing
  across augmentations (CLRS Lemma 26.7).
* `edmonds_karp_complexity`: Total cost ≤ `n × num_edges × (2 × num_edges)`.
* `edmonds_karp_verified_complexity`: End-to-end verified O(VE²) with explicit
  tick accounting via `edmonds_karp_state`.

## Proof Structure

The proof has four layers:

1. **Spec layer** (`Spec.fst`): Defines flow networks, validity, residual
   graphs, augmenting paths, bottleneck, augmentation, Ford-Fulkerson steps,
   and s-t cuts. Zero admits.

2. **Augmentation lemma layer** (`Lemmas.fst`): Proves augmentation preserves
   validity and increases flow value. Uses `distinct_vertices` (simple path)
   as a key precondition. Proves `augment_edge` maintains capacity constraints
   and conservation at uninvolved vertices. Zero admits.

3. **MFMC layer** (`Lemmas.MaxFlowMinCut.fst`): Proves the max-flow min-cut
   theorem via the standard construction: define `S = {v | reachable from source
   in residual graph}`. When no augmenting path exists, `sink ∉ S`, so `(S, T)`
   is an s-t cut. All cross-cut edges are saturated (flow = capacity) and all
   reverse cross-cut edges have zero flow, giving `flow_value = cut_capacity`.
   Zero admits.

4. **Complexity layer** (`Complexity.fst`): Defines BFS distance computation,
   augmentation traces, criticality counting. Proves edge criticality bound
   via monotonicity of BFS distances. Derives O(VE²) bound. Zero admits.

## Files

| File | Role |
|------|------|
| `CLRS.Ch26.MaxFlow.Impl.fsti` | Public interface (this signature) |
| `CLRS.Ch26.MaxFlow.Impl.fst` | Pulse implementation |
| `CLRS.Ch26.MaxFlow.Spec.fst` | Pure spec: flow validity, residual graphs, augmentation |
| `CLRS.Ch26.MaxFlow.Lemmas.fsti` | Augmentation lemma signatures |
| `CLRS.Ch26.MaxFlow.Lemmas.fst` | Augmentation proofs |
| `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fsti` | MFMC theorem signature |
| `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fst` | MFMC proof |
| `CLRS.Ch26.MaxFlow.Complexity.fsti` | Complexity interface |
| `CLRS.Ch26.MaxFlow.Complexity.fst` | O(VE²) complexity proof |
| `CLRS.Ch26.MaxFlow.Test.fst` | Test cases (5 tests, zero assumes) |
