# Prim's MST Algorithm (CLRS §23.2)

**Last reviewed**: 2026-03-16

## Top-Level Signature

Here is the top-level signature proven about Prim's algorithm in
`CLRS.Ch23.Prim.Impl.fsti`:

```fstar
fn prim
  (#p: perm)
  (weights: array SZ.t)
  (#weights_seq: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (source: SZ.t)
  requires A.pts_to weights #p weights_seq ** pure (
    SZ.v n > 0 /\
    SZ.v n * SZ.v n < pow2 64 /\
    SZ.v source < SZ.v n /\
    Seq.length weights_seq == SZ.v n * SZ.v n /\
    SZ.fits_u64
  )
  returns res: (V.vec SZ.t & V.vec SZ.t)
  ensures exists* (key_seq parent_seq: Ghost.erased (Seq.seq SZ.t)).
    A.pts_to weights #p weights_seq **
    V.pts_to (fst res) key_seq **
    V.pts_to (snd res) parent_seq **
    pure (prim_correct key_seq parent_seq weights_seq (SZ.v n) (SZ.v source))
```

### Parameters

* `weights` is a flat `n×n` weight matrix (read-only, `SZ.t` entries). Ghost
  variable `weights_seq` captures its contents.

* `n` is the number of vertices, of type `SZ.t`.

* `source` is the starting vertex for tree growth.

### Preconditions

* `SZ.v n > 0`: At least one vertex.
* `SZ.v n * SZ.v n < pow2 64`: No overflow in matrix indexing.
* `SZ.v source < SZ.v n`: Source is a valid vertex.
* `Seq.length weights_seq == SZ.v n * SZ.v n`: Weight matrix is properly sized.
* `SZ.fits_u64`: SizeT fits in 64 bits.

### Postcondition

The function returns a pair of vectors `(key, parent)` with:

* `prim_correct key_seq parent_seq weights_seq (SZ.v n) (SZ.v source)` — The
  output satisfies correctness predicates on the key and parent arrays.

## Auxiliary Definitions

### `prim_correct` (from `CLRS.Ch23.Prim.Impl`)

```fstar
let prim_correct 
    (key_seq: Seq.seq SZ.t)
    (parent_seq: Seq.seq SZ.t)
    (weights_seq: Seq.seq SZ.t)
    (n: nat) 
    (source: nat) 
  : prop 
  = Seq.length key_seq == n /\
    Seq.length parent_seq == n /\
    source < n /\
    Seq.length weights_seq == n * n /\
    SZ.v (Seq.index key_seq source) == 0 /\
    all_keys_bounded key_seq /\
    SZ.v (Seq.index parent_seq source) == source
```

This is a **weak postcondition**. It states:
* Arrays have correct lengths.
* `key[source] = 0`: Source has zero key.
* `all_keys_bounded key_seq`: All keys ≤ `infinity` (65535).
* `parent[source] = source`: Source is its own parent.

**Critically, `prim_correct` does NOT prove:** sorted output, spanning tree,
subset of MST, acyclicity, or any structural tree property. It only constrains
array shapes and boundary values.

### `prim_spec` (from `CLRS.Ch23.Prim.Spec`)

```fstar
val prim_spec (adj: adj_matrix) (n: nat) (start: nat)
  : Pure (list edge)
    (requires n > 0 /\ start < n /\
              well_formed_adj adj n /\
              all_connected n (adj_to_edges adj n) /\
              (exists (t: list edge). is_mst (adj_to_graph adj n) t))
    (ensures fun result ->
      let g = adj_to_graph adj n in
      List.Tot.length result = n - 1 /\
      (exists (t: list edge). is_mst g t /\ subset_edges result t) /\
      all_connected n result)
```

The pure spec proves: `n−1` edges, safe (subset of some MST), and all
vertices connected. Combined, this is equivalent to proving the result is a
spanning tree that is safe — but it does **not** directly state `is_mst`.

### `pure_prim` (from `CLRS.Ch23.Prim.Spec`)

```fstar
val pure_prim (adj: adj_matrix) (n: nat) (start: nat) : list edge
```

The pure functional Prim algorithm. Three lemmas prove its properties:
* `lemma_prim_has_n_minus_1_edges`: Exactly `n−1` edges.
* `lemma_prim_all_connected`: All vertices connected.
* `lemma_prim_result_is_safe`: Result is subset of some MST.

## MST Bridging

### `prim_result_is_mst` (from `CLRS.Ch23.Prim.Impl`)

```fstar
val prim_result_is_mst
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      n > 0 /\
      prim_correct key_seq parent_seq weights_seq n source /\
      Seq.length weights_seq == n * n /\
      (let adj = weights_to_adj_matrix weights_seq n in
       let g = PrimSpec.adj_to_graph adj n in
       let wes = edges_from_parent_key parent_seq key_seq n source 0 in
       is_spanning_tree g wes /\
       (exists (t: list edge). is_mst g t /\ subset_edges wes t) /\
       Bridge.noRepeats_edge wes /\
       (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v)))
    (ensures
      (let adj = weights_to_adj_matrix weights_seq n in
       let g = PrimSpec.adj_to_graph adj n in
       let wes = edges_from_parent_key parent_seq key_seq n source 0 in
       is_mst g wes))
```

Like Kruskal's bridge, this requires the caller to provide `is_spanning_tree`,
safety (subset of MST), `noRepeats_edge`, and valid edges. These are not
automatically established by `prim` alone. The proof body calls
`Bridge.safe_spanning_tree_is_mst` — **fully proven, no admits**.

## What Is Proven

1. **Imperative local correctness:** `prim` proves `prim_correct` — key/parent
   array shapes, `key[source] = 0`, keys bounded, `parent[source] = source`.

2. **Pure spec correctness:** `pure_prim` produces `n−1` edges, connects all
   vertices, and is safe (subset of some MST).

3. **Bridge to MST:** `prim_result_is_mst` proves MST given spanning tree +
   safety + no duplicates preconditions. Fully proven via
   `Bridge.safe_spanning_tree_is_mst`.

**Zero admits, zero assumes** across `Impl.fst`, `Spec.fst`.

## Specification Gaps and Limitations

1. **`prim_correct` is weak.** The imperative postcondition does not prove any
   structural tree property (spanning, acyclic, connected, MST). It only
   constrains key/parent array shapes and boundary values. This is the most
   significant gap: the Pulse function's postcondition alone does not imply
   the result is meaningful as an MST.

2. **Gap between imperative and pure.** There is no proven refinement linking
   the imperative output (`key_seq`, `parent_seq` arrays) to the pure
   `pure_prim` result. The `edges_from_parent_key` function extracts edges
   from the parent array, but proving these edges match `pure_prim`'s output
   requires additional work.

3. **MST bridging has heavy preconditions.** `prim_result_is_mst` requires
   `is_spanning_tree`, safety, and `noRepeats_edge` — none of which are
   established by the `prim` function. A caller must independently prove these.

4. **MST existence now dischargeable.** The pure spec requires
   `(exists (t: list edge). is_mst (adj_to_graph adj n) t)` as a precondition,
   but this is now provable via `CLRS.Ch23.MST.Existence.mst_exists`.

5. **Complexity not linked to implementation.** The complexity module
   (`Prim.Complexity`) is explicitly **disconnected** from `Prim.Impl` — it
   re-implements Prim from scratch with ghost tick counters and only proves
   `prim_correct` (the weak predicate) and `complexity_bounded_prim`, not MST
   properties.

6. **Infinity sentinel mismatch.** `Prim.Impl` uses `infinity = 65535sz`
   (SizeT), while `Prim.Spec` uses `infinity = 1000000000` (int). These are
   conceptually the same role but numerically different. The impl bound limits
   edge weights to < 65535.

7. ~~**Prim.Lemmas.fst/.fsti missing.**~~ **RESOLVED.** `Prim.Lemmas.fsti/.fst`
   created as a façade re-exporting key lemmas from `Prim.Spec`.

## Profiling & Proof Stability

| File | Lines | Checked size | Max z3rlimit | Notes |
|------|-------|-------------|-------------|-------|
| `Prim.Spec.fst` | 1024 | 1060 KB | 60 | All pure proofs |
| `Prim.Impl.fst` | 438 | 344 KB | 100 | Pulse loop, rlimit 100 at line 75 |
| `Prim.Complexity.fst` | 449 | 202 KB | 100 | Ghost-tick instrumented |
| `Prim.Impl.fsti` | 145 | 104 KB | — | Interface |
| `Prim.Spec.fsti` | 77 | 75 KB | — | Interface |
| `Prim.Complexity.fsti` | 40 | 10 KB | — | Interface |

**Stability concerns:**
- `Prim.Impl.fst` line 75: `z3rlimit 100` for the main Prim loop invariant.
  Moderate; likely needs this for the `SZ.t` arithmetic and array indexing.
- `Prim.Complexity.fst` line 78: `z3rlimit 100` for complexity loop invariant.
- `Prim.Spec.fst` max rlimit is 60, which is reasonable.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Operations | O(V²) = 3·V² | ⚠️ Separate module | Upper bound only |

The complexity bound `cf - c0 ≤ 3·V²` is proven in `Prim.Complexity.fsti` but
is **not connected** to the main `Prim.Impl`. The `MST.Complexity` module also
proves `prim_iterations v ≤ 2 * v * v` algebraically, and that Prim beats
Kruskal for V ≥ 4.

## Proof Structure

The proof has three layers:

1. **Pure spec layer** (`Prim.Spec`): Defines `pure_prim` and proves `n−1`
   edges, connectivity, and safety via induction on the greedy vertex
   selection loop, using the cut property from `MST.Spec`.

2. **Imperative layer** (`Prim.Impl`): Pulse implementation with linear-scan
   extract-min over a `key` array. Maintains `prim_correct` as an invariant.

3. **Bridge layer** (reuses `Kruskal.Bridge`): `safe_spanning_tree_is_mst`
   converts a safe spanning tree to an MST.

## Checklist

- [x] Pure spec `pure_prim` defined
- [x] Pure spec proves n−1 edges (`lemma_prim_has_n_minus_1_edges`)
- [x] Pure spec proves connectivity (`lemma_prim_all_connected`)
- [x] Pure spec proves safety (`lemma_prim_result_is_safe`)
- [x] Imperative Pulse implementation verified (`prim_correct`)
- [x] Bridge theorem `prim_result_is_mst` fully proven (no admits)
- [x] Zero admits / zero assumes
- [ ] Strengthen `prim_correct` to include tree structure properties
- [ ] Prove refinement: imperative output matches `pure_prim`
- [x] Create `Prim.Lemmas.fsti/.fst` (rubric compliance)
- [ ] Reconcile infinity values (65535 vs 10⁹)
- [ ] Connect Complexity module to Impl (ghost ticks in main loop)

## Spec Validation (ImplTest)

**Test file**: `CLRS.Ch23.Prim.ImplTest.fst` — ✅ Verified (1 admit for
platform assumption `SZ.fits_u64`)
**Documentation**: `CLRS.Ch23.Prim.ImplTest.md`

### Test Instance
3-vertex triangle graph with edges (0,1) w=1, (1,2) w=2, (0,2) w=3.
Source = vertex 0. Expected MST: {(0,1), (1,2)}, total weight = 3.

### Results

| Property | Status |
|----------|:------:|
| Precondition satisfiable | ✅ (with `SZ.fits_u64` assumed) |
| `key[source] == 0` | ✅ Proven |
| `parent[source] == source` | ✅ Proven |
| All keys bounded by infinity | ✅ Proven |
| `key[1] == 1` (correct MST weight) | ❌ Unprovable |
| `parent[1] == 0` (correct MST parent) | ❌ Unprovable |
| Result is spanning tree | ❌ Not in postcondition |
| Result is MST | ❌ Not in postcondition |

**Finding**: `prim_correct` is transparent but only captures array shapes
and boundary values. It admits infinitely many incorrect outputs. For the
test instance, `prim_correct` is satisfied by both the correct output
(`key=[0,1,2], parent=[0,0,1]`) and incorrect outputs (e.g.,
`key=[0,65535,65535], parent=[0,0,0]`).

**Additional API gap**: `prim` returns freshly allocated vecs but its
postcondition does not include `is_full_vec`, preventing callers from
freeing them.

**Severity**: High. The postcondition cannot distinguish correct from
incorrect MST computations.

**Suggested fix**: Strengthen `prim_correct` to include structural tree
properties: parent validity, key-weight correspondence, tree connectivity,
and MST optimality (via the existing bridge theorem).

## Files

| File | Role |
|------|------|
| `CLRS.Ch23.Prim.Impl.fsti` | Public interface (this signature) |
| `CLRS.Ch23.Prim.Impl.fst` | Pulse implementation |
| `CLRS.Ch23.Prim.Spec.fsti` | Pure spec: `pure_prim`, `prim_spec` |
| `CLRS.Ch23.Prim.Spec.fst` | Pure spec proofs |
| `CLRS.Ch23.Prim.Complexity.fsti` | Complexity interface (disconnected) |
| `CLRS.Ch23.Prim.Complexity.fst` | Complexity proofs (disconnected) |
| `CLRS.Ch23.Prim.ImplTest.fst` | Spec validation test |
| `CLRS.Ch23.Kruskal.Bridge.fsti` | `safe_spanning_tree_is_mst` (shared) |
| `CLRS.Ch23.MST.Spec.fsti` | Graph defs, cut property, MST defs |
| `CLRS.Ch23.MST.Complexity.fsti` | Prim O(V²) algebraic proof |
