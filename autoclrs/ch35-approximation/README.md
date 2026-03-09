# CLRS Chapter 35: Approximation Algorithms — 2-Approximation Vertex Cover

This directory contains a verified Pulse implementation of the 2-approximation
vertex cover algorithm from CLRS Chapter 35, Section 35.1 (APPROX-VERTEX-COVER).

**Zero admits. Zero assumes. All proofs complete, including the 2-approximation
ratio (CLRS Theorem 35.1).**

---

## Algorithm: APPROX-VERTEX-COVER (CLRS §35.1)

The APPROX-VERTEX-COVER algorithm is a greedy matching-based approach that provides
a 2-approximation to the minimum vertex cover problem:

1. Start with an empty cover set C
2. While there exist uncovered edges:
   - Pick an arbitrary uncovered edge (u, v)
   - Add both u and v to C
   - Remove all edges incident on u or v

### Implementation Variant

The implementation scans all pairs (u, v) with u < v in the upper triangle of the
adjacency matrix. When an edge is found where neither endpoint is covered
(`cover[u] = 0` and `cover[v] = 0`), it adds both endpoints to the cover. This
produces the same result as the CLRS algorithm: the set of selected edges forms a
maximal matching, and the cover consists of exactly the matching endpoints.

### Pure Specification

Key definitions from `CLRS.Ch35.VertexCover.Spec`:

```fstar
type edge = nat & nat
type cover_fn = nat -> bool

let pairwise_disjoint (m: list edge) : Type0 = …  (* no two edges share a vertex *)

let is_valid_cover_for_edges (c: cover_fn) (edges: list edge) : Type0 =
  forall (e: edge). memP e edges ==> (let (u, v) = e in c u \/ c v)

let rec count_cover (c: cover_fn) (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0
  else (if c (n - 1) then 1 else 0) + count_cover c (n - 1)
```

**Minimum vertex cover** — the optimization target:

```fstar
let is_minimum_vertex_cover (adj: seq int) (n: nat) (c_min: cover_fn) : Type0 =
  is_valid_graph_cover adj n c_min /\
  (forall (c': cover_fn). is_valid_graph_cover adj n c' ==>
    count_cover c_min n <= count_cover c' n)

let min_vertex_cover_size (adj: seq int) (n: nat) (opt: nat) : Type0 =
  exists (c_min: cover_fn).
    is_minimum_vertex_cover adj n c_min /\
    count_cover c_min n = opt
```

### Correctness Theorem (Impl.fsti)

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
      (forall (i: nat). i < SZ.v n ==>
        (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
      (forall (opt: nat). Spec.min_vertex_cover_size s_adj (SZ.v n) opt ==>
        Spec.count_cover (Spec.seq_to_cover_fn s_cover (SZ.v n)) (SZ.v n)
          <= 2 * opt)
    )
```

The postcondition guarantees **four** properties:

1. **Correct length**: `Seq.length s_cover == SZ.v n` — output has one entry per vertex.
2. **Valid cover** (`is_cover`): for all edges (u, v) with u < v that have been
   examined (i.e., all of them, since bound_u = n), at least one of cover[u] or
   cover[v] is non-zero. This means every edge has at least one endpoint in the cover.
3. **Binary output**: every cover entry is 0 or 1 (no arbitrary non-zero values).
4. **2-approximation**: `count_cover(cover) ≤ 2 × OPT` for every possible optimal
   value. This is universally quantified over all `opt` satisfying
   `min_vertex_cover_size`, capturing CLRS Theorem 35.1.

**Why this is the strongest guarantee**: The postcondition proves both *feasibility*
(valid cover) and *optimality bound* (2-approximation ratio) simultaneously. The
2-approximation ratio `|C| ≤ 2 × OPT` is the tightest known polynomial-time
guarantee for vertex cover (assuming P ≠ NP). Proving equality with a specific pure
spec function is not meaningful here since the algorithm's output depends on edge
traversal order; instead, the universally quantified approximation bound is the
correct strongest postcondition for an approximation algorithm.

### Proof Structure (CLRS Theorem 35.1)

The proof proceeds in two steps, mirroring the CLRS textbook argument:

**Step 1 — Matching lower bound** (`matching_lower_bound`): Any valid cover must
include at least one endpoint of each edge in a pairwise-disjoint matching, so
`count_cover(any_cover) ≥ |matching|`:

```fstar
val matching_lower_bound (c: cover_fn) (m: list edge) (n: nat)
  : Lemma (requires pairwise_disjoint m /\ is_valid_cover_for_edges c m /\ …)
          (ensures count_cover c n >= List.Tot.length m)
```

**Step 2 — Algorithm cover size** (`matching_cover_size`): The cover produced by
taking both endpoints of every matching edge has size exactly `2 × |matching|`:

```fstar
val matching_cover_size (m: list edge) (n: nat)
  : Lemma (requires pairwise_disjoint m /\ …)
          (ensures count_cover (fun x -> existsb (fun e -> edge_uses_vertex e x) m) n
                   == 2 * List.Tot.length m)
```

**Combined** (`theorem_35_1`): `|C_alg| = 2|M| ≤ 2 × count(any valid cover) ≤ 2 × OPT`:

```fstar
val theorem_35_1 (m: list edge) (c_opt: cover_fn) (n: nat)
  : Lemma (requires pairwise_disjoint m /\ … /\ is_valid_cover_for_edges c_opt m)
          (ensures (
            let c_alg = fun x -> existsb (fun e -> edge_uses_vertex e x) m in
            count_cover c_alg n == 2 * List.Tot.length m /\
            count_cover c_opt n >= List.Tot.length m /\
            count_cover c_alg n <= 2 * count_cover c_opt n))
```

**Bridge to Pulse** (`approximation_ratio_theorem`): Connects the Pulse
implementation's concrete `seq int` cover to the abstract matching structure,
establishing that the Pulse output satisfies the 2-approximation bound. A ghost
reference tracks the matching during execution; loop invariants ensure the matching
is pairwise disjoint and the cover consists exactly of matching endpoints.

### Complexity

The algorithm examines every entry in the upper triangle of the adjacency matrix:
`V × (V-1) / 2` iterations, giving **O(V²)** time complexity.

```fstar
let vertex_cover_iterations (v: nat) : nat = v * (v - 1) / 2

let vertex_cover_quadratic (v: nat)
  : Lemma (ensures vertex_cover_iterations v <= v * v) = ()

let vertex_cover_tight_bound (v: nat)
  : Lemma (ensures vertex_cover_iterations v <= v * v / 2) = ()
```

**Limitation**: CLRS achieves O(V + E) using adjacency lists by maintaining a set
of remaining edges and removing all edges incident on matched vertices. This
implementation uses an adjacency matrix, requiring O(V²) even for sparse graphs.
The complexity definitions are proven but are **not formally linked** to the Pulse
implementation via ghost operation counters.

### Limitations

- **Adjacency matrix representation**: O(V²) space and time, even for sparse graphs.
  CLRS uses adjacency lists for O(V + E). This is a representation choice, not an
  algorithmic deficiency.
- **Upper-triangle scan only** (u < v): Correct for undirected graphs where
  `adj[u×n+v] = adj[v×n+u]`. Directed graphs would need full matrix scan.
- **Graph size limited**: `n × n` must fit in `SizeT` (`SZ.fits (n * n)`).
- **No edge output**: Returns the cover array, not the matching. The matching exists
  only as a ghost value during verification.
- **Tight ratio not proven**: The 2-approximation bound is proven to be *achieved*
  (i.e., the algorithm never exceeds 2×OPT), but it is not proven that the bound is
  *tight* (i.e., that there exist graphs achieving ratio exactly 2). This is a
  textbook result but is not formalized.

---

## File Inventory

| File | Type | Description |
|------|------|-------------|
| `CLRS.Ch35.VertexCover.Spec.fst` | Pure spec | Types, graph predicates, counting functions, min cover definition |
| `CLRS.Ch35.VertexCover.Lemmas.fsti` | Interface | Lemma signatures: counting, matching bounds, Theorem 35.1 |
| `CLRS.Ch35.VertexCover.Lemmas.fst` | Pure proof | All proofs: counting, matching_lower_bound, matching_cover_size, theorem_35_1, approximation_ratio_theorem |
| `CLRS.Ch35.VertexCover.Complexity.fsti` | Interface | Complexity definitions: iteration count, quadratic bound |
| `CLRS.Ch35.VertexCover.Complexity.fst` | Pure proof | O(V²) bound proof and tight bound |
| `CLRS.Ch35.VertexCover.Impl.fsti` | Interface | Pulse function signature with full postcondition |
| `CLRS.Ch35.VertexCover.Impl.fst` | Pulse impl | Implementation with nested loops, ghost matching, and approximation bridge |

## Build Instructions

```bash
cd ch35-approximation
make verify              # Verify all modules
```

Or verify the implementation explicitly:

```bash
FSTAR_FILES="CLRS.Ch35.VertexCover.Impl.fst" make verify
```

The `Makefile` includes the Pulse test infrastructure:

```makefile
PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk
```

### Constraints

- Graph size limited by `n * n` fitting in `SizeT` (i.e., `SZ.fits (n * n)`)
- Requires Pulse library (located at `../../pulse` relative to this directory)

## Summary

| Property | Status | Details |
|---|---|---|
| Valid vertex cover | ✅ Proven | `is_cover s_adj s_cover n n 0` — all edges covered |
| Binary output | ✅ Proven | `∀i. cover[i] = 0 ∨ cover[i] = 1` |
| 2-approximation (CLRS Thm 35.1) | ✅ Proven | `count_cover ≤ 2 × OPT` via ghost matching |
| Memory safety | ✅ Proven | Separation-logic framing via `pts_to` |
| Complexity | O(V²) proven | `vertex_cover_iterations v ≤ v²`; not linked to Pulse |
| Admits | **0** | Fully verified |
