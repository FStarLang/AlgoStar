# CLRS Chapter 26: Maximum Flow (Edmonds-Karp)

## Overview

A verified implementation of the **Edmonds-Karp algorithm** (BFS-based Ford-Fulkerson method) for computing maximum flow in a network, following CLRS §26.2.

- **~5300 lines** across 6 verified F\*/Pulse modules + 4 interface files
- **Zero admits** in Spec, Lemmas, Lemmas.MaxFlowMinCut (all fully proven)
- **4 `assume val`** in Complexity.fst for BFS shortest-path distance properties
- **Max-Flow Min-Cut Theorem** (CLRS Theorem 26.6) fully proven
- **Termination** proven without fuel (bounded by `cap_sum`)

## Algorithm (CLRS §26.2, p. 714)

```
FORD-FULKERSON-METHOD(G, s, t)
1  initialize flow f to 0
2  while there exists an augmenting path p in G_f
3      augment flow f along p
4  return f
```

The implementation specializes to Edmonds-Karp by using **BFS** to find shortest augmenting paths (CLRS p. 727), yielding O(VE²) worst-case complexity.

### Implementation details

- **Representation**: Flat n×n arrays for capacity and flow matrices
- **BFS on residual graph** (`bfs_residual`): BFS with color/pred/dist/queue arrays
- **Bottleneck computation** (`find_bottleneck_imp`): Walks pred chain from sink to source
- **Flow augmentation** (`augment_imp`): Updates flow along the augmenting path
- **Static validity**: Postcondition guarantees `imp_valid_flow` (backed by runtime check)

## Specification

### `valid_flow` (CLRS Definition 26.1)

From `Spec.fst`, a valid flow satisfies two properties:

```fstar
let valid_flow (#n: nat) (flow: flow_matrix n) (cap: capacity_matrix n)
               (source: nat{source < n}) (sink: nat{sink < n}) : prop =
  // Capacity constraint: 0 ≤ f(u,v) ≤ c(u,v) for all u,v
  (forall (u: nat{u < n}) (v: nat{v < n}).
    0 <= get flow n u v /\ get flow n u v <= get cap n u v) /\
  // Flow conservation: Σ f(v,u) = Σ f(u,v) for all u ≠ source, sink
  (forall (u: nat{u < n /\ u <> source /\ u <> sink}).
    sum_flow_into flow n u n == sum_flow_out flow n u n)
```

### `no_augmenting_path`

Termination condition: every source-to-sink path has non-positive bottleneck capacity in the residual graph. This is the exact precondition of the MFMC theorem.

```fstar
let no_augmenting_path (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                       (source: nat{source < n}) (sink: nat{sink < n}) : prop =
  forall (path: list nat).
    Cons? path /\ L.hd path = source /\ L.last path = sink /\
    (forall (v: nat). L.mem v path ==> v < n) ==>
    bottleneck cap flow n path <= 0
```

## Correctness Theorem

The main entry point in `Impl.fsti`:

```pulse
fn max_flow
  (capacity: A.array int)
  (#cap_seq: Ghost.erased (Seq.seq int))
  (flow: A.array int)
  (#flow_contents: Ghost.erased (Seq.seq int))
  (n: SZ.t) (source: SZ.t) (sink: SZ.t)
  requires
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_contents **
    pure (
      SZ.v n > 0 /\ SZ.v source < SZ.v n /\ SZ.v sink < SZ.v n /\
      SZ.v source <> SZ.v sink /\
      Seq.length cap_seq == SZ.v n * SZ.v n /\
      Seq.length flow_contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\ valid_caps cap_seq (SZ.v n))
  returns completed: bool
  ensures exists* flow_seq'.
    A.pts_to capacity cap_seq **
    A.pts_to flow flow_seq' **
    pure (
      ...
      imp_valid_flow flow_seq' cap_seq (SZ.v n) (SZ.v source) (SZ.v sink) /\
      (completed ==> no_augmenting_path #(SZ.v n) cap_seq flow_seq' (SZ.v source) (SZ.v sink)))
```

**Postcondition breakdown:**

| Conjunct | Meaning |
|----------|---------|
| `imp_valid_flow flow_seq' cap_seq ...` | Resulting flow satisfies capacity constraints and conservation (always) |
| `completed ==> no_augmenting_path ...` | When `completed = true`, no augmenting path exists (MFMC precondition) |

### Bridge Lemma

`imp_valid_flow_implies_valid_flow` connects the imperative postcondition to `Spec.valid_flow`, enabling use with the MFMC theorem:

```fstar
val imp_valid_flow_implies_valid_flow (flow_seq cap_seq: Seq.seq int) (n source sink: nat)
  : Lemma
    (requires imp_valid_flow flow_seq cap_seq n source sink)
    (ensures ... /\ valid_flow #n flow_seq cap_seq source sink)
```

### Max-Flow Min-Cut Theorem (CLRS Theorem 26.6)

Fully proven in `Lemmas.MaxFlowMinCut.fsti` with zero admits:

```fstar
val max_flow_min_cut_theorem (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                             (source: nat{source < n}) (sink: nat{sink < n})
  : Lemma
    (requires valid_flow flow cap source sink /\ no_augmenting_path cap flow source sink)
    (ensures (exists (s_set: nat -> bool).
      is_st_cut s_set n source sink /\
      flow_value flow n source == cut_capacity cap s_set))
```

**Usage pattern for callers:**
1. Call `max_flow` → get `imp_valid_flow` + `no_augmenting_path` (when `completed = true`)
2. Apply `imp_valid_flow_implies_valid_flow` → get `Spec.valid_flow`
3. Apply `max_flow_min_cut_theorem` → conclude result is maximum and equals min-cut capacity

### Strongest Guarantee

The postcondition is the strongest functional guarantee achievable:
- `imp_valid_flow` is equivalent to the textbook definition of a valid flow (capacity + conservation).
- `no_augmenting_path` is the exact condition under which CLRS Theorem 26.6 guarantees the flow is maximum.
- Together they certify that any caller can derive max-flow = min-cut via the proven MFMC theorem, without any additional axioms.

## Limitations

### Admits / Assumes

**In `Complexity.fst` (4 `assume val`):**

| `assume val` | CLRS Reference | Description |
|--------------|---------------|-------------|
| `axiom_spd_source_zero` | BFS property | δ(s,s) = 0 in residual graph |
| `axiom_spd_bounded` | BFS property | δ(s,v) ≤ n − 1 for all v |
| `lemma_distances_nondecreasing` | Lemma 26.7 | Shortest-path distances non-decreasing after augmentation |
| `axiom_edge_critical_bound` | Lemma 26.8 | Each edge becomes critical at most n/2 times |

These are the **only** `assume val` statements in the entire project outside ch22 and ch24. They are all in the complexity analysis module and pertain to BFS shortest-path distance properties. The functional correctness of the implementation (valid flow + no augmenting path) is **fully proven** without any assumes.

**In `Test.fst` (1 `assume_`):**

| `assume_` | Justification |
|-----------|---------------|
| `assume_ (pure (valid_caps sc2 (SZ.v n)))` | Backed by runtime check `check_valid_caps_fn`; test-only |

**Previously admitted, now proven:**
- ~~`axiom_bfs_complete`~~ → `lemma_bfs_complete` + `lemma_bottleneck_crossing` (induction on path)
- ~~BFS postcondition `assume_` ×2~~ → Counting invariants (`count_color1`, `queue_color1`) prove `bfs_complete` at termination

## Complexity

| CLRS Result | Location | Status |
|-------------|----------|--------|
| O(VE²) total cost bound | `Complexity.fst` — `edmonds_karp_complexity` | **Proven** (from 4 axioms) |
| Each augmentation creates ≥1 critical edge | `Complexity.fst` — `lemma_augmentation_creates_critical_edge` | **Proven** (zero axioms) |
| O(VE) max augmentations | `Complexity.fst` — `lemma_max_augmentations_justified` | **Proven** (from axiom) |
| Dense graph O(V⁵) | `Complexity.fst` — `edmonds_karp_dense_graph_complexity` | **Proven** |
| Sparse graph O(V³) | `Complexity.fst` — `edmonds_karp_sparse_graph_complexity` | **Proven** |
| Distance monotonicity (Lemma 26.7) | `Complexity.fst` — `lemma_distances_nondecreasing` | **Axiom** |
| Edge criticality bound (Lemma 26.8) | `Complexity.fst` — `axiom_edge_critical_bound` | **Axiom** |

**Ghost tick framework**: The `edmonds_karp_state` type threads a `tick_count` (ghost nat) through the computation. Each BFS + augmentation adds `augmentation_cost(E)` ticks. The total is bounded by `max_augmentations(V, E) × augmentation_cost(E) ≤ V·E·2E = O(VE²)`.

**Gap**: The 4 axioms bridge BFS correctness to the O(VE²) bound. All other complexity results (critical edge creation, cost accounting, dense/sparse corollaries) are fully proven.

## Verified Properties

### Spec-level (fully proven, zero admits)

| CLRS Result | Location |
|-------------|----------|
| Lemma 26.4: \|f\| = net flow across any cut | `Lemmas.MaxFlowMinCut.fst` — `lemma_flow_value_eq_net_flow` |
| Corollary 26.5: Weak duality \|f\| ≤ c(S,T) | `Lemmas.MaxFlowMinCut.fst` — `weak_duality` |
| Theorem 26.6: Max-flow min-cut | `Lemmas.MaxFlowMinCut.fst` — `max_flow_min_cut_theorem` |
| Flow conservation preserved by augmentation | `Lemmas.fst` — `augment_preserves_valid` |
| Capacity constraints preserved by augmentation | `Lemmas.fst` — `lemma_augment_edge_capacity` |
| Flow value strictly increases per augmentation | `Lemmas.fst` — `augment_increases_value` |
| Zero flow is valid | `Lemmas.fst` — `zero_flow_valid` |

### Pure path lemmas (fully proven in Impl.fst)

| Property | Lemma |
|----------|-------|
| path\_from\_preds starts at source | `lemma_path_starts_source` |
| path\_from\_preds ends at current vertex | `lemma_path_ends_current` |
| All path vertices are < n | `lemma_path_vertices_bounded` |
| Path vertices have decreasing BFS depth | `lemma_path_depths_decreasing` |
| Path has distinct vertices | `lemma_path_distinct` |
| Augmenting path has length ≥ 2 | `lemma_path_length_ge_2` |

### BFS completeness (fully proven in Impl.fst)

| Property | Lemma |
|----------|-------|
| Bottleneck ≤ 0 across colored/uncolored partition | `lemma_bottleneck_crossing` |
| BFS complete + sink uncolored ⟹ no augmenting path | `lemma_bfs_complete` |
| BFS termination ⟹ bfs_complete | Loop invariant: `count_color1`, `queue_color1`, `processed_complete` |

### Imperative level

- **Memory safety**: All array accesses bounds-checked
- **Termination**: Proven without fuel — each augmentation increases `flow_value` by ≥1, bounded by `cap_sum`
- **Capacity validation**: Runtime `check_valid_caps_fn` verifies non-negative capacities
- **Static flow validity**: `max_flow` postcondition guarantees `imp_valid_flow`
- **Spec bridge**: `imp_valid_flow_implies_valid_flow` connects imperative postcondition to `Spec.valid_flow`
- **MFMC usability**: When `completed = true`, `no_augmenting_path` holds → callers can apply the MFMC theorem

## File Inventory

| File | Lines | Role | Admits/Assumes |
|------|------:|------|:--------------:|
| `CLRS.Ch26.MaxFlow.Spec.fst` | 355 | Pure spec: flow networks, residual graphs, augmenting paths, cuts | 0 |
| `CLRS.Ch26.MaxFlow.Lemmas.fsti` | 138 | Interface: augmentation lemma signatures | 0 |
| `CLRS.Ch26.MaxFlow.Lemmas.fst` | 679 | Lemmas: augmentation preserves validity, increases value | 0 |
| `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fsti` | 52 | Interface: MFMC theorem signatures | 0 |
| `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fst` | 800 | MFMC theorem: weak duality, strong duality (Thm 26.6) | 0 |
| `CLRS.Ch26.MaxFlow.Complexity.fsti` | 66 | Interface: complexity theorem signatures | 0 |
| `CLRS.Ch26.MaxFlow.Complexity.fst` | 618 | O(VE²) complexity analysis with ghost tick counter | **4 `assume val`** |
| `CLRS.Ch26.MaxFlow.Impl.fsti` | 116 | Interface: `max_flow` public API + bridge lemma | 0 |
| `CLRS.Ch26.MaxFlow.Impl.fst` | 2454 | Pulse implementation: BFS + augmentation + BFS completeness proof | 0 |
| `CLRS.Ch26.MaxFlow.Test.fst` | 61 | Smoke test on a 3-vertex graph | 1 `assume_` (test) |

## Summary

| Property | Status |
|----------|--------|
| Functional correctness (`valid_flow` + `no_augmenting_path`) | ✅ Fully proven |
| Bridge to spec (`imp_valid_flow → valid_flow`) | ✅ Fully proven |
| Max-Flow Min-Cut Theorem (Thm 26.6) | ✅ Fully proven |
| Weak duality (Cor 26.5) | ✅ Fully proven |
| BFS completeness | ✅ Fully proven |
| Termination (no fuel) | ✅ Proven via `cap_sum` bound |
| O(VE²) complexity | ⚠️ Proven modulo 4 `assume val` (BFS distance properties) |
| Memory safety | ✅ Pulse separation logic |

## Building

```bash
cd ch26-max-flow
make verify
```

## References

- CLRS 3rd Edition, Chapter 26: Maximum Flow (§26.1–§26.3)
- Pulse separation logic: https://github.com/FStarLang/pulse
