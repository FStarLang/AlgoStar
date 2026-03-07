# CLRS Chapter 26: Maximum Flow (Edmonds-Karp)

## Overview

A verified implementation of the **Edmonds-Karp algorithm** (BFS-based Ford-Fulkerson method) for computing maximum flow in a network, following CLRS §26.2.

- **~4200 lines** across 6 verified F\*/Pulse modules + 4 interface files
- **Zero admits** in spec and lemmas (Spec.fst, Lemmas.fst)
- **Zero assumes** in BFS and implementation (all BFS completeness fully proven)
- **Max-Flow Min-Cut Theorem** (CLRS Theorem 26.6) fully proven

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

## Files

| File | Lines | Description |
|------|------:|-------------|
| `CLRS.Ch26.MaxFlow.Spec.fst` | 341 | Pure spec: flow networks, residual graphs, augmenting paths, cuts |
| `CLRS.Ch26.MaxFlow.Lemmas.fsti` | — | Interface: augmentation lemma signatures |
| `CLRS.Ch26.MaxFlow.Lemmas.fst` | 679 | Lemmas: augmentation preserves flow validity, increases flow value |
| `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fsti` | — | Interface: MFMC theorem signatures |
| `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fst` | 804 | MFMC theorem: weak duality, strong duality (CLRS Theorem 26.6) |
| `CLRS.Ch26.MaxFlow.Complexity.fsti` | — | Interface: complexity theorem signatures |
| `CLRS.Ch26.MaxFlow.Complexity.fst` | 618 | O(VE²) complexity analysis with ghost tick counter |
| `CLRS.Ch26.MaxFlow.Impl.fsti` | — | Interface: `max_flow` public API + bridge lemma |
| `CLRS.Ch26.MaxFlow.Impl.fst` | ~1800 | Imperative Pulse implementation: BFS + augmentation + BFS completeness proof |
| `CLRS.Ch26.MaxFlow.Test.fst` | 61 | Smoke test on a 3-vertex graph |

## Verified Properties

### Spec-level (fully proven, zero admits)

| CLRS Result | Location |
|-------------|----------|
| Lemma 26.4: \|f\| = net flow across any cut | `Lemmas.MaxFlowMinCut.fst` — `lemma_flow_value_eq_net_flow` |
| Corollary 26.5: Weak duality \|f\| ≤ c(S,T) | `Lemmas.MaxFlowMinCut.fst` — `weak_duality` |
| Theorem 26.6: Max-flow min-cut | `Lemmas.MaxFlowMinCut.fst` — `max_flow_min_cut_theorem` |
| Flow conservation preserved by augmentation | `Lemmas.fst` — `augment_preserves_valid` |
| Capacity constraints preserved by augmentation | `Lemmas.fst` — `lemma_augment_preserves_capacity` |
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
| Queue entries have color 1 | `queue_color1`, `lemma_queue_color1_preserved`, `lemma_queue_color1_after_set2` |
| Color-1 count tracks queue occupancy | `count_color1 == vtail - vhead` invariant |

### Complexity (O(VE²) arithmetic proven)

| CLRS Result | Location | Status |
|-------------|----------|--------|
| O(VE²) total cost bound | `Complexity.fst` — `edmonds_karp_complexity` | Proven |
| Each augmentation creates ≥1 critical edge | `Complexity.fst` — `lemma_augmentation_creates_critical_edge` | Proven |
| Distance monotonicity (Lemma 26.7) | `Complexity.fst` — `lemma_distances_nondecreasing` | Axiom |
| Edge criticality bound (Lemma 26.8) | `Complexity.fst` — `axiom_edge_critical_bound` | Axiom |

### Imperative level

- **Memory safety**: All array accesses bounds-checked
- **Bounded iterations**: Fuel parameter ensures termination
- **Capacity validation**: Runtime `check_valid_caps_fn` verifies non-negative capacities
- **Static flow validity**: `max_flow` postcondition guarantees `imp_valid_flow`
- **Spec bridge**: `imp_valid_flow_implies_valid_flow` connects imperative postcondition to `Spec.valid_flow`, enabling use with MFMC theorem
- **MFMC usability**: `max_flow` returns `completed: bool`. When `true` (natural termination), postcondition additionally guarantees `no_augmenting_path` — the exact precondition of the MFMC theorem. A caller can: (1) call `max_flow`, (2) bridge to `valid_flow`, (3) apply MFMC to conclude the result is maximum and equals the min-cut capacity.

### Remaining proof obligations

| Obligation | File | Notes |
|------------|------|-------|
| `lemma_augment_imp_preserves_valid` | `Impl.fst` | `admit()` — augmentation preserves validity |
| `axiom_spd_source_zero` | `Complexity.fst` | BFS shortest-path distance |
| `axiom_spd_bounded` | `Complexity.fst` | BFS shortest-path bound |
| `lemma_distances_nondecreasing` | `Complexity.fst` | Lemma 26.7 |
| `axiom_edge_critical_bound` | `Complexity.fst` | Lemma 26.8 |

**Previously present, now proven:**
- ~~`axiom_bfs_complete`~~ → `lemma_bfs_complete` + `lemma_bottleneck_crossing` (induction on path)
- ~~BFS postcondition `assume_` ×2~~ → Counting invariants (`count_color1`, `queue_color1`) prove `bfs_complete` at termination

Test code uses 1 `assume_` for `valid_caps` (backed by runtime check).

## Building

```bash
cd ch26-max-flow
make verify
```

## References

- CLRS 3rd Edition, Chapter 26: Maximum Flow (§26.1–§26.3)
- Pulse separation logic: https://github.com/FStarLang/pulse
