# CLRS Chapter 26: Maximum Flow (Edmonds-Karp)

## Overview

A verified implementation of the **Edmonds-Karp algorithm** (BFS-based Ford-Fulkerson method) for computing maximum flow in a network, following CLRS §26.2.

- **3321 lines** across 5 verified F\*/Pulse modules
- **Zero admits** in production code
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
- **BFS on residual graph** (`bfs_residual`): Standard BFS with color/pred/queue arrays
- **Bottleneck computation** (`find_bottleneck_imp`): Walks pred chain from sink to source
- **Flow augmentation** (`augment_imp`): Updates flow along the augmenting path
- **Runtime validity check** (`check_imp_valid_flow_fn`): Defense-in-depth postcondition

## Files

| File | Lines | Description |
|------|------:|-------------|
| `CLRS.Ch26.MaxFlow.Spec.fst` | 1125 | Pure spec: flow networks, residual graphs, augmenting paths, cuts, MFMC theorem |
| `CLRS.Ch26.MaxFlow.fst` | 913 | Imperative Pulse implementation: BFS-based Ford-Fulkerson (Edmonds-Karp) |
| `CLRS.Ch26.MaxFlow.Proofs.fst` | 679 | Proofs: augmentation preserves flow validity, increases flow value |
| `CLRS.Ch26.MaxFlow.Complexity.fst` | 548 | O(VE²) complexity analysis with ghost tick counter |
| `CLRS.Ch26.MaxFlow.Test.fst` | 56 | Smoke test on a 3-vertex graph |

## Verified Properties

### Spec-level (fully proven, zero admits)

| CLRS Result | Location |
|-------------|----------|
| Lemma 26.4: \|f\| = net flow across any cut | `Spec.fst` — `lemma_flow_value_eq_net_flow` |
| Corollary 26.5: Weak duality \|f\| ≤ c(S,T) | `Spec.fst` — `weak_duality` |
| Theorem 26.6: Max-flow min-cut | `Spec.fst` — `max_flow_min_cut_theorem` |
| Flow conservation preserved by augmentation | `Proofs.fst` — `augment_preserves_valid` |
| Capacity constraints preserved by augmentation | `Proofs.fst` — `lemma_augment_preserves_capacity` |
| Flow value strictly increases per augmentation | `Proofs.fst` — `augment_increases_value` |
| Zero flow is valid | `Proofs.fst` — `zero_flow_valid` |

### Complexity (O(VE²) arithmetic proven)

| CLRS Result | Location | Status |
|-------------|----------|--------|
| O(VE²) total cost bound | `Complexity.fst` — `edmonds_karp_complexity` | ✅ Proven |
| Each augmentation creates ≥1 critical edge | `Complexity.fst` — `lemma_augmentation_creates_critical_edge` | ✅ Proven |
| Distance monotonicity (Lemma 26.7) | `Complexity.fst` — `lemma_distances_nondecreasing` | ⚠️ Axiom (pending BFS proof) |
| Edge criticality bound (Lemma 26.8) | `Complexity.fst` — `axiom_edge_critical_bound` | ⚠️ Axiom (pending BFS proof) |

### Imperative level

- **Memory safety**: All array accesses bounds-checked
- **Bounded iterations**: Fuel parameter ensures termination
- **Flow validity**: Verified via runtime check (`check_imp_valid_flow_fn`) — returns `valid: bool`
- **No admits or assumes** in production code (1 `assume_` in test harness for `valid_caps`)

## Building

```bash
cd ch26-max-flow
make verify
```

## References

- CLRS 3rd Edition, Chapter 26: Maximum Flow (§26.1–§26.3)
- Pulse separation logic: https://github.com/FStarLang/pulse
