# Kruskal's Algorithm — Spec Validation Test

**File**: `CLRS.Ch23.Kruskal.ImplTest.fst`
**Status**: ✅ Verified (no admits, no assumes)

## Test Instance

3-vertex triangle graph:
```
  0 --1-- 1 --2-- 2
  |               |
  +------3--------+
```
Adjacency matrix (flat 3×3): `[0, 1, 3, 1, 0, 2, 3, 2, 0]`
Expected MST: edges `{(0,1) w=1, (1,2) w=2}`, total weight = 3

## What Was Proven

### ✅ Precondition Satisfiability

The test constructs a valid input and calls `kruskal`, proving all
preconditions are satisfiable:

| Precondition | Concrete Value | Status |
|--------------|---------------|--------|
| `SZ.v n > 0` | 3 > 0 | ✅ Automatic |
| `Seq.length sadj == n * n` | 9 == 9 | ✅ From array writes |
| `Seq.length sedge_u == n` | 3 == 3 | ✅ From V.alloc |
| `Seq.length sedge_v == n` | 3 == 3 | ✅ From V.alloc |
| `SZ.fits (n * n)` | `SZ.fits 9` | ✅ Via `fits_at_least_16` (9 < 2¹⁶) |

### ✅ Partial Postcondition Verification (via elim lemmas)

We use `result_is_forest_adj_elim` and `result_is_forest_adj_forest_elim`
to expose concrete facts from the opaque postcondition:

| Property | Status | How |
|----------|:------:|-----|
| Edge count ≤ n-1 = 2 | ✅ | `result_is_forest_adj_elim` |
| Output array lengths correct | ✅ | `result_is_forest_adj_elim` |
| All endpoints valid (< n) | ✅ | `result_is_forest_adj_elim` |
| Edges from positive adj entries | ✅ | `result_is_forest_adj_elim` |
| Result is a forest (acyclic) | ✅ | `result_is_forest_adj_forest_elim` |
| Edge count = 2 exactly | ❌ | Forest, not spanning tree |
| Specific edge endpoints | ❌ | Multiple valid forests exist |
| Result is spanning tree | ❌ | Not in postcondition |
| Result is MST | ❌ | Not in postcondition |

## Spec Improvements Made

### Added: `result_is_forest_adj_elim` (Impl.fsti)

```fstar
val result_is_forest_adj_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires result_is_forest_adj sadj seu sev n ec)
    (ensures
      ec <= n - 1 /\
      Seq.length seu == n /\ Seq.length sev == n /\
      Seq.length sadj == n * n /\ n > 0 /\
      (forall (k:nat). k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index seu k < n /\
        Seq.index sev k >= 0 /\ Seq.index sev k < n /\
        Seq.index sadj (Seq.index seu k * n + Seq.index sev k) > 0))
```

This lemma exposes array-level facts from the previously completely opaque
`result_is_forest_adj` postcondition.

### Added: `result_is_forest_adj_forest_elim` (Impl.fsti)

```fstar
val result_is_forest_adj_forest_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires result_is_forest_adj sadj seu sev n ec)
    (ensures
      ec <= n - 1 /\ n > 0 /\
      Seq.length seu == n /\ Seq.length sev == n /\
      (forall (k:nat). k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
      KSpec.is_forest (edges_from_arrays seu sev ec 0) n)
```

This lemma exposes the **structural forest property**: the selected edges
form an acyclic subgraph. This is the key structural invariant maintained
by Kruskal's algorithm. Previously, external consumers could only see
array-level facts; now they can access the graph-theoretic `is_forest`
predicate directly.

## MST Infrastructure Status

The Pulse postcondition proves the result is a **forest** (acyclic subgraph)
with edges from the adjacency matrix. Extensive infrastructure is now proven
(zero admits) for connecting to MST via the `kruskal_result_is_mst` bridge:

**Proven (7 of 10 bridge preconditions):**

| Precondition | Lemma |
|---|---|
| `result_is_forest_adj` | Kruskal postcondition |
| `subset_edges wes g.edges` | `weighted_edges_subset_graph` |
| `acyclic g.n wes` | `acyclic_transfer` |
| `noRepeats_edge wes` | `noRepeats_transfer` |
| Valid graph edges | `adj_graph_valid_edges` |
| UF completeness | `uf_complete_init/union/eq/unreachable` |
| Scan minimality | `scan_min_inv` + `scan_min_inv_complete` |

**Remaining for MST (3 preconditions need loop invariant changes):**
- `length wes = n-1` (needs `ec == n-1` tracking for connected graphs)
- `all_connected g.n wes` (follows from ec=n-1 + acyclic)
- Safety `⊆ some MST` (needs `greedy_step_safe` at each loop step)

## Conclusion

**Satisfiability**: ✓ proven
**Forest verification**: ✓ edge count bounded, endpoints valid, acyclicity, edge provenance
**MST infrastructure**: ✓ all pure lemmas proven (UF completeness, transfer, scan min)
**MST (pure spec)**: ✓ `pure_kruskal_is_mst` proves MST for connected graphs
**MST (Pulse postcondition)**: pending loop invariant integration
