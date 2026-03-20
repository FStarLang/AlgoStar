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

## MST Proof Infrastructure

All MST proof infrastructure is **fully verified with zero admits**:

**Core Safety:**
- `greedy_safety_step`: Adding min-weight cross-component edge preserves safety ✅
- `edges_safe`: Clean safety predicate (edges ⊆ some MST) ✅
- `adj_weight`: Safe adj matrix indexing (bundles NL arithmetic) ✅

**Transfer Lemmas:**
- `noRepeats_transfer`: w=1 noRepeats → weighted noRepeats ✅
- `acyclic_transfer`: w=1 acyclic → weighted acyclic ✅
- `reachable_weighted_to_unweighted` + `reachable_unweighted_to_weighted` ✅

**UF Completeness (zero admits):**
- `uf_complete_init`, `uf_complete_union`, `uf_complete_eq`, `uf_complete_unreachable` ✅
- Full equivalence: `find(u) = find(v) ⟺ reachable(forest, u, v)` ✅

**Bridging:**
- `pure_kruskal_is_mst`: Pure spec produces MST for connected graphs ✅
- `scan_min_inv`: Minimum-weight cross-component edge tracking ✅
- `adj_graph_edge_weight`, `adj_graph_edge_ge_scanmin` ✅

**Remaining for Pulse postcondition upgrade to `is_mst`:**
- Integrate `greedy_safety_step` + `uf_complete` into Pulse outer loop invariant
- Track `ec == round` for connected graphs (needs cross-component edge existence)
- Surface MST property to `kruskal` postcondition

## Conclusion

**Satisfiability**: ✓ proven
**Forest verification**: ✓ edge count bounded, endpoints valid, acyclicity, edge provenance
**MST infrastructure**: ✓ all pure lemmas proven — **zero admits**
**MST (pure spec)**: ✓ `pure_kruskal_is_mst` proves MST for connected graphs
**Safety step**: ✓ `greedy_safety_step` proven via Bridge + UF completeness
**MST (Pulse postcondition)**: pending loop invariant integration
