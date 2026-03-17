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

### ✅ Partial Postcondition Verification (via elim lemma)

We added `result_is_forest_adj_elim` to the `.fsti` to expose concrete
facts from the previously opaque postcondition:

| Property | Status | How |
|----------|:------:|-----|
| Edge count ≤ n-1 = 2 | ✅ | `result_is_forest_adj_elim` |
| Output array lengths correct | ✅ | `result_is_forest_adj_elim` |
| All endpoints valid (< n) | ✅ | `result_is_forest_adj_elim` |
| Edges from positive adj entries | ✅ | `result_is_forest_adj_elim` |
| Edge count = 2 exactly | ❌ | Forest, not spanning tree |
| Specific edge endpoints | ❌ | Multiple valid forests exist |
| Result is spanning tree | ❌ | Not in postcondition |
| Result is MST | ❌ | Not in postcondition |

## Spec Improvement Made

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
`result_is_forest_adj` postcondition. It gives consumers:
- Edge count bound (forest has at most n-1 edges)
- Endpoint validity (all selected vertices are valid indices)
- Edge provenance (each selected edge has a positive adjacency matrix entry)

## Remaining Spec Weakness

The postcondition proves the result is a **forest** (acyclic subgraph)
but not a **spanning tree** (connected + n-1 edges). The edge count is
bounded by n-1 but could be less (e.g., 0 edges is a valid forest).

To prove the exact output for a concrete instance, the postcondition
would need to include `is_spanning_tree` or `is_mst`, which requires
strengthening the Pulse loop invariant to track connectivity/safety.

## Conclusion

**Satisfiability**: ✓ proven
**Partial verification**: ✓ edge count bounded, endpoints valid, edge provenance
**Completeness**: ✗ postcondition too weak — admits empty forests
