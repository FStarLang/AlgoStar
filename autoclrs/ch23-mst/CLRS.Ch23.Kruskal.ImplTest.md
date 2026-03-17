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

### ❌ Postcondition Precision

The postcondition `result_is_forest_adj` is declared as an **opaque `val`**
in `CLRS.Ch23.Kruskal.Impl.fsti`:

```fstar
val result_is_forest_adj (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat) : prop
```

Since this is opaque to external consumers, the test **cannot verify**:

| Property | Verifiable? | Reason |
|----------|:-----------:|--------|
| Edge count = 2 | ❌ | `ec` is existentially quantified, opaque prop |
| Edge endpoints correct | ❌ | `sedge_u'`, `sedge_v'` are existential, no info extractable |
| Result is spanning tree | ❌ | Not part of postcondition at all |
| Result is MST | ❌ | Not part of postcondition at all |
| Result is a forest | ❌ | Buried inside opaque prop |

## Spec Weakness Analysis

### Root Cause: Opaque Postcondition

The Kruskal API's postcondition is completely opaque to external consumers.
While the implementation (`Impl.fst`) defines `result_is_forest_adj` as:
```
result_is_forest seu sev n ec ∧ edges_adj_pos sadj seu sev n ec
```
this definition is hidden behind the `val` declaration in `Impl.fsti`.

### Impact

A caller of `kruskal` receives a proof of an opaque proposition but cannot
extract any useful information from it. The caller cannot:

1. Determine how many edges were selected
2. Determine which specific edges were selected
3. Verify that the result is a spanning tree
4. Verify that the result is an MST

### Suggested Fix

To make the postcondition useful to external consumers, either:

1. **Expose the definition** by changing `val result_is_forest_adj ...` to
   `let result_is_forest_adj ...` in the `.fsti`
2. **Export intro/elim lemmas** that allow consumers to unfold and inspect
   the postcondition components
3. **Strengthen the postcondition** to include `is_spanning_tree` and
   `is_mst` directly (requires strengthening the loop invariant)

## Conclusion

**Satisfiability**: ✓ proven
**Completeness**: ✗ postcondition too opaque — no output information extractable
