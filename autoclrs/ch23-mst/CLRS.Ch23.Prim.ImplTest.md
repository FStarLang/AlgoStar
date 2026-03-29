# Prim's Algorithm — Verified Test

**File**: `CLRS.Ch23.Prim.ImplTest.fst`
**Status**: ✅ Verified — zero admits in proof code, output uniqueness proved

## Test Instance

3-vertex triangle graph (source = vertex 0):
```
  0 --1-- 1 --2-- 2
  |               |
  +------3--------+
```
Weight matrix (flat 3×3, SZ.t): `[0, 1, 3, 1, 0, 2, 3, 2, 0]`
Expected MST: edges `{(0,1) w=1, (1,2) w=2}`, total weight = 3

## What Is Proven

### ✅ Postcondition: `prim_correct` + `prim_mst_result`

| Property | Status | Source |
|----------|:------:|--------|
| `key[source] == 0` | ✅ | `prim_correct` |
| `parent[source] == source` | ✅ | `prim_correct` |
| `key[i] <= infinity` for all i | ✅ | `all_keys_bounded` |
| `parent[v] < n` for all v | ✅ | `parent_valid` |
| `key[v] == weights[parent[v]*n+v]` | ✅ | `key_parent_consistent` |
| **Result is MST** | ✅ | `prim_mst_result` → `is_mst` |

### ✅ Concrete Output Uniqueness

From `is_mst` + concrete graph structure, the output is uniquely determined:

| Property | Status | How |
|----------|:------:|-----|
| `key[1] == 1, parent[1] == 0` | ✅ | `mst_test_facts` + `prim_unique_output` |
| `key[2] == 2, parent[2] == 1` | ✅ | `mst_test_facts` + `prim_unique_output` |
| Total weight == 3 | ✅ | `witness_spanning_tree` bounds `is_mst` |

**Proof chain**: `is_mst` → `mst_edge_facts` (no self-loops, finite keys)
→ `mst_total_weight` (witness spanning tree with weight 3 bounds total)
→ `prim_unique_output` (eliminates all but one (key,parent) assignment).

### ✅ Runtime Check (survives C extraction)

The function returns `bool` with `ensures pure (r == true)`:
- `sz_eq` comparisons check `key=[0,1,2], parent=[0,0,1]`
- The proof guarantees the runtime check always passes
- Extracted C code contains the actual comparisons (not erased)

## Proof Architecture

| Module | Lines | Verification Time | Admits |
|--------|-------|-------------------|--------|
| `Defs.fst` | 68 | 1.5s | 0 |
| `KeyInv.fst` | 730 | 6s | 0 |
| `Greedy.fst` | 1060 | 45s | 0 |
| `Impl.fst` | 985 | 69s | **0** |
| `ImplTestHelper.fst` | ~290 | 41s | 0 |
| `ImplTest.fst` | ~300 | 11s | 1 (platform) |

## Admits

### `SZ.fits_u64` (Platform Assumption)
64-bit SizeT — deployment property of the target platform.
Not a spec or proof gap.

## API Gap

`prim` returns freshly allocated vecs but postcondition lacks `is_full_vec`,
preventing the caller from freeing them. Test uses `drop_` as workaround.
