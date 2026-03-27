# Prim's Algorithm — Spec Validation Test

**File**: `CLRS.Ch23.Prim.ImplTest.fst`
**Status**: ✅ Verified — imperative Prim produces MST (zero admits in proof code)

## Test Instance

3-vertex triangle graph (source = vertex 0):
```
  0 --1-- 1 --2-- 2
  |               |
  +------3--------+
```
Weight matrix (flat 3×3, SZ.t): `[0, 1, 3, 1, 0, 2, 3, 2, 0]`
Expected MST: edges `{(0,1) w=1, (1,2) w=2}`

## What Is Proven

### ✅ Postcondition: `prim_correct` + `prim_mst_result`

| Property | Status | Source |
|----------|:------:|--------|
| `key[source] == 0` | ✅ | `prim_correct` |
| `parent[source] == source` | ✅ | `prim_correct` |
| `key[i] <= infinity` for all i | ✅ | `all_keys_bounded` |
| `parent[v] < n` for all v | ✅ | `parent_valid` |
| `key[v] == weights[parent[v]*n+v]` | ✅ | `key_parent_consistent` |
| **Result is MST** | ✅ | `prim_mst_result` → `prim_mst_result_elim` → `is_mst` |

### ✅ MST Proof (imperative output)

The postcondition `prim_mst_result` proves that the edges extracted from
the parent/key arrays form a **minimum spanning tree** of the input graph.
This is proven via:

1. **Greedy safety** (cut property, CLRS Thm 23.1): each greedy step preserves
   the invariant that current edges are a subset of some MST
2. **Key invariant**: `key[v] ≤ weight(w,v)` for MST vertex w, non-MST vertex v
3. **Connectivity**: connected graph guarantees finite-key non-MST vertex exists
4. **Vertex counting**: after n iterations, all vertices are in MST
5. **Post-loop derivation**: `n-1` edges + spanning + acyclic + safe → MST

Calling `prim_mst_result_elim` (given `symmetric_weights` + `all_connected`)
extracts `is_mst g (edges_from_parent_key parent_seq key_seq n source 0)`.

## Proof Architecture

| Module | Lines | Verification Time | Admits |
|--------|-------|-------------------|--------|
| `Defs.fst` | 68 | 1.5s | 0 |
| `KeyInv.fst` | 730 | 6s | 0 |
| `Greedy.fst` | 1060 | 45s | 0 |
| `Impl.fst` | 1010 | 69s | **0** |
| `ImplTest.fst` | 260 | 5s | 2 (test-only) |

## Test Admits (not proof gaps)

### 1. `SZ.fits_u64` (Platform Assumption)
64-bit SizeT — cannot be proven from first principles.

### 2. `test_graph_preconditions` (Normalization)
`valid_weights`, `symmetric_weights`, `all_connected`, `no_zero_edges` for
the concrete test data. These are verifiable by inspection but F*'s normalizer
can't reduce `weights_to_adj_matrix` (involves `Seq.init` with lambdas).

## API Gap

`prim` returns freshly allocated vecs but postcondition lacks `is_full_vec`,
preventing the caller from freeing them. Test uses `drop_` as workaround.
