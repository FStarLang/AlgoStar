# Kruskal's Algorithm — Verified Test

**File**: `CLRS.Ch23.Kruskal.ImplTest.fst`
**Status**: ✅ Verified — zero admits, zero assumes, output uniqueness proved

## Test Instance

3-vertex triangle graph:
```
  0 --1-- 1 --2-- 2
  |               |
  +------3--------+
```
Adjacency matrix (flat 3×3): `[0, 1, 3, 1, 0, 2, 3, 2, 0]`
Expected MST: edges `{(0,1) w=1, (1,2) w=2}`, total weight = 3

## What Is Proven

### ✅ Postcondition: `result_is_forest_adj` + `kruskal_mst_result`

| Property | Status | Source |
|----------|:------:|--------|
| Edge count ≤ n-1 = 2 | ✅ | `result_is_forest_adj_elim` |
| Output array lengths correct | ✅ | `result_is_forest_adj_elim` |
| All endpoints valid (< n) | ✅ | `result_is_forest_adj_elim` |
| Edges from positive adj entries | ✅ | `result_is_forest_adj_elim` |
| Result is a forest (acyclic) | ✅ | `result_is_forest_adj_forest_elim` |
| **Result is MST** | ✅ | `kruskal_mst_result` → `is_mst` |

### ✅ Concrete MST Uniqueness

From `is_mst` + concrete graph structure, the MST edges are uniquely determined:

| Property | Status | How |
|----------|:------:|-----|
| MST contains edge (0,1) w=1 | ✅ | `kruskal_mst_edges` |
| MST contains edge (1,2) w=2 | ✅ | `kruskal_mst_edges` |
| Total weight == 3 | ✅ | `kruskal_mst_edges` |

**Proof chain**: `is_mst` → `kruskal_witness_spanning_tree` (witness with weight 3
bounds total) → case analysis on graph edges (weight-3 edge eliminated by bound,
duplicate-(0,1) case eliminated by `both_01_not_connected` + `no_path_to_2`) →
only option is `{(0,1,1), (1,2,2)}`.

Unlike Prim (per-vertex key/parent arrays), Kruskal stores edges in discovery
order with arbitrary endpoint direction. So we prove **edge set membership**
(`mem_edge`, direction-insensitive) rather than specific array indices.

### ✅ Runtime Check (survives C extraction)

The function returns `bool` with `ensures pure (r == true)`:
- `sz_eq` comparisons check `ec=2` and edges `{(0,1),(1,2)}` in any order/direction
- The proof guarantees the runtime check always passes
- Extracted C code contains the actual comparisons (not erased)

## Proof Architecture

| Module | Role | Admits |
|--------|------|--------|
| `ImplTestHelper.fst` | MST proof + uniqueness lemmas | **0** |
| `ImplTest.fst` | Pulse test function | **0** |
| `Impl.fst` | Imperative Kruskal + MST elim | **0** |
| `Spec.fst` | Pure Kruskal + correctness | **0** |

## Key Helper Lemmas (ImplTestHelper)

- **`kruskal_witness_spanning_tree`**: `[{0,1,1}; {1,2,2}]` is a spanning tree
  with weight 3 (acyclicity via `acyclic_when_unreachable`)
- **`no_path_to_2`**: recursive — edges connecting only {0,1} can't reach vertex 2
- **`both_01_not_connected`**: two copies of edge (0,1) violate `all_connected`
- **`kruskal_mst_edges`**: from `is_mst` + witness, derives unique MST edges
