# Dijkstra — Spec Validation Test (`CLRS.Ch24.Dijkstra.ImplTest.fst`)

## Test Instance

| Parameter | Value |
|-----------|-------|
| Vertices | 3 |
| Source | 0 |
| Edges | 0→1 (w=3), 0→2 (w=7), 1→2 (w=2) |

Adjacency matrix (row-major, `SP.inf` = no edge):
```
     0    1    2
0: [inf,  3,   7 ]
1: [inf, inf,  2 ]
2: [inf, inf, inf]
```

Expected shortest paths from source 0:
- `dist[0] = 0` (source)
- `dist[1] = 3` (direct edge 0→1)
- `dist[2] = 5` (path 0→1→2: 3+2=5 < 7)

## What Is Proven

### Precondition Satisfiability
- **`weights_in_range`**: Each finite weight w satisfies `|w|*(n-1) < inf`.
  With `inf = 1000000`: 3×2=6, 7×2=14, 2×2=4, all < 1000000. ✓
- **`all_weights_non_negative`**: All entries ≥ 0. ✓
- **`SZ.fits (3*3)`**: 9 fits in machine integers. ✓ (via `fits_at_least_16`)
- **`n > 0`, `source < n`**: Trivially satisfied. ✓

### Postcondition Precision
- **`sp_dist` normalization**: Using `friend CLRS.Ch24.ShortestPath.Inf` to see
  `inf = 1000000`, the normalizer fully evaluates `sp_dist` for each vertex:
  - `sp_dist(tw, 3, 0, 0) == 0` ✓
  - `sp_dist(tw, 3, 0, 1) == 3` ✓
  - `sp_dist(tw, 3, 0, 2) == 5` ✓
- **Completeness lemma (dist)**: The postcondition `forall v < 3. dist[v] == sp_dist(0, v)`
  combined with the computed `sp_dist` values uniquely determines `dist = [0, 3, 5]`.
- **Completeness lemma (pred)**: The `shortest_path_tree` postcondition gives
  `sp_dist(0,v) == sp_dist(0, pred[v]) + w(pred[v], v)` for each reachable non-source
  vertex. Case analysis on `pred[v] ∈ {0,1,2}` using the concrete sp_dist and weight
  values eliminates all but one option per vertex, uniquely determining `pred = [0, 0, 1]`.
- **Runtime verification**: After calling `dijkstra`, the test reads back `dist[0..2]`
  and `pred[0..2]`, asserts they match the proven values, and performs a computational
  check that survives extraction to C.

### Summary

| Property | Status |
|----------|--------|
| Precondition satisfiable | ✅ Proven |
| sp_dist computed for all vertices | ✅ `assert_norm` |
| Postcondition determines dist uniquely | ✅ Proven |
| Postcondition determines pred uniquely | ✅ Proven |
| Output values verified by reading | ✅ `assert (pure (...))` |
| No admits | ✅ |
| No assumes | ✅ |

## Technical Notes

- **`friend CLRS.Ch24.ShortestPath.Inf`**: Required to see the concrete value
  `inf = 1000000`, enabling `assert_norm` to fully evaluate `sp_dist`. Without
  friendship, `inf` is abstract (only `inf > 0` is known), making it impossible
  to prove `weights_in_range` for concrete non-zero weights or normalize `sp_dist`.
  An empty `.fsti` is required by F*'s friend mechanism.

- **`--z3rlimit 80 --fuel 4 --ifuel 2`**: Used for the Pulse test function to
  handle the array allocation/write/cleanup pattern and connect the postcondition
  to the completeness lemma.

## Spec Assessment

The Dijkstra `Impl.fsti` specification is **fully precise**: the postcondition
`dist[v] == sp_dist(source, v)` uniquely determines the output for any input.
No spec issues found.

## Concrete Execution (C Extraction)

The verified Dijkstra implementation is extracted to C via F*'s `--codegen krml`
and KaRaMeL, then compiled and executed on the same test instance.

**Command**: `make test-c`

**Output**:
```
Dijkstra (3 vertices, source=0):
  dist = [0, 3, 5]
  pred = [0, 0, 1]
  result: PASS
```

The extracted C code matches the F*-proven expected distances exactly.
The predecessor array `pred = [0, 0, 1]` encodes the shortest-path tree:
- vertex 0: self (source)
- vertex 1: predecessor 0 (edge 0→1, weight 3)
- vertex 2: predecessor 1 (path 0→1→2, weight 3+2=5)

| Property | Status |
|----------|--------|
| Extraction to C via krml | ✅ |
| Compilation with gcc | ✅ |
| Runtime output matches expected | ✅ dist=[0,3,5], pred=[0,0,1] |
