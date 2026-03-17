# Bellman-Ford — Spec Validation Test (`CLRS.Ch24.BellmanFord.ImplTest.fst`)

## Test Instance

| Parameter | Value |
|-----------|-------|
| Vertices | 3 |
| Source | 0 |
| Edges | 0→1 (w=4), 0→2 (w=5), 1→2 (w=−2) |

Adjacency matrix (row-major, `SP.inf` = no edge):
```
     0    1    2
0: [inf,  4,   5 ]
1: [inf, inf, -2 ]
2: [inf, inf, inf]
```

Contains a **negative-weight edge** (1→2: −2) but **no negative cycle**.

Expected shortest paths from source 0:
- `dist[0] = 0` (source)
- `dist[1] = 4` (direct edge 0→1)
- `dist[2] = 2` (path 0→1→2: 4+(−2) = 2 < 5)
- `no_neg_cycle = true`

## What Is Proven

### Precondition Satisfiability
- **`weights_in_range`**: Each finite weight w satisfies `|w|*(n-1) < inf` and
  `w*(n-1) > -inf`. With `inf = 1000000`: 4×2=8, 5×2=10, |−2|×2=4, all < 1000000;
  (−2)×2=−4 > −1000000. ✓
- **`SZ.fits (3*3)`**: 9 fits in machine integers. ✓
- **`n > 0`, `source < n`**: Trivially satisfied. ✓

### Postcondition Precision
- **`sp_dist` normalization**: Using `friend CLRS.Ch24.ShortestPath.Inf` to see
  `inf = 1000000`:
  - `sp_dist(tw, 3, 0, 0) == 0` ✓ (`assert_norm`)
  - `sp_dist(tw, 3, 0, 1) == 4` ✓ (`assert_norm`)
  - `sp_dist(tw, 3, 0, 2) == 2` ✓ (Z3 with fuel 8, intermediate sp_dist_k hints)
- **`no_neg_cycles_flat`**: Proven with high fuel/rlimit, establishing that an
  extra relaxation pass doesn't improve any distance.
- **Unconditional properties**: `dist[source] == 0` verified by reading dist[0].
- **Unconditional completeness**: The new postcondition guarantees
  `no_neg_cycles_flat ==> no_neg_cycle == true`. Since we proved
  `no_neg_cycles_flat` for the test graph, `no_neg_cycle == true` follows
  unconditionally. Combined with the equality clause, the test now asserts
  unconditional dist equality:
  ```
  no_neg_cycle == true
  dist[0]==0 ∧ dist[1]==4 ∧ dist[2]==2
  ```
  This is a strict improvement over the previous conditional assertion.

### Summary

| Property | Status |
|----------|--------|
| Precondition satisfiable | ✅ Proven |
| sp_dist computed for all vertices | ✅ |
| no_neg_cycles_flat proven | ✅ |
| dist[source] == 0 verified | ✅ |
| no_neg_cycle == true verified (unconditional) | ✅ |
| Unconditional completeness (dist == expected) | ✅ |
| No admits | ✅ |
| No assumes | ✅ |

## Technical Notes

- **`friend CLRS.Ch24.ShortestPath.Inf`**: Same as Dijkstra — required to see
  `inf = 1000000` for normalization. An empty `.fsti` is required.

- **Unconditional vs conditional completeness**: With the new postcondition
  `no_neg_cycles_flat ==> no_neg_cycle == true`, the test can now make
  unconditional assertions. Since we prove `no_neg_cycles_flat` for our test
  graph, we derive `no_neg_cycle == true` and therefore `dist == sp_dist`
  unconditionally. This eliminates the previous limitation where the test
  could only assert the implication `no_neg_cycle == true ==> dist == expected`.

## Spec Assessment

The Bellman-Ford `Impl.fsti` specification is **fully precise**: under
`no_neg_cycles_flat`, the postcondition guarantees `no_neg_cycle == true`
and uniquely determines `dist = [0, 4, 2]`. No spec incompleteness or
imprecision issues found.

### Minor Observation

The postcondition's dependence on `no_neg_cycles_flat` (a `prop` that must be
proven externally by the caller) means the test cannot unconditionally verify
exact equality — it requires proving a non-trivial mathematical property about
the graph. While this is inherent to the Bellman-Ford algorithm's correctness
theorem, it makes testing more complex than Dijkstra's unconditional
`dist[v] == sp_dist(v)`.
