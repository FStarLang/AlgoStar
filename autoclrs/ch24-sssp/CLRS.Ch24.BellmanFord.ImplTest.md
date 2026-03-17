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
- **Conditional completeness**: The postcondition says
  `no_neg_cycles_flat ∧ no_neg_cycle == true ⟹ dist[v] == sp_dist(v)`.
  The test proves the conditional assertion:
  ```
  no_neg_cycle == true ==> dist[0]==0 ∧ dist[1]==4 ∧ dist[2]==2
  ```
  This shows the postcondition is **sufficiently precise** when no negative
  cycle exists: it uniquely determines the output.

### Summary

| Property | Status |
|----------|--------|
| Precondition satisfiable | ✅ Proven |
| sp_dist computed for all vertices | ✅ |
| no_neg_cycles_flat proven | ✅ |
| dist[source] == 0 verified | ✅ |
| Conditional completeness (dist == expected when no_neg_cycle) | ✅ |
| No admits | ✅ |
| No assumes | ✅ |

## Technical Notes

- **`friend CLRS.Ch24.ShortestPath.Inf`**: Same as Dijkstra — required to see
  `inf = 1000000` for normalization. An empty `.fsti` is required.

- **sp_dist(2) normalization challenge**: The normalizer struggles with
  `sp_dist tw 3 0 2 == 2` because the computation involves the negative weight
  −2 in `sp_dist_k`'s mutual recursion. The proof works by providing Z3 with
  intermediate `sp_dist_k` values and concrete sequence element values via
  `assert_norm`, then using `--fuel 8 --ifuel 4 --z3rlimit 200` for Z3 to
  unfold and verify the final computation.

- **Conditional vs unconditional completeness**: The BF postcondition conditions
  exact equality (`dist[v] == sp_dist(v)`) on two things:
  1. `no_neg_cycles_flat` — a mathematical property we prove for our graph
  2. `no_neg_cycle == true` — a runtime boolean the algorithm computes

  Since `no_neg_cycle` is existentially bound in the Pulse postcondition (a ghost
  variable), we cannot branch on it. Instead, the test asserts the implication
  `no_neg_cycle == true ==> dist == expected`. This is a limitation of the
  testing methodology in Pulse, not of the specification.

- **`R.alloc` deprecation warning**: The BF API takes `result: R.ref bool` as a
  parameter, requiring the test to allocate a mutable reference. `R.alloc` is
  deprecated in Pulse (marked unsound for model implementations). This produces
  warnings but does not affect verification correctness of the test.

## Spec Assessment

The Bellman-Ford `Impl.fsti` specification is **sufficiently precise**: under
`no_neg_cycles_flat ∧ no_neg_cycle == true`, the postcondition uniquely
determines the output. No spec incompleteness or imprecision issues found.

### Minor Observation

The postcondition's dependence on `no_neg_cycles_flat` (a `prop` that must be
proven externally by the caller) means the test cannot unconditionally verify
exact equality — it requires proving a non-trivial mathematical property about
the graph. While this is inherent to the Bellman-Ford algorithm's correctness
theorem, it makes testing more complex than Dijkstra's unconditional
`dist[v] == sp_dist(v)`.
