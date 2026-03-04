# Floyd-Warshall All-Pairs Shortest Paths

## Overview

This is a **fully verified** Pulse implementation of the Floyd-Warshall algorithm from CLRS Chapter 25 (All-Pairs Shortest Paths).

## Algorithm

The Floyd-Warshall algorithm computes shortest-path weights between all pairs of vertices in a weighted directed graph. It uses dynamic programming with a 2D table and runs in O(n³) time.

Given an n×n adjacency/weight matrix W, the algorithm iteratively improves path estimates:

```
for k = 0 to n-1:
  for i = 0 to n-1:
    for j = 0 to n-1:
      D[i][j] = min(D[i][j], D[i][k] + D[k][j])
```

## Implementation Details

### Data Representation
- Graph stored as a **flat array** of size n×n (row-major layout)
- Element at row i, column j is at index: `i * n + j`
- Uses `1000000` as sentinel value for "infinity" (no edge)
- In-place updates to the distance matrix

### Type Signature

```pulse
fn floyd_warshall
  (dist: array int)
  (#contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires 
    A.pts_to dist contents **
    pure (
      SZ.v n > 0 /\
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _:unit
  ensures exists* contents'. 
    A.pts_to dist contents' **
    pure (
      Seq.length contents' == SZ.v n * SZ.v n /\
      contents' == fw_outer contents (SZ.v n) 0
    )
```

### Key Features

✅ **NO admits** - All proofs are complete  
✅ **NO assumes** - All preconditions established  
✅ **Memory safe** - All array accesses proven in bounds  
✅ **Low rlimit** - All queries succeed with rlimit ≤40  
✅ **Minimal invariants** - Simple loop invariants tracking array ownership and length  
✅ **Correctness spec** - `contents' == fw_outer` proves output matches the recurrence (Spec.fst)  
✅ **Concrete tests** - SpecTest.fst verifies all 9 output entries of a 3×3 graph  
✅ **Walk formalism** - Paths.fst defines walks, proves base case, outlines path to δ(i,j) (no admits)

### Implementation Patterns

The implementation follows critical Pulse patterns for robust verification:

1. **Explicit array operations**: Uses `A.op_Array_Access` and `A.op_Array_Assignment` instead of shorthand notation
2. **Unconditional writes**: Computes new value first, then writes unconditionally (avoids ghost context issues)
3. **Clean loop invariants**: Uses `invariant exists* ...` pattern (not `invariant b. exists*`)
4. **Index arithmetic**: Proper use of `FStar.Mul` for size arithmetic with `*^` operator

## Verification

```bash
cd ch25-apsp
make
```

## Example Usage

See `CLRS.Ch25.FloydWarshall.Test.fst` for a complete example with a 3×3 graph.

## Files

| File | Purpose |
|------|---------|
| `CLRS.Ch25.FloydWarshall.Spec.fst` | Pure specification: `fw_entry` recurrence, `fw_inner_j/i`, `fw_outer`, safety predicates, length lemmas |
| `CLRS.Ch25.FloydWarshall.Lemmas.fsti` | Interface for correctness lemma signatures |
| `CLRS.Ch25.FloydWarshall.Lemmas.fst` | Correctness proofs: `fw_outer ≡ fw_entry` (main theorem) |
| `CLRS.Ch25.FloydWarshall.Paths.fst` | Walk formalism connecting fw_entry to graph-theoretic paths |
| `CLRS.Ch25.FloydWarshall.Complexity.fsti` | Interface for complexity bound definition and signature |
| `CLRS.Ch25.FloydWarshall.Complexity.fst` | O(n³) ghost-tick complexity proof |
| `CLRS.Ch25.FloydWarshall.Impl.fsti` | Interface for the imperative Floyd-Warshall entry point |
| `CLRS.Ch25.FloydWarshall.Impl.fst` | Pulse implementation proven equivalent to `fw_outer` |
| `CLRS.Ch25.FloydWarshall.SpecTest.fst` | Concrete 3×3 test verification (all 9 entries + no-neg-cycle) |
| `CLRS.Ch25.FloydWarshall.Test.fst` | Pulse compilation/runtime test |

## Verification Statistics

All queries succeed quickly:
- Total queries: ~20
- Max rlimit used: 40
- All proofs stable and fast

## References

- **CLRS**: Introduction to Algorithms, Chapter 25
- **Pulse**: Concurrent Separation Logic DSL in F* (https://fstar-lang.org)
