# CLRS Chapter 35: 2-Approximation Vertex Cover

This directory contains a verified Pulse implementation of the 2-approximation vertex cover algorithm from CLRS Chapter 35.

## Algorithm

The APPROX-VERTEX-COVER algorithm is a greedy matching-based approach that provides a 2-approximation to the minimum vertex cover problem:

1. Start with an empty cover set C
2. While there exist uncovered edges:
   - Pick an arbitrary uncovered edge (u,v)
   - Add both u and v to C
   - Remove all edges incident on u or v

## Implementation

The implementation uses:
- **Graph representation**: Adjacency matrix `adj[i*n+j]` for an undirected graph with n vertices
- **Output**: Array `cover[i]` where `cover[i] = 1` if vertex i is in the cover, 0 otherwise
- **Simplified greedy approach**: Iterate through all edges in order, adding both endpoints to cover if neither is already covered

## Files

| File | Description |
|------|-------------|
| `CLRS.Ch35.VertexCover.Spec.fst` | Pure F* specification: types, graph predicates, counting functions |
| `CLRS.Ch35.VertexCover.Lemmas.fsti` | Interface for lemma signatures |
| `CLRS.Ch35.VertexCover.Lemmas.fst` | Proofs: counting lemmas, CLRS Theorem 35.1, 2-approximation ratio |
| `CLRS.Ch35.VertexCover.Complexity.fsti` | Interface for complexity definitions |
| `CLRS.Ch35.VertexCover.Complexity.fst` | O(V²) time bound proof |
| `CLRS.Ch35.VertexCover.Impl.fsti` | Public signature for the Pulse implementation |
| `CLRS.Ch35.VertexCover.Impl.fst` | Pulse implementation with correctness proof |

## Proven Properties

- ✅ **Valid cover**: every edge has ≥1 endpoint in the cover (`is_cover`)
- ✅ **Binary output**: all cover values are 0 or 1
- ✅ **2-approximation**: `|C| ≤ 2 · OPT` via `approximation_ratio_theorem`
- ✅ **Memory safety**: separation-logic framing via Pulse `pts_to`

## Verification

The implementation is fully verified in Pulse with:
- ✅ No `admit()` calls
- ✅ No `assume` statements  
- ✅ Proper resource management (no memory leaks)
- ✅ Separation logic specifications
- ✅ Loop invariants for nested loops
- ✅ Connection to pure specification

## Building

```bash
make verify
```

Or explicitly:

```bash
FSTAR_FILES="CLRS.Ch35.VertexCover.Impl.fst" make verify
```

### Constraints

- Graph size limited by `n * n` fitting in `SizeT` (i.e., `SZ.fits (n * n)`)
- Uses `A.alloc` (marked as deprecated but acceptable for model implementations)

## Dependencies

Requires Pulse library (located at `../../pulse` relative to this directory).
