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

## Verification

The implementation is fully verified in Pulse with:
- ✅ No `admit()` calls
- ✅ No `assume` statements  
- ✅ Proper resource management (no memory leaks)
- ✅ Separation logic specifications
- ✅ Loop invariants for nested loops

### Constraints

- Graph size limited to n < 256 vertices to ensure n² fits in size_t
- Uses `A.alloc` (marked as deprecated but acceptable for model implementations)

## Building

```bash
make verify
```

Or explicitly:

```bash
FSTAR_FILES="CLRS.Ch35.VertexCover.fst" make verify
```

## Dependencies

Requires Pulse library (located at `../../pulse` relative to this directory).
