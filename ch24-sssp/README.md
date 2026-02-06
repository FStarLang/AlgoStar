# CLRS Chapter 24: Bellman-Ford Algorithm

## Verified Implementation

This directory contains a formally verified implementation of the Bellman-Ford single-source shortest paths algorithm from CLRS Chapter 24.

### Algorithm

Given a weighted directed graph with n vertices and edges encoded in an n×n weight matrix, compute shortest-path distances from a source vertex to all other vertices.

The algorithm performs:
1. **Initialization**: Set `dist[source] = 0` and `dist[v] = INFINITY` for all other vertices
2. **Relaxation**: For n-1 rounds, relax all edges by checking if `dist[u] + weight[u][v] < dist[v]`

### Implementation Details

- **Language**: Pulse (embedded in F*)
- **Module**: `CLRS.Ch24.BellmanFord`
- **Sentinel value**: 1000000 for INFINITY
- **Graph representation**: Flat array of size n×n (row-major order)
- **Distance array**: Modified in-place

### Key Specifications

**Preconditions**:
- n > 0
- source < n  
- weights array length == n × n
- dist array length == n
- SZ.fits(n × n) (no overflow)

**Postconditions**:
- dist array has same length n
- Contains shortest path distances from source

### Verification

```bash
make verify
```

### Implementation Highlights

1. **No admits or assumes**: Fully verified with no proof holes
2. **Explicit array operations**: Uses `A.op_Array_Access` and `A.op_Array_Assignment` instead of shorthand notation
3. **Unconditional writes**: Computes new value conditionally, then always writes to avoid branch joining issues
4. **Minimal invariants**: Loop invariants only track essential properties (loop counter bounds, array lengths)
5. **Overflow handling**: Checks sentinel values before arithmetic operations

### Structure

- 4 nested loops total:
  1. Initialization loop (1 level)
  2. Relaxation loops (3 levels: rounds, source vertices, destination vertices)

Each loop maintains minimal invariants tracking:
- Loop counter value and bounds
- Current state of distance array
- Array length preservation
