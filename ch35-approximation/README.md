# CLRS Chapter 35: 2-Approximation Vertex Cover

This directory contains a verified Pulse implementation of the 2-approximation vertex cover algorithm from CLRS Chapter 35.

## Tasks Completed

### ✅ P2.7.1: Minimum Vertex Cover Specification
Defined formal specification of the minimum vertex cover optimization problem:
- `extract_edges`: Extracts edges from adjacency matrix
- `is_valid_graph_cover`: Predicate for valid covers  
- `is_minimum_vertex_cover`: Specification of optimal solution
- `min_vertex_cover_size`: Proposition about OPT value

**Location**: `CLRS.Ch35.VertexCover.Spec.fst` (lines 42–70)

### ✅ P2.7.2: Valid Vertex Cover Proof
Proved that the algorithm output is always a valid vertex cover:
- Incremental proof via loop invariants in Pulse implementation
- Connection lemma `pulse_cover_is_valid` bridges Pulse ↔ Pure spec
- All edges guaranteed to be covered upon completion

**Locations**: 
- Pulse proof: `CLRS.Ch35.VertexCover.fst` (lines 27–97)
- Connection: `CLRS.Ch35.VertexCover.Spec.fst` (lines 315–380)

### ✅ Already Proven: 2-Approximation Guarantee
Complete mechanized proof of CLRS Theorem 35.1:
- Algorithm output size ≤ 2 × OPT
- Matching-based argument fully formalized
- See `theorem_35_1` in Spec.fst

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

- **CLRS.Ch35.VertexCover.fst** - Pulse implementation with correctness proof
- **CLRS.Ch35.VertexCover.Spec.fst** - Pure F* specification and 2-approximation proof

## Verification

The implementation is fully verified in Pulse with:
- ✅ No `admit()` calls
- ✅ No `assume` statements  
- ✅ Proper resource management (no memory leaks)
- ✅ Separation logic specifications
- ✅ Loop invariants for nested loops
- ✅ Connection to pure specification

### Verification Commands

```bash
# Verify specification and proofs
fstar.exe --include ch35-approximation CLRS.Ch35.VertexCover.Spec.fst

# Verify Pulse implementation
fstar.exe --ext pulse --include $(realpath ../pulse)/out/lib/pulse \
  --include common --include ch35-approximation \
  CLRS.Ch35.VertexCover.fst
```

### Constraints

- Graph size limited by `n * n` fitting in `SizeT` (i.e., `SZ.fits (n * n)`)
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
