# Prim's Minimum Spanning Tree Algorithm - Verified Pulse Implementation

This directory contains a verified implementation of Prim's MST algorithm from CLRS Chapter 23 in Pulse, the concurrent separation logic DSL embedded in F*.

## Files

- `CLRS.Ch23.Prim.fst` - Verified Pulse implementation of Prim's algorithm
- `Makefile` - Build configuration
- `_cache/` - F* verification cache

## Implementation Details

### Algorithm
Implements Prim's algorithm for finding minimum spanning trees using an adjacency matrix representation:
1. Initialize: key[v] = INFINITY for all v, key[source] = 0
2. Repeat n times:
   - Find vertex u not in MST with minimum key value  
   - Add u to MST
   - For each neighbor v of u: if weight(u,v) < key[v], update key[v]

### Key Features
✅ **Fully verified** - No admits, no assumes  
✅ **Proper Pulse syntax** - Uses `#lang-pulse` with explicit array operations  
✅ **Resource management** - Proper allocation and deallocation of arrays  
✅ **Unconditional writes** - All assignments outside conditionals as required  
✅ **Loop invariants** - Proper separation logic invariants with `exists*`  

### Specification
- **Input**: Weight matrix as flat array `weights[u*n+v]`, number of vertices `n`, source vertex
- **Output**: Array `key[v]` containing minimum edge weights to add each vertex to MST
- **Precondition**: `n > 0`, `n² < 2⁶⁴`, `source < n`, `SizeT.fits_u64` (64-bit platform)
- **Postcondition**: Output array has length `n`

### Technical Notes

1. **Infinity Value**: Uses `65535sz` instead of the CLRS value of 1000000 due to SizeT constraints

2. **Matrix Indexing**: Implements flat array indexing `weights[u*n+v]` using `U64.mul_mod` and `U64.add_mod` to avoid overflow checks, with a proved lemma that the result is correct when `n² < 2⁶⁴`

3. **Platform Requirement**: Requires `SizeT.fits_u64` (64-bit SizeT), which holds on 64-bit platforms

4. **Model Implementation**: Uses `Array.alloc` which is marked deprecated for model implementations only

## Building

```bash
cd /home/nswamy/workspace/clrs/ch23-mst
FSTAR_FILES="CLRS.Ch23.Prim.fst" make verify
```

## Verification

The implementation successfully verifies with F* with only deprecation warnings about `Array.alloc` being for model implementations.

Verification time: ~240 seconds
