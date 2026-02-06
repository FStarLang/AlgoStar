# CLRS Chapter 28: Matrix Operations

## Matrix Multiplication

This directory contains a verified Pulse implementation of standard matrix multiplication from CLRS Chapter 28.

### Algorithm

Given two n×n matrices A and B stored as flat arrays in row-major order, compute their product C = A × B:

```
for i = 0 to n-1:
  for j = 0 to n-1:
    C[i*n+j] = 0
    for k = 0 to n-1:
      C[i*n+j] += A[i*n+k] * B[k*n+j]
```

### Files

- `CLRS.Ch28.MatrixMultiply.fst` - Verified Pulse implementation (170 lines)
- `Makefile` - Build configuration

### Verification

The implementation is formally verified with the following guarantees:

1. **Memory Safety**
   - All array accesses are within bounds
   - No buffer overflows or underflows
   - Index arithmetic checked for overflow via `SZ.fits`

2. **Resource Management**
   - Input arrays (a, b) read with fractional permissions
   - Output array (c) written with full permission
   - Array lengths preserved throughout

3. **Complete Proof**
   - No `admit()` or `assume` statements
   - Triple-nested loops with verified invariants
   - All separation logic obligations discharged

### Building

```bash
# Verify the implementation
make verify

# Or specify explicitly
FSTAR_FILES="CLRS.Ch28.MatrixMultiply.fst" make verify
```

### Implementation Notes

- Uses explicit array access operations: `A.op_Array_Access` and `A.op_Array_Assignment`
- Employs arithmetic lemma `index_bounds_lemma` to help SMT prove index bounds
- Loop invariants track array lengths and index bounds
- No shorthand array syntax (e.g., `a.(i)`) - all operations explicit for clarity

### Requirements

- F* with Pulse support
- PULSE_ROOT environment variable pointing to Pulse installation
- Standard Pulse libraries (included via Makefile)
