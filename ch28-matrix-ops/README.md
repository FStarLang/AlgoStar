# CLRS Chapter 28: Matrix Operations

## Matrix Multiplication

This directory contains verified implementations of matrix multiplication from CLRS §4.2:
the standard triple-loop algorithm (Pulse) and Strassen's divide-and-conquer algorithm (pure F*).

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

- `CLRS.Ch28.MatrixMultiply.fst` - Verified Pulse implementation (~240 lines)
  with functional correctness and O(n³) complexity proof
- `CLRS.Ch28.Strassen.fst` - Strassen's divide-and-conquer algorithm in pure F*
  (~975 lines) with correctness proof (pointwise equivalence to standard multiply)
  and O(n^{lg 7}) complexity analysis
- `CLRS.Ch28.StrassenPulse.fst` - Imperative Pulse Strassen (~450 lines) with
  Vec allocation/deallocation, recursive `fn rec`, and bridging lemma to the
  functional spec (4 admits remaining, see file header)
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

## Strassen's Algorithm

A pure F* specification of Strassen's divide-and-conquer matrix multiplication
(CLRS §4.2, pp. 79–82). Requires square, power-of-2 matrices.

### Key Results

1. **Functional correctness**: Strassen's output equals the standard triple-loop
   multiply element-wise (`lemma_strassen_correct`)
2. **Complexity**: The number of scalar multiplications satisfies
   T(n) = 7^{log₂ n} = n^{lg 7} ≈ n^{2.807}, proven strictly less than n³

### Proof Highlights

- Pointwise equivalence to `standard_multiply` via structural induction
- Four algebraic distributivity lemmas expand P1–P7 symbolically
- Connection lemmas bridge quadrant-level dot products to full-matrix dot products
- `smt_sync'` tactic used for quadrant case proofs to avoid solver timeout
- Zero admits, zero assumes
