# Matrix Multiply — Spec Validation Test

## Test File

`CLRS.Ch04.MatrixMultiply.ImplTest.fst`

Adapted from the reference test at:
https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch04-divide-conquer/Test.MatrixMultiply.fst

## What Is Tested

One test function exercises the `matrix_multiply` API from
`CLRS.Ch04.MatrixMultiply.Impl.fsti` on a 2×2 instance:

### Test: `test_matrix_multiply_2x2`

- **Input**:
  - A = `[[1,2],[3,4]]` (flat: `[1,2,3,4]`)
  - B = `[[5,6],[7,8]]` (flat: `[5,6,7,8]`)
- **Expected output**:
  - C = `[[19,22],[43,50]]` (flat: `[19,22,43,50]`)
- **Hand calculation**:
  - C[0][0] = 1·5 + 2·7 = 5 + 14 = 19
  - C[0][1] = 1·6 + 2·8 = 6 + 16 = 22
  - C[1][0] = 3·5 + 4·7 = 15 + 28 = 43
  - C[1][1] = 3·6 + 4·8 = 18 + 32 = 50

### What Is Proven

1. **Precondition satisfiability**: `n > 0`, `SZ.fits(n*n)`, and length
   constraints are all satisfied for `n = 2`.

2. **Postcondition precision**: From `mat_mul_correct sa sb sc' 2`, the test
   derives exact values for all 4 output entries:
   - `Seq.index sc' 0 == 19`
   - `Seq.index sc' 1 == 22`
   - `Seq.index sc' 2 == 43`
   - `Seq.index sc' 3 == 50`

3. **Concrete value verification**: The test reads each output element from
   the array and asserts the expected value (`c00 == 19`, etc.).

4. **Complexity exactness**: The test asserts `cf == 8` (exactly `n³ = 2³ = 8`
   multiply-add operations). The `complexity_bounded_cubic` predicate is
   transparent (defined in `Spec.fst`), allowing this verification.

### Proof Technique

A helper lemma `mm_dot_products` connects the ghost sequences (from array
writes, represented as `Seq.upd` chains) to concrete `Seq.seq_of_list`
representations via `Seq.lemma_eq_intro` (extensional equality). This allows
`assert_norm` to evaluate `dot_product_spec` on the concrete sequences.

## Spec Completeness Assessment

The `mat_mul_correct` postcondition is **fully precise**:

- It specifies `Seq.index sc' (flat_index n i j) == dot_product_spec sa sb n i j n`
  for all `(i,j)`, which is the **exact** mathematical definition of matrix
  multiplication.

- For any concrete inputs, the postcondition uniquely determines every
  output entry.

**No spec weaknesses found.** The postcondition is both satisfiable and
complete.

## Verification Status

- **Zero admits, zero assumes**
- Verified with `--z3rlimit 80 --fuel 2 --ifuel 2`

## Concrete Execution Status

Successfully extracted to C and executed.

### Extraction pipeline

1. **F* → KaRaMeL IR**: `fstar --codegen krml --extract_module`
2. **KaRaMeL IR → C**: `krml -bundle ... -add-include '"krml/internal/compat.h"'`
3. **C → executable**: linked with `libkrmllib.a` (provides `Prims_op_*` for
   checked integer arithmetic)

### Test output

```
Matrix Multiply - 2x2... PASS
```

### Build

```
make extract   # Extract to C
make test      # Extract, compile, link, and run
```
