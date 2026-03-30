# Binary Search — Spec Validation Test

## Test File

`CLRS.Ch04.BinarySearch.ImplTest.fst`

## What Is Tested

Three test functions exercise the `binary_search` API from
`CLRS.Ch04.BinarySearch.Impl.fsti` on concrete instances:

### Test 1: `test_binary_search_found` — Key present

- **Input**: sorted array `[1, 3, 5]`, key = 3
- **Expected result**: `SZ.v result == 1` (found at index 1)
- **What is proven**:
  - The `is_sorted` precondition is satisfiable (Z3 verifies all 3 pairs)
  - The postcondition uniquely determines the result:
    - `result == 3` (not found) is contradicted by `s0[1] = 3`
    - `result == 0` is contradicted by `s0[0] = 1 ≠ 3`
    - `result == 2` is contradicted by `s0[2] = 5 ≠ 3`
    - Only `result == 1` satisfies `s0[result] == 3`
  - Complexity: `cf <= 2` (at most `⌊log₂ 3⌋ + 1 = 2` comparisons)

### Test 2: `test_binary_search_not_found` — Key absent

- **Input**: sorted array `[1, 3, 5]`, key = 2
- **Expected result**: `SZ.v result == 3` (sentinel = len, not found)
- **What is proven**:
  - The postcondition uniquely determines the result:
    - `result < 3` would require `s0[result] == 2`, but none of
      `s0[0]=1, s0[1]=3, s0[2]=5` equals 2
    - So `result == 3` (not found)
  - Complexity: `cf <= 2` (at most 2 comparisons)

### Test 3: `test_binary_search_empty` — Empty array

- **Input**: empty array `[]`, key = 1
- **Expected result**: `SZ.v result == 0` (sentinel = len = 0)
- **What is proven**:
  - The `is_sorted` precondition is vacuously true for empty sequences
  - `result <= 0` from postcondition, so `result == 0`
  - The `forall i < 0. ...` not-found clause is vacuously true
  - Complexity: `cf <= 1` (at most `⌊log₂ 0⌋ + 1 = 1` comparison)
  - Tests the boundary behavior of the implementation (empty array
    returns immediately without entering the loop)

## Spec Completeness Assessment

The `binary_search` postcondition is **fully precise** for concrete inputs:

1. **Found case**: `s0[result] == key` combined with concrete element values
   uniquely determines the index.

2. **Not found case**: `forall i < n. s0[i] ≠ key` combined with the
   dichotomy `result < len ∨ result == len` uniquely determines the sentinel.

3. **Empty array**: `result <= 0` immediately gives `result == 0`.

4. **Precondition**: `is_sorted s0` is satisfiable and easily proven for
   small concrete sorted arrays (and vacuously true for empty arrays).

5. **Complexity**: `complexity_bounded_log` (transparent in Spec.fst) allows
   verification of the O(log n) comparison bound.

**No spec weaknesses found.** The postcondition is both satisfiable and
precise enough to uniquely determine the output for any concrete input.

## Verification Status

- **Zero admits, zero assumes**
- Verified with `--z3rlimit 10 --fuel 2 --ifuel 2`

## Runtime Assurance

Each test function returns `bool` with two layers of assurance:

1. **PROOF** (ghost, erased at extraction): Ghost assertions prove the
   postcondition uniquely determines the result. `ensures pure (r == true)`
   proves the runtime check always succeeds.
2. **RUNTIME** (computational, survives extraction to C): `sz_eq` comparisons
   produce a `bool` that is checked by the C test driver (`main.c`).

## Concrete Execution Status

Successfully extracted to C and executed. The `Pulse.Lib.BoundedIntegers`
dependency was removed from `Impl.fst` (operators on `SZ.t` already come from
`FStar.SizeT`; operators on `int` come from `Prims`).

### Extraction pipeline

1. **F* → KaRaMeL IR**: `fstar --codegen krml --extract_module`
2. **KaRaMeL IR → C**: `krml -bundle ... -add-include '"krml/internal/compat.h"'`
3. **C → executable**: linked with `libkrmllib.a` (provides `Prims_op_*` for
   checked integer arithmetic)

### Test output

```
=== CLRS Ch04 Verified Algorithm Tests ===

Binary Search - found case... PASS
Binary Search - not found case... PASS
Binary Search - empty array... PASS
Matrix Multiply - 2x2... PASS
Kadane Max Subarray - mixed array... PASS
Kadane Max Subarray - all negative... PASS

All 6 tests passed.
```

### Build

```
make extract   # Extract to C
make test      # Extract, compile, link, and run
```
