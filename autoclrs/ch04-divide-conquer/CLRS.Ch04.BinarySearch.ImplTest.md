# Binary Search — Spec Validation Test

## Test File

`CLRS.Ch04.BinarySearch.ImplTest.fst`

## What Is Tested

Two test functions exercise the `binary_search` API from
`CLRS.Ch04.BinarySearch.Impl.fsti` on a concrete sorted array `[1, 3, 5]`:

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

### Test 2: `test_binary_search_not_found` — Key absent

- **Input**: sorted array `[1, 3, 5]`, key = 2
- **Expected result**: `SZ.v result == 3` (sentinel = len, not found)
- **What is proven**:
  - The postcondition uniquely determines the result:
    - `result < 3` would require `s0[result] == 2`, but none of
      `s0[0]=1, s0[1]=3, s0[2]=5` equals 2
    - So `result == 3` (not found)

## Spec Completeness Assessment

The `binary_search` postcondition is **fully precise** for concrete inputs:

1. **Found case**: `s0[result] == key` combined with concrete element values
   uniquely determines the index.

2. **Not found case**: `forall i < n. s0[i] ≠ key` combined with the
   dichotomy `result < len ∨ result == len` uniquely determines the sentinel.

3. **Precondition**: `is_sorted s0` is satisfiable and easily proven for
   small concrete sorted arrays.

**No spec weaknesses found.** The postcondition is both satisfiable and
precise enough to uniquely determine the output for any concrete input.

## Verification Status

- **Zero admits, zero assumes**
- Verified with `--z3rlimit 60 --fuel 2 --ifuel 2`
