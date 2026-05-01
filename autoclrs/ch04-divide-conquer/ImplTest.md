# CLRS Chapter 4: Divide and Conquer — Implementation Test Results

## Overview

Three verified Pulse implementations are extracted to C via KaRaMeL and
executed as concrete tests:

| Algorithm | Module | Tests |
|-----------|--------|-------|
| Binary Search | `CLRS.Ch04.BinarySearch.Impl` | 3 |
| Matrix Multiply (O(n³)) | `CLRS.Ch04.MatrixMultiply.Impl` | 1 |
| Kadane's Max Subarray | `CLRS.Ch04.MaxSubarray.Kadane` | 2 |

## Concrete Execution Results

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

**All 6 tests pass.** Exit code: 0.

## Test Details

### Binary Search (`CLRS.Ch04.BinarySearch.ImplTest`)

| Test | Input | Target | Expected | Verified |
|------|-------|--------|----------|----------|
| Found | `[1, 3, 5]` | 3 | index 1 | ✅ |
| Not found | `[1, 3, 5]` | 2 | sentinel (len=3) | ✅ |
| Empty | `[]` | 1 | sentinel (len=0) | ✅ |

Complexity bounds also verified: ≤ ⌊log₂ n⌋ + 1 comparisons.

### Matrix Multiply (`CLRS.Ch04.MatrixMultiply.ImplTest`)

| Test | A | B | Expected C | Verified |
|------|---|---|------------|----------|
| 2×2 | `[[1,2],[3,4]]` | `[[5,6],[7,8]]` | `[[19,22],[43,50]]` | ✅ |

Complexity bound also verified: exactly n³ = 8 multiply-add operations.

### Kadane Max Subarray (`CLRS.Ch04.MaxSubarray.Kadane.ImplTest`)

| Test | Input | Expected | Verified |
|------|-------|----------|----------|
| Mixed | `[-1, 3, -2]` | 3 | ✅ |
| All negative | `[-5, -3, -1]` | -1 | ✅ |

Complexity bound also verified: exactly n = 3 operations per test.

## Two Layers of Assurance

1. **PROOF (ghost, erased at extraction):** Ghost Pulse assertions prove the
   postcondition uniquely determines the result from the specification. These
   are checked by F*/Z3 at verification time and erased by KaRaMeL.

2. **RUNTIME (computational, survives extraction to C):** Concrete equality
   checks produce a `bool` that is returned to the C test driver (`main.c`).
   The driver prints PASS/FAIL and exits nonzero on any failure.

## Build Commands

```bash
make              # Verify all F* files
make extract      # Extract to C via KaRaMeL
make test-c       # Compile and run C tests
```

## Notes

- Strassen's algorithm exists only as a pure functional specification with
  correctness and complexity proofs — no imperative `Impl` or `ImplTest`.
- A `prims_compat.c` shim bridges the F*2 extraction naming (`Prims_op_Star`)
  with the krmllib runtime (`Prims_op_Multiply`) for integer multiplication.
- All arithmetic uses F*'s unbounded `int` type, extracted as
  `krml_checked_int_t` with runtime overflow checking.
