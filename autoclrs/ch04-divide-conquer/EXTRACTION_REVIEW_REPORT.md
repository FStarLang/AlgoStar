# Extraction Review Report — Chapter 04: Divide and Conquer

## Summary Checklist

### 1. All C code generated using krml from verified F*/Pulse code?

**YES.**

`main.c` is a handwritten C test driver that calls extracted test
functions and checks their `bool` return values, failing with a nonzero
exit code if any test returns `false`.

### 2. Makefiles canonical, reusing autoclrs.test.mk with no hacks?

**YES.**

The Makefile correctly includes `autoclrs.test.mk` and sets all required
variables (`CHAPTER_ID`, `KRML_INPUT_FILES`, `KRML_BUNDLE_FLAGS`,
`EXTRACT_C_FILES`). The `KRML_BUNDLE_FLAGS` includes both the API bundle
and a hide-bundle for `FStar.*,Pulse.*,PulseCore.*,Prims`.

Note: The Makefile defines a custom `.krml` extraction pattern using
`_krml_extracted` sentinel files. This is reasonable chapter-specific
boilerplate that could be factored into the shared mk in the future.

### 3. No handwritten code?

**PARTIALLY.** `main.c` is a handwritten test driver (follows the ch23-mst
pattern). All algorithm code is extracted from verified F*/Pulse.

### 4. C code generated for ImplTest files and their dependencies only?

**YES.** `ALL_EXTRACT_MODULES` correctly lists only:
- `CLRS.Ch04.BinarySearch.Impl`
- `CLRS.Ch04.MatrixMultiply.Impl`
- `CLRS.Ch04.MaxSubarray.Kadane`
- `CLRS.Ch04.BinarySearch.ImplTest`
- `CLRS.Ch04.MatrixMultiply.ImplTest`
- `CLRS.Ch04.MaxSubarray.Kadane.ImplTest`

Spec, Lemma, and Complexity modules are not extracted.

### 5. Extracted C contains concrete test execution with actual result checks?

**YES.**

All ImplTest functions return `bool` with two layers of assurance:

1. **PROOF** (ghost, erased at extraction): Ghost assertions prove the
   postcondition uniquely determines the result (e.g.,
   `assert (pure (SZ.v result == 1))`). The postcondition
   `ensures pure (r == true)` proves the runtime check always succeeds.

2. **RUNTIME** (computational, survives extraction to C): Concrete
   equality checks produce a `bool` that is returned to the C driver:
   - Binary Search: `sz_eq result expected_sz` (SizeT comparison)
   - Matrix Multiply: `c00 = 19 && c01 = 22 && c10 = 43 && c11 = 50`
   - Kadane: `result = expected_int` (int comparison)

The `main.c` driver uses a `CHECK()` macro that prints FAIL and
returns nonzero if any test function returns `false`.

### 6. Files with Pulse code not being extracted or tested?

| Module | Type | Extracted? | ImplTest? | Notes |
|--------|------|-----------|-----------|-------|
| `CLRS.Ch04.MaxSubarray.DivideConquer` | Pure F* spec + proofs | No | No | Specification-level correctness reference for Kadane's. |
| `CLRS.Ch04.Strassen.Spec` | Pure F* spec | No | No | Defines `strassen_multiply` recursively. |
| `CLRS.Ch04.Strassen.Lemmas` | Pure F* proofs | No | No | Proves Strassen == standard multiply. |
| `CLRS.Ch04.Strassen.Complexity` | Pure F* proofs | No | No | Proves O(n^log₂7) bound. |

**Strassen** has no `Impl` or `ImplTest` — it is entirely spec-level.
This is a design choice: Strassen's divide-and-conquer structure with
submatrix operations is substantially harder to implement imperatively.

## Remaining Observations

### Use of F*'s unbounded `int` type in extractable code

All three Impl modules operate on `array int` where `int` is F*'s
mathematical unbounded integer. KaRaMeL extracts this as
`krml_checked_int_t`, which provides runtime overflow checking but is not
a standard C type. For these algorithms (binary search on small arrays,
2×2 matrix multiply, 3-element subarray), this is functionally correct.

### No imperative Strassen implementation

Strassen's algorithm exists only as a pure functional specification with
correctness and complexity proofs. The extraction covers Binary Search,
Matrix Multiply (naïve O(n³)), and Kadane's Maximum Subarray.
