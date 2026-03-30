# EXTRACTION REVIEW REPORT — Chapter 9: Order Statistics

## Summary Checklist

### 1. All C code generated via krml from verified F*/Pulse code?

**YES** (with one acceptable exception). All algorithm implementations and test
functions are generated from verified F*/Pulse code via KaRaMeL extraction.

The only handwritten C files are:

- **`main.c`** (~65 lines): A thin test driver that calls the extracted
  bool-returning test functions. It performs no algorithmic logic — just calls
  each extracted test and reports pass/fail. The actual result checks are in
  the extracted ImplTest code.

- **`krmlinit_override.c`** (37 lines): Initialization of the
  `Pulse_Lib_BoundedIntegers` typeclass function-pointer struct. This is a
  necessary workaround for a known KaRaMeL limitation with typeclass extraction.

### 2. Makefiles are canonical and reuse autoclrs.test.mk with no hacks?

**YES.** The Makefile correctly includes `autoclrs.test.mk` and uses `-bundle`
(not `-drop`) to hide spec and library modules. Standard warning flags are used
with no extra suppressions.

### 3. No handwritten code (handwritten code voids verification guarantees)?

**ACCEPTABLE.** The `main.c` driver is ~65 lines of trivial dispatching code.
It calls extracted bool-returning test functions and reports results. The actual
correctness checks are inside the extracted C code, backed by F* proofs.
The `krmlinit_override.c` is a known necessary workaround.

### 4. C code generated for ImplTest files and their dependencies, not other files?

**YES.** EXTRACTED_C includes both Impl and ImplTest `.c` files. All are compiled
and linked into the test binary.

### 5. Extracted ImplTest C files contain concrete execution with result checks?

**YES.** Each extracted ImplTest function:
- Allocates arrays and populates them with test values
- Calls the Impl functions
- **Captures the return value**
- **Performs concrete equality checks** using `Prims_op_LessThan`
- **Returns a bool** indicating pass/fail

Example from extracted `CLRS_Ch09_MinMax_ImplTest.c`:
```c
bool CLRS_Ch09_MinMax_ImplTest_test_find_minimum(void) {
  krml_checked_int_t *v = KRML_HOST_CALLOC((size_t)3U, sizeof (krml_checked_int_t));
  krml_checked_int_t *arr = v;
  arr[0U] = (krml_checked_int_t)5;
  arr[1U] = (krml_checked_int_t)2;
  arr[2U] = (krml_checked_int_t)8;
  krml_checked_int_t min_val = CLRS_Ch09_MinMax_Impl_find_minimum(arr, (size_t)3U);
  bool ok = !(Prims_op_LessThan(min_val, 2) || Prims_op_LessThan(2, min_val));
  KRML_HOST_FREE(v);
  return ok;
}
```

### 6. Pulse code files that are not being extracted or tested?

The following are proof-only and correctly excluded from extraction:
- Complexity files (Lemma return types, no C code)
- Lemmas files (proof-only helpers)
- Spec files (hidden via `-bundle`, except SimultaneousMinMax.Spec which
  defines the extractable `minmax_result` struct type)

No Pulse implementation code is missing from extraction.

---

## Remaining Notes

### `krmlinit_override.c` (known workaround)

The `BoundedIntegers` typeclass requires a handwritten C file to initialize
function pointers. This is a known KaRaMeL limitation. If BoundedIntegers
support improves in KaRaMeL, this file can be removed. The struct fields
must match the extracted `Pulse_Lib_BoundedIntegers.h`.

### `Pulse_Lib_BoundedIntegers` extracted per-chapter

This library module is extracted as a chapter-level `.c` file. Ideally it
would be shared infrastructure, but this is acceptable for now.
