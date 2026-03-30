# Ch02 — Extraction Review Report

## Summary Checklist

| # | Criterion | Pass? | Justification |
|---|-----------|-------|---------------|
| 1 | All C code generated via krml from verified F*/Pulse code | **YES** | `InsertionSort.c` and `MergeSort.c` are extracted from krml. `test_main.c` is a minimal 57-line driver that only calls extracted test functions and checks return values — no test logic. |
| 2 | Makefiles are canonical and reuse `autoclrs.test.mk` with no hacks | **YES** | The Makefile includes `autoclrs.test.mk`, uses test.mk pattern rules for `.krml` extraction (no explicit per-module rules), and uses `--extract_module` via test.mk. |
| 3 | No handwritten code | **YES** | `test_main.c` is a minimal driver (printf + if/return). All test inputs, expected outputs, and comparison logic are in verified Pulse ImplTest modules. |
| 4 | C code generated for ImplTest and its dependencies, not other files | **YES** | `KRML_INPUT_FILES` includes both ImplTest and Impl modules. Bundle flags expose ImplTest + Impl as the public API. |
| 5 | Extracted ImplTest C code contains concrete execution with result checks | **YES** | ImplTest functions return `bool`, read array elements after sorting, and compare to expected values at runtime. Ghost assertions prove `r == true`. |
| 6 | All Pulse code files being extracted or tested | **YES** | All 6 ImplTest functions (3 InsertionSort + 3 MergeSort) are extracted to C and called from `test_main.c`. |

## Issues Fixed

| Issue | Status | Description |
|-------|--------|-------------|
| #1 (P0) | **FIXED** | ImplTest functions return `bool` with runtime element comparisons and `ensures pure (r == true)` |
| #2 (P0) | **FIXED** | ImplTest `.krml` files extracted via test.mk pattern rules and included in `KRML_INPUT_FILES` |
| #3 (P0) | **FIXED** | `test_main.c` replaced with 57-line minimal driver calling extracted test functions |
| #4 (P1) | **FIXED** | test.mk pattern rules use `--extract_module`; explicit per-module rules removed |
| #5 (P1) | **FIXED** | `.krml` extraction uses generic `KRML_MODULES` list with `patsubst` |
| #6 (P2) | **VERIFIED** | `fstar_int32.c` IS needed (prims.c references `FStar_Int32_to_string`); kept in `EXTRA_C_SOURCES` |
