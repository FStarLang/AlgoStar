# Ch33 Computational Geometry — Extraction Review Report

## Summary Checklist

### 1. All C code generated via KaRaMeL from verified F*/Pulse code?

**Yes.** All C implementation code is generated from verified Pulse code via
the F*→.krml→C pipeline. The `prims_shim.c` has been replaced with KaRaMeL's
canonical `krmllib/dist/generic/prims.c`, linked with `-ffunction-sections
-fdata-sections -Wl,--gc-sections` to eliminate unused symbols.

### 2. Makefiles canonical and reuse autoclrs.test.mk with no hacks?

**Yes.** The Makefile sets the standard variables (`CHAPTER_ID`, `KRML_INPUT_FILES`,
`KRML_BUNDLE_FLAGS`, `EXTRACT_C_FILES`, etc.) and includes `../autoclrs.test.mk`
with no pattern-rule overrides or hacks.

### 3. No handwritten code?

**Yes.** The handwritten `prims_shim.c` has been removed. The Makefile now
references KaRaMeL's canonical `prims.c` from `$(KRML_HOME)/krmllib/dist/generic/`.

### 4. C code generated for ImplTest files and their dependencies only?

**Yes.** The Makefile's `EXTRACT_KRML_MODULES` lists exactly:
- `CLRS_Ch33_Segments_Impl`
- `CLRS_Ch33_Segments_ImplTest`
- `CLRS_Ch33_GrahamScan_Impl`
- `CLRS_Ch33_GrahamScan_ImplTest`
- `CLRS_Ch33_JarvisMarch_Impl`
- `CLRS_Ch33_JarvisMarch_ImplTest`

Spec, Lemmas, Complexity, and top-level monolith modules are correctly excluded
from extraction. The `-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'` hides
standard library internals.

### 5. Extracted C code contains concrete test execution with result checking?

**Yes.** All ImplTest functions return `bool` (true = all checks passed). The
extracted C code performs concrete computations and returns boolean results that
are checked by `main.c`:

```c
if (!CLRS_Ch33_Segments_ImplTest_test_cross_product()) {
    printf("FAIL\n"); failed++;
}
```

Each test function:
1. Calls the Impl function with concrete inputs
2. Has ghost `assert (pure (...))` for proof-level verification (erased in C)
3. Returns a concrete boolean checking the results at runtime

### 6. Pulse code files not being extracted or tested?

**All Impl functions are now tested:**

| Function | Module | Tested? |
|----------|--------|---------|
| `cross_product` | Segments.Impl | ✅ |
| `direction` | Segments.Impl | ✅ |
| `on_segment` | Segments.Impl | ✅ |
| `segments_intersect` | Segments.Impl | ✅ |
| `find_bottom` | GrahamScan.Impl | ✅ |
| `polar_cmp` | GrahamScan.Impl | ✅ |
| `pop_while` | GrahamScan.Impl | ✅ |
| `graham_scan_step` | GrahamScan.Impl | ✅ |
| `find_leftmost` | JarvisMarch.Impl | ✅ |
| `find_next` | JarvisMarch.Impl | ✅ |
| `jarvis_march` | JarvisMarch.Impl | ✅ |
| `jarvis_march_with_hull` | JarvisMarch.Impl | ✅ |

---

## Resolved Issues

### Issue 1: Use of unbounded `int` in extractable code (Deferred)

The Impl code uses F*'s `int` (unbounded integer) for coordinates, which
KaRaMeL maps to `krml_checked_int_t` (int32_t with overflow checking). This
is functional via KaRaMeL's compat layer but not idiomatic Low* style.
Refactoring to machine-width integers is a significant effort deferred for now.

### Issue 2: Handwritten `prims_shim.c` → canonical KaRaMeL prims.c ✅

**Fixed.** Replaced `EXTRA_C_SOURCES = prims_shim.c` with
`$(KRML_HOME)/krmllib/dist/generic/prims.c`. Added `-ffunction-sections
-fdata-sections -Wl,--gc-sections` to eliminate unreferenced symbols
(`Prims_string_of_int` etc.) that depend on `FStar_Int32_to_string`.

### Issue 3: No C-level result checking in tests ✅

**Fixed.** All ImplTest functions now return `bool` instead of `unit`. Each
test computes results, verifies them with ghost assertions, and returns a
concrete boolean. `main.c` checks the return value and reports PASS/FAIL with
a nonzero exit code on failure.

### Issue 4: Missing tests for `graham_scan_step` and `jarvis_march_with_hull` ✅

**Fixed.** Added:
- `test_graham_scan_step`: Tests the scan step on a 4-point set, verifies
  the returned top index and hull contents after popping and pushing.
- `test_jarvis_march_with_hull`: Tests the full algorithm on a triangle,
  verifies hull size (3) and hull indices ([0, 1, 2]).

### Issue 5: `triangle_pre` leaks into C header as `void *` ✅

**Fixed.** Added `CLRS.Ch33.JarvisMarch.ImplTest.fsti` that only exposes the
test functions. The `triangle_pre` predicate is hidden behind the interface
and no longer appears in the extracted C header.

---

## Summary

| # | Check | Status |
|---|-------|--------|
| 1 | All C from verified code | ✅ canonical prims.c from KaRaMeL |
| 2 | Canonical Makefile | ✅ Uses autoclrs.test.mk cleanly |
| 3 | No handwritten code | ✅ prims_shim.c removed |
| 4 | Extract ImplTest + deps only | ✅ Correct modules extracted |
| 5 | C tests check results | ✅ All tests return bool, main.c checks |
| 6 | All Pulse code tested | ✅ All 12 functions tested |
