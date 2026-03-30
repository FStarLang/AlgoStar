# Extraction Review Report — Chapter 35 (Approximation: Vertex Cover)

## Checklist Summary

### 1. All C code is generated via KaRaMeL from verified F*/Pulse code

**YES** ✅

The extracted C in `_output/c_extract/VertexCoverTest.c` is produced by the
KaRaMeL pipeline (`fstar.exe --codegen krml` → `krml`). The `.krml` files
(`CLRS_Ch35_VertexCover_Impl.krml`, `CLRS_Ch35_VertexCover_ImplTest.krml`)
are present in `_output/`. The extracted C contains the algorithm
(`approx_vertex_cover`) and the test wrapper (`test_vertex_cover_triangle`),
both generated from verified Pulse source.

### 2. Makefiles are canonical and reuse autoclrs.test.mk with no hacks

**YES** ✅

The chapter Makefile sets the required variables (`CHAPTER_ID`,
`KRML_INPUT_FILES`, `KRML_BUNDLE_FLAGS`, `EXTRACT_C_FILES`,
`TEST_EXE_NAME`) and does `include ../autoclrs.test.mk`. There are no
pattern-rule overrides, no ad-hoc shell commands, no extra C support files
beyond `main.c`, and no workarounds. Compare with ch23-mst which needs
pattern-rule cancellations (`$(EXTRACT_DIR)/%.krml: @true`) and an
`fstar_support.c` shim — ch35 is cleaner.

### 3. No handwritten code

**YES — main.c is a minimal test driver** ✅

`main.c` is a thin 18-line C driver that calls the verified
`test_vertex_cover_triangle()` function and checks its boolean return
value. It contains no algorithm logic, no direct API calls to
`approx_vertex_cover`, and no hand-written validation. All runtime
checks are in the verified Pulse test function.

### 4. C code is generated for ImplTest and its dependencies only

**YES** ✅

`KRML_INPUT_FILES` lists exactly `CLRS_Ch35_VertexCover_ImplTest.krml` and
`CLRS_Ch35_VertexCover_Impl.krml`. The bundle flags produce a single
`VertexCoverTest.c` containing both the test and the implementation. Spec,
Lemmas, and Complexity modules are not extracted (they are pure/ghost and
are captured by the hide-bundle `FStar.*,Pulse.*,PulseCore.*,Prims`).

### 5. Extracted ImplTest contains concrete test execution with runtime result checks

**YES — test returns bool with runtime cover validation** ✅

The extracted `test_vertex_cover_triangle` function:

```c
bool CLRS_Ch35_VertexCover_ImplTest_test_vertex_cover_triangle(void) {
    // ... setup adjacency matrix, call algorithm ...
    krml_checked_int_t c0 = cover_a[0U];
    krml_checked_int_t c1 = cover_a[1U];
    krml_checked_int_t c2 = cover_a[2U];
    bool ok =
        c0 == 1 && c1 == 1 && c2 == 0 ||
        c0 == 1 && c1 == 0 && c2 == 1 ||
        c0 == 0 && c1 == 1 && c2 == 1;
    // ... cleanup ...
    return ok;
}
```

The function:
- Returns `bool` (not `void`)
- Reads the cover values at runtime (concrete array access)
- Compares results against the 3 valid 2-vertex covers for K₃
- The proof guarantees `r == true` (so the check always passes)
- `main.c` checks the return value and reports PASS/FAIL

This follows the ch23-mst pattern where ImplTest functions return `bool`
with verified computational comparisons that survive extraction.

### 6. Files with Pulse code not being extracted or tested

**All Pulse code is accounted for** ✅

- `Impl.fst` — extracted ✅
- `ImplTest.fst` — extracted ✅
- `Spec.fst` — pure F*, correctly not extracted (spec-only)
- `Lemmas.fst` — pure F*, correctly not extracted (proof-only)
- `Complexity.fst` — pure F*, correctly not extracted (proof-only)

The Impl/ImplTest naming convention is correctly followed.

---

## Issues — Resolved

### Issue 1 (Critical): ImplTest lacked runtime result checks — FIXED ✅

Refactored `test_vertex_cover_triangle` to return `bool` with runtime
array reads and comparisons. The extracted C function reads cover values
and checks against the 3 valid covers. The proof guarantees `r == true`.

### Issue 2 (Minor): main.c duplicated algorithm logic — FIXED ✅

Simplified `main.c` to just call `test_vertex_cover_triangle()` and check
its boolean return. Removed the direct call to `approx_vertex_cover` and
all hand-written validation logic.

### Issue 3 (Minor): main.c used `krml_checked_int_t` directly — FIXED ✅

Resolved by Issue 2: `main.c` no longer calls the algorithm API directly.

### Issue 4 (Informational): Spec/Lemmas/Complexity not in hide-bundle — FIXED ✅

Added spec/proof modules to the hide-bundle in the Makefile:
```
-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,CLRS.Ch35.VertexCover.Spec,CLRS.Ch35.VertexCover.Lemmas,CLRS.Ch35.VertexCover.Complexity'
```

---

## Summary

| # | Check | Status |
|---|-------|--------|
| 1 | C code generated via KaRaMeL | ✅ Yes |
| 2 | Canonical Makefile using autoclrs.test.mk | ✅ Yes |
| 3 | No handwritten code | ✅ main.c is minimal test driver only |
| 4 | Extraction targets ImplTest + deps only | ✅ Yes |
| 5 | ImplTest has runtime result checks | ✅ Yes — returns bool with cover validation |
| 6 | All Pulse code extracted/tested | ✅ Yes |

**Overall**: All extraction review checks pass. The ImplTest function
returns `bool` with verified runtime comparisons, `main.c` is a thin
driver that checks the return value, and the Makefile bundle flags
defensively hide all spec/proof modules.
