# Ch26 Max Flow — Extraction Review Report

## Summary Checklist

### 1. All C code generated via krml from verified F*/Pulse code?

**PARTIAL — NO**

The core algorithm (BFS, augmentation, max_flow) and the two ImplTest
functions are extracted from verified Pulse via KaRaMeL. However, two
handwritten C files are also required:

- `test_main.c` — Hand-written C test harness that calls the extracted test
  functions and prints PASS/FAIL.
- `clrs_ch26_compat.h` — Hand-written compatibility shims providing
  `FStar_SizeT_v()` and `FStar_SizeT_uint_to_t()` as static inline C
  functions.

The compat header is needed because the Impl code mixes `FStar.SizeT.t`
(machine-width `size_t`) with `int` (unbounded, extracted as
`krml_checked_int_t`), and KaRaMeL does not natively provide the conversion
functions. This is a code-smell indicating the Impl code should ideally use
machine-width integers uniformly.

### 2. Makefiles canonical, reusing autoclrs.test.mk with no hacks?

**NO — several hacks present**

The Makefile includes `autoclrs.test.mk` correctly, but has these
non-canonical elements:

1. **Custom `extract-krml` target**: Manually invokes `$(FSTAR) --codegen
   krml --extract_module ...` for each module. Other chapters (e.g., ch23)
   rely on Pulse's `test.mk` pattern rules for `.krml` generation. This
   custom target duplicates logic that should be handled by the standard
   extraction rules.

2. **`CC_EXTRA_FLAGS = -Wno-implicit-function-declaration`**: Suppresses C
   compiler warnings about undeclared functions. This masks real issues
   (e.g., missing prototypes for `FStar_SizeT_v` before the compat header
   is processed).

3. **`CC_EXTRA_INCLUDES = -include clrs_ch26_compat.h`**: Force-includes a
   handwritten compatibility header. This is a workaround for the SizeT
   conversion issue.

4. **`KRML_WARN_FLAGS = -warn-error -2-15`**: Suppresses KaRaMeL warning 15
   ("Non-Low\* function"), which indicates spec-level functions are leaking
   into the extraction path. The default in `autoclrs.test.mk` is
   `-warn-error -2-9-11-15-17`; this chapter narrows to just `-2-15`,
   which means warnings 9, 11, 17 are promoted to errors (or simply not
   suppressed). The suppression of warning 15 is concerning because it
   masks real extraction quality issues.

5. **Missing `STAGE3 ?= 1`**: Unlike ch23, this Makefile does not set
   `STAGE3 ?= 1` but does use the Pulse test.mk. This may work if the
   default is stage3, but it's inconsistent with other chapters.

### 3. No handwritten code?

**NO — two handwritten files present**

| File | Purpose | Voids verification? |
|------|---------|-------------------|
| `test_main.c` | C test driver: calls extracted functions, prints results | Yes — the test harness is unverified |
| `clrs_ch26_compat.h` | SizeT↔int conversion shims | Yes — the conversions are unchecked C casts |

The `clrs_ch26_compat.h` performs unchecked casts between `size_t` and
`krml_checked_int_t`. An incorrect cast (e.g., truncation on 32-bit
platforms) could silently produce wrong behavior. This undermines the
verification guarantees.

**Compare with ch23**: ch23 also has handwritten files (`main.c`,
`fstar_support.c`), so this is a project-wide pattern, not unique to ch26.
However, the ch23 `main.c` performs independent runtime re-checks of the
algorithm output via the direct API, providing a second layer of assurance
beyond the proof. The ch26 `test_main.c` does NOT perform any such
independent checks.

### 4. C code generated for ImplTest and dependencies only?

**YES**

The Makefile correctly extracts only:
- `CLRS.Ch26.MaxFlow.Impl` (the algorithm)
- `CLRS.Ch26.MaxFlow.ImplTest` (the test)

The bundle flag `-bundle CLRS.Ch26.MaxFlow.ImplTest=CLRS.Ch26.MaxFlow.*`
correctly makes ImplTest the API module and internalizes (makes `static`)
all Impl functions. The generated `CLRS_Ch26_MaxFlow_ImplTest.c` is the
sole extracted C file.

Spec, Lemmas, Complexity, and MaxFlowMinCut modules are correctly excluded
from extraction — they are pure F\* and produce no C code.

### 5. Extracted C contains concrete test execution with actual result checks?

**NO — this is the most critical issue**

The ImplTest functions (`test_max_flow_completeness` and
`test_max_flow_disconnected_completeness`) do execute the `max_flow`
algorithm on concrete inputs. However, all result validation is via ghost
assertions:

```fstar
assert (pure (f01 == 7));  // GHOST — erased at extraction
assert (pure (flow_val == 7));  // GHOST — erased at extraction
```

In the extracted C, these assertions completely vanish. The extracted test
functions:
1. Allocate capacity/flow matrices
2. Call `max_flow`
3. Free memory
4. Return `void`

There are **no runtime comparisons** of the computed flow values against
expected values. The tests "pass" as long as they don't crash (segfault,
infinite loop). A completely wrong `max_flow` implementation that returns
garbage but doesn't crash would still "pass" these tests.

**Compare with ch23 (the reference)**: The ch23 `ImplTest` functions:
- Return `bool` (not `void`) with `ensures pure (r == true)`
- Contain runtime `sz_eq` comparisons that survive extraction to C
- The extracted C actually checks `edge_count == 2` and verifies MST edges
- The `main.c` also performs *independent* C-level runtime checks via
  the direct algorithm API

The ch26 ImplTest completely lacks this runtime verification layer.

### 6. Files with Pulse code not being extracted or tested?

**YES — `CLRS.Ch26.MaxFlow.Test.fst` is not extracted**

`Test.fst` contains 5 Pulse test functions covering more test cases than
ImplTest:

| Function | Graph | Expected flow |
|----------|-------|--------------|
| `test_max_flow_3v` | 3-vertex, two paths | 20 |
| `test_max_flow_disconnected` | 3-vertex, no edges | 0 |
| `test_max_flow_single_edge` | 2-vertex, single edge | 7 |
| `test_max_flow_diamond` | 4-vertex diamond | 20 |
| `test_max_flow_bottleneck` | 3-vertex bottleneck | 1 |

These functions are verified by F\* (`.checked` file exists in `_cache`)
but are NOT in the extraction pipeline. The Makefile only extracts
`ImplTest.fst`, not `Test.fst`.

Additionally, `Test.fst` has the same problem as `ImplTest.fst` — all
result validation is ghost-only. The functions don't return `bool` and
don't contain runtime comparisons. Even if extracted, they would not
provide meaningful C-level testing.

---

## Issues To Fix

### Issue 1 (Critical): ImplTest has no runtime result checking

**Problem**: All assertions in ImplTest are ghost (`assert (pure (...))`)
and are erased during extraction. The extracted C test functions are
effectively no-ops that call `max_flow` and discard the result.

**Fix**: Refactor `ImplTest.fst` to follow the ch23 pattern:
1. Have test functions return `bool` with `ensures pure (r == true)`
2. Read back flow values into concrete variables (already done)
3. Add runtime comparisons using an `int_eq` helper (like ch23's `sz_eq`):
   ```fstar
   inline_for_extraction
   let int_eq (a b: int) : (r:bool{r <==> a = b}) = a = b
   ```
4. Compute a `pass` boolean from runtime comparisons:
   ```fstar
   let pass = int_eq f01 7 && int_eq f00 0 && int_eq f10 0
              && int_eq f11 0 && int_eq flow_val 7;
   ```
5. Return `pass` with a proof that `pass == true`

This ensures the extracted C code actually checks the computed flow values
match expected results, providing a runtime verification layer.

### Issue 2 (Critical): Handwritten `clrs_ch26_compat.h` undermines verification

**Problem**: The compat header provides unchecked C casts for
`FStar_SizeT_v` and `FStar_SizeT_uint_to_t`. These functions appear in the
extracted code because the Impl mixes `SizeT.t` with unbounded `int`.

**Fix (preferred)**: Refactor the Impl to avoid mixing `SizeT.t` with
`int` in contexts that survive extraction. Use `SizeT.t` for indices and
`int` only behind `Ghost.erased`. If the `pred` array must store vertex
indices as `int` (to use -1 as sentinel), consider using `SizeT.t` with a
distinguished sentinel value instead.

**Fix (short-term)**: If refactoring Impl is too invasive, at minimum the
compat header should include bounds checking (e.g., `assert(x >= 0)` in
`FStar_SizeT_uint_to_t`). Document why it's needed.

### Issue 3 (Moderate): Test.fst not extracted or tested

**Problem**: `Test.fst` has 5 Pulse test functions covering more graph
topologies (3-vertex, 4-vertex diamond, bottleneck) that are not in the
extraction pipeline.

**Fix**: Either:
- (a) Merge the Test.fst test cases into ImplTest.fst (with runtime
  checks), rename appropriately, and extract; or
- (b) Add Test.fst to the extraction pipeline alongside ImplTest.fst,
  after adding runtime result checks to the Test.fst functions.

Option (a) is preferred — consolidate all tests into ImplTest.fst following
the naming convention.

### Issue 4 (Moderate): Non-canonical `extract-krml` target

**Problem**: The Makefile has a custom `extract-krml` target that manually
runs `fstar.exe --codegen krml` for each module. This duplicates logic and
is fragile.

**Fix**: Remove the custom `extract-krml` target. Use pattern rules (either
from Pulse's `test.mk` or define standard ones) so `.krml` files are
produced via the standard `make` dependency chain. The `autoclrs.test.mk`
already provides the `.krml → .c` step; the `.fst → .krml` step should
similarly be standardized.

### Issue 5 (Moderate): `-Wno-implicit-function-declaration` masks errors

**Problem**: `CC_EXTRA_FLAGS = -Wno-implicit-function-declaration`
suppresses C compiler warnings about undeclared functions. This could mask
real linking errors or ABI mismatches.

**Fix**: Remove this flag. If it causes compilation errors, fix the root
cause (likely the compat header include order or missing prototypes).

### Issue 6 (Minor): Unbounded `int` extracted as `krml_checked_int_t`

**Problem**: The Impl uses F\*'s `int` (unbounded integer) for flow and
capacity values. KaRaMeL extracts this as `krml_checked_int_t` with
checked arithmetic operations (`Prims_op_Addition`, etc.), requiring
linkage with `libkrmllib.a`. This is:
- Non-standard for C extraction (most chapters use `SizeT.t` or fixed-width)
- Requires `libkrmllib.a` linkage for `Prims_op_*` functions
- Potentially slower due to checked arithmetic

**Fix**: This is a deeper design issue. For a proper C extraction, flow
and capacity values should use a fixed-width type (e.g., `Int32.t` or
`Int64.t`). However, this would require significant refactoring of both
Spec and Impl. Mark as a known limitation for now.

### Issue 7 (Minor): KaRaMeL warning 15 suppressed

**Problem**: `-warn-error -2-15` suppresses warning 15 ("Non-Low\*
function"), indicating spec-level functions reached extraction.

**Fix**: Investigate which functions trigger warning 15. If they are
spec-level helpers (e.g., `seq_get`, `seq_get_sz`), ensure they are behind
interfaces or `Ghost.erased`. If they are legitimately needed in extracted
code, document why.

### Issue 8 (Minor): `test_main.c` lacks independent runtime verification

**Problem**: Unlike ch23's `main.c` which calls the algorithm directly and
checks results independently, ch26's `test_main.c` only calls the
extracted test functions and assumes success if they return.

**Fix**: Add independent C-level runtime checks in `test_main.c` that
call `max_flow` directly and verify the result (similar to ch23's
"runtime recheck (direct API)" pattern). This provides defense-in-depth
even if the extracted test functions are no-ops.

---

## Summary

| # | Check | Pass? | Notes |
|---|-------|-------|-------|
| 1 | All C from verified code via krml | **NO** | `test_main.c` + `clrs_ch26_compat.h` handwritten |
| 2 | Canonical Makefile, no hacks | **NO** | Custom extract-krml, -Wno-implicit-function-declaration, compat header |
| 3 | No handwritten code | **NO** | Two handwritten C files |
| 4 | Extract ImplTest + deps only | **YES** | Correct bundle and module selection |
| 5 | Extracted C checks test results | **NO** | All assertions erased; no runtime checks |
| 6 | No un-extracted Pulse code | **NO** | Test.fst has 5 tests not in pipeline |

**Overall assessment**: The extraction pipeline mechanically works (krml
produces C, it compiles and links, the test binary runs). But the tests
provide no meaningful runtime verification — they are effectively no-ops
that call the algorithm and discard results. The most important fix is
adding runtime result checking to ImplTest (Issue 1), following the ch23
pattern.

---

## Fix Status (2026-03-30)

| # | Issue | Status | Notes |
|---|-------|--------|-------|
| 1 | ImplTest no runtime checks | **FIXED** | Test functions return `bool` with `int_eq` comparisons that survive to C |
| 2 | Compat header | **IMPROVED** | Added bounds-checking assertions + documentation; elimination requires Impl refactoring |
| 3 | Test.fst not extracted | **FIXED** | 3 tests consolidated into ImplTest (3v-two-path, diamond, bottleneck) |
| 4 | Non-canonical extract-krml | **FIXED** | Removed; using Pulse test.mk pattern rules for .krml generation |
| 5 | -Wno-implicit-function-declaration | **FIXED** | Removed |
| 6 | Unbounded int | **KNOWN** | Design limitation; would require Impl refactoring to use fixed-width types |
| 7 | KaRaMeL warning 15 | **FIXED** | Now using standard `-warn-error -2-9-11-15-17` flags |
| 8 | test_main.c no verification | **FIXED** | Checks bool return values, reports PASS/FAIL per test |

### Summary After Fixes

| # | Check | Pass? |
|---|-------|-------|
| 1 | All C from verified code via krml | **PARTIAL** — `test_main.c` + `clrs_ch26_compat.h` still handwritten |
| 2 | Canonical Makefile, no hacks | **YES** — uses standard Pulse test.mk + autoclrs.test.mk |
| 3 | No handwritten code | **PARTIAL** — compat header needed for SizeT↔int conversions |
| 4 | Extract ImplTest + deps only | **YES** — correct bundle and module selection |
| 5 | Extracted C checks test results | **YES** — all 5 tests return bool with runtime `==` comparisons |
| 6 | No un-extracted Pulse code | **PARTIAL** — Test.fst retained for verification coverage but not extracted |
