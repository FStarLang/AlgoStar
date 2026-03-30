# EXTRACTION REVIEW REPORT — Chapter 9: Order Statistics

## Summary Checklist

### 1. All C code generated via krml from verified F*/Pulse code?

**NO.** There are two handwritten C files that are **not** generated from verified code:

- **`test_main.c`** (141 lines): A hand-written C test driver that directly calls
  extracted Impl functions with hardcoded test data and hardcoded expected values.
  This voids verification guarantees because the expected values (e.g., `result == 2`)
  are asserted in C without any connection to the F* proofs.

- **`krmlinit_override.c`** (37 lines): Hand-written initialization of the
  `Pulse_Lib_BoundedIntegers` typeclass function-pointer struct. This replaces
  the auto-generated `krmlinit.c` which sets function pointers to NULL. This file
  is a necessary workaround for a known KaRaMeL limitation with typeclass extraction
  and is acceptable — but it is still handwritten C.

### 2. Makefiles are canonical and reuse autoclrs.test.mk with no hacks?

**MOSTLY YES**, with caveats:

- The Makefile correctly includes `autoclrs.test.mk` and sets the standard variables.
- Uses `-drop` instead of `-bundle` to hide Spec modules. This works but is
  non-canonical: the `-drop` flag is a legacy KaRaMeL feature. The canonical
  approach (used by ch23-mst) is `-bundle 'FStar.*,Pulse.*,...'` to group
  library/spec modules into a no-API bundle. The ch09 Makefile uses `-drop` to
  individually name each Spec module, which is fragile (must be updated if Spec
  modules are added/renamed).
- Suppresses warning `-10` (deprecated feature) in addition to the standard set.
  The default in `autoclrs.test.mk` is `-warn-error -2-9-11-15-17`. Ch09 adds `-10`.
  This should be investigated — what deprecated feature is being used?

### 3. No handwritten code (handwritten code voids verification guarantees)?

**NO — MAJOR ISSUE.** The `test_main.c` file is 141 lines of handwritten C that:

- Constructs test arrays manually (`make_test_array()`)
- Calls extracted Impl functions directly
- Checks results against hardcoded expected values (`result == 2`, `result == 8`)
- Provides its own `main()` function

This completely bypasses the verified ImplTest modules. The F* ImplTest files
contain proof-carrying tests where the postconditions guarantee correctness
(`assert (pure (min_val == 2))`), but these assertions are **erased** during
extraction. The extracted ImplTest C code calls the functions but **discards the
return values** — it performs no runtime checks at all.

The handwritten `test_main.c` reimplements these checks in C, but without any
formal connection to the F* specifications. The expected values could be wrong,
the function signatures could mismatch, and the handwritten code could have bugs —
none of this is caught by F* verification.

### 4. C code generated for ImplTest files and their dependencies, not other files?

**PARTIALLY.** The KRML_MODULES list includes both Impl and ImplTest modules, plus
`Pulse_Lib_BoundedIntegers` and `CLRS_Ch09_SimultaneousMinMax_Spec`. However:

- The ImplTest `.krml` files are extracted by KaRaMeL and `.c` files are generated.
- BUT the ImplTest `.c` files are **not listed in `EXTRACTED_C`** and are therefore
  **not compiled or linked** into the test binary.
- The test binary only compiles `test_main.c` + the Impl `.c` files.
- So the extracted ImplTest code is generated but **unused**.

### 5. Extracted ImplTest C files contain concrete execution with result checks?

**NO — CRITICAL ISSUE.** The extracted ImplTest C files contain test functions that:

- Allocate arrays and populate them with test values (correct)
- Call the Impl functions (correct)
- **Discard the return value** — no variable captures the result (WRONG)
- **Perform no checks** — no `if` statements, no `printf`, no assertions (WRONG)

Example from `_output/CLRS_Ch09_MinMax_ImplTest.c`:
```c
void CLRS_Ch09_MinMax_ImplTest_test_find_minimum(void) {
  krml_checked_int_t *v = KRML_HOST_CALLOC((size_t)3U, sizeof (krml_checked_int_t));
  krml_checked_int_t *arr = v;
  arr[0U] = (krml_checked_int_t)5;
  arr[1U] = (krml_checked_int_t)2;
  arr[2U] = (krml_checked_int_t)8;
  CLRS_Ch09_MinMax_Impl_find_minimum(arr, (size_t)3U);  // return discarded!
  KRML_HOST_FREE(v);
}
```

The F* source has `let min_val = find_minimum arr 3sz ctr #(hide 0)` followed by
`assert (pure (min_val == 2))`, but the assertion is erased during extraction (it's
a `pure` ghost assertion) and the binding is optimized away since the value is only
used in the erased assertion.

### 6. Pulse code files that are not being extracted or tested?

**YES.** The following Pulse/F* files have no extraction or test coverage:

- **Complexity files** (4 modules): `CLRS.Ch09.MinMax.Complexity`,
  `CLRS.Ch09.PartialSelectionSort.Complexity` (+ `.Enhanced`, `.Test`),
  `CLRS.Ch09.Quickselect.Complexity`, `CLRS.Ch09.SimultaneousMinMax.Complexity`.
  These are proof-only (Lemma return types) and correctly excluded from extraction.

- **Lemmas files** (4 modules): Similarly proof-only and correctly excluded.

- **Spec files**: `MinMax.Spec`, `PartialSelectionSort.Spec`, `Quickselect.Spec`
  are correctly dropped via `-drop`. `SimultaneousMinMax.Spec` is intentionally
  extracted because it defines the `minmax_result` struct type used in the Impl
  return type — this is correct.

No Pulse implementation code is missing from extraction. The issue is not missing
files but rather that the extracted tests are non-functional.

---

## Issues To Fix

### Issue 1 (CRITICAL): Extracted ImplTest C code performs no runtime checks

**Problem:** The F* ImplTest modules use `assert (pure (...))` to verify results.
These assertions are ghost/pure and are erased during extraction. The extracted C
test functions call the algorithms but discard return values and check nothing.

**How to fix:** The ImplTest F* modules need to be restructured to produce
**concrete runtime checks** that survive extraction. Two approaches:

**Approach A (preferred):** Add a concrete `bool`-returning check to each test function.
Instead of:
```fstar
let result = find_minimum arr 3sz ctr #(hide 0);
assert (pure (result == 2));
```
Use:
```fstar
let result = find_minimum arr 3sz ctr #(hide 0);
assert (pure (result == 2));  // ghost: erased
let ok = (result = 2);        // concrete: survives extraction
if not ok then ...;            // or return ok from the function
```
The test function should return `bool` indicating pass/fail, and `main()` (also
in Pulse/F*) should call all tests and return a nonzero exit code on failure.

**Approach B:** Write a single F* `main` function (in a new `Main.fst` module)
that calls the ImplTest functions and is itself extracted. The `test_main.c` would
then be trivial — just `int main() { return Module_main(); }` — or eliminated
entirely if F* `main` is the entry point.

Either way, **`test_main.c` should be eliminated** as handwritten code.

### Issue 2 (MODERATE): Uses `-drop` instead of `-bundle` for Spec hiding

**Problem:** The Makefile uses:
```
-drop 'CLRS.Ch09.PartialSelectionSort.Spec,CLRS.Ch09.Quickselect.Spec,CLRS.Ch09.MinMax.Spec,CLRS.Common.Complexity'
```
This individually names modules to drop. If any Spec module is added or renamed,
this list must be manually updated.

**How to fix:** Replace `-drop` with a canonical `-bundle` that groups all
non-extractable modules:
```
-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,CLRS.Ch09.MinMax.Spec,CLRS.Ch09.PartialSelectionSort.Spec,CLRS.Ch09.Quickselect.Spec,CLRS.Common.Complexity'
```
Or, if feasible, restructure so Spec modules that don't define extractable types
are simply not included in `KRML_MODULES`, and library modules are hidden via:
```
-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
```

### Issue 3 (MODERATE): Handwritten `krmlinit_override.c`

**Problem:** The `BoundedIntegers` typeclass requires a handwritten C file to
initialize function pointers. This is a known KaRaMeL limitation and is
currently necessary, but it is fragile and chapter-specific.

**How to fix (long-term):** If the `BoundedIntegers` typeclass is used across
multiple chapters, factor the `krmlinit_override.c` into `../common/` so it's
shared. Alternatively, if the Pulse/KaRaMeL toolchain adds typeclass extraction
support, this file can be removed.

**Short-term:** Document this as a known workaround. Ensure the struct fields
match the extracted `Pulse_Lib_BoundedIntegers.h` — any change to the typeclass
definition will silently break this file.

### Issue 4 (MINOR): Warning `-10` suppressed without justification

**Problem:** The Makefile suppresses KaRaMeL warning 10 (deprecated feature)
beyond the standard set. It's unclear what deprecated feature is being used.

**How to fix:** Run extraction without `-10` to identify the warning source.
If the deprecated feature is unavoidable, add a comment in the Makefile
explaining why. If avoidable, update the code.

### Issue 5 (MINOR): `EXTRACTED_C` does not include ImplTest `.c` files

**Problem:** KaRaMeL generates `CLRS_Ch09_*_ImplTest.c` files, but they are not
listed in `EXTRACTED_C` and are not compiled into the test binary. This means
the extracted test code is dead code.

**How to fix:** Once Issue 1 is resolved (ImplTest functions perform real checks),
add the ImplTest `.c` files to `EXTRACTED_C` and call the extracted test functions
from a minimal main (or an extracted F* main). Remove `test_main.c`.

### Issue 6 (MINOR): `Pulse_Lib_BoundedIntegers` extracted as a chapter-level module

**Problem:** `Pulse_Lib_BoundedIntegers` is extracted per-chapter as a `.krml`
and `.c` file. This is a library module, not chapter code.

**How to fix:** Ideally this would be handled by the shared infrastructure.
For now, it's acceptable but should be noted as duplication across chapters.
