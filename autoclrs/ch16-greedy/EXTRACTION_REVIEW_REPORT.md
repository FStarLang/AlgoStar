# Chapter 16 — Extraction Review Report

## Summary

Ch16 extracts two ImplTest modules (Activity Selection and Huffman) to C via
KaRaMeL, compiles them with a hand-written `main.c` driver, and runs the test
binary. The pipeline builds and runs to completion, but there are several issues
with the extracted tests and Makefile structure.

---

## Checklist: Extraction Requirements

### 1. All C code generated via krml from verified F\*/Pulse code

**Partially — NO**

The following hand-written C files are included in the build:

| File | Purpose | Issue |
|------|---------|-------|
| `main.c` | Test driver calling extracted test functions | Acceptable (standard driver pattern) |
| `prims_stubs.c` / `prims_stubs.h` | Stubs for `Prims_op_*` and `FStar_SizeT_v` | **Problematic — voids verification guarantees** |

The `prims_stubs.c` file provides hand-written implementations for:
- `Prims_op_GreaterThanOrEqual`, `Prims_op_LessThanOrEqual`, `Prims_op_GreaterThan`,
  `Prims_op_LessThan`, `Prims_op_Addition`, `Prims_op_Subtraction`, `Prims_op_Multiply`
- `FStar_SizeT_v`

These stubs manually implement checked integer operations as plain C integer
ops (using `krml_checked_int_t`, which is typically `int64_t`), bypassing the
KaRaMeL-standard `krmllib/dist/generic/prims.c` implementation. The stubs
are technically correct for the types used, but are hand-written C that
replaces what should come from the verified toolchain.

**Verdict: NO** — `prims_stubs.c` is handwritten code that replaces standard
library functions. Ch23-mst uses the canonical `$(KRML_HOME)/krmllib/dist/generic/prims.c`
instead.

### 2. Makefiles are canonical, reusing autoclrs.test.mk with no hacks

**Partially — NO**

The Makefile does include `autoclrs.test.mk` (line 68), but contains several
non-canonical elements:

1. **Custom krmllib `.krml` extraction rules (lines 39–56)**: The Makefile
   defines custom rules to extract `FStar_Pervasives_Native.krml`,
   `FStar_Order.krml`, and `FStar_Seq_Base.krml` from the ulib. While these
   may be needed, ch23-mst does not require them — this suggests the ch16
   code may be using polymorphic stdlib types in extraction-reachable paths
   (e.g., `Seq.seq_of_list`, `FStar.Order` types) that should ideally be
   avoided or handled differently.

2. **`out.krml` dependency (line 57)**: `KRML_EXTRA_INPUTS` includes
   `$(OUTPUT_DIR)/out.krml`. This is the file produced when Pulse's test.mk
   `.krml` pattern rule extracts multiple modules in a single pass (using
   `--extract` instead of `--extract_module`). Its presence indicates some
   module extraction produces a multi-module `out.krml` rather than
   individual per-module `.krml` files. This is fragile and non-canonical.

3. **Warning suppression (line 28)**: `-warn-error -2-9-11-15-17-18` suppresses
   warnings 11 (Non-Low\* expression) and 15 (Non-Low\* function), which
   indicate that unbounded types or spec functions are leaking into extraction.
   Warning 18 (bundle collision) is also suppressed. Ch23-mst uses the same
   warning suppression, so this may be a systemic issue, but warnings 11 and
   15 are concerning and should be investigated.

4. **`KRML_MODULES` uses underscore names (lines 10–21)**: The module list
   uses `CLRS_Ch16_ActivitySelection_ImplTest` (underscores) rather than the
   conventional dot notation used in `KRML_INPUT_FILES` in ch23-mst. This is
   cosmetic but inconsistent.

**Verdict: NO** — The krmllib extraction rules, `out.krml` hack, and prims stubs
are non-canonical.

### 3. No handwritten code

**NO**

- `prims_stubs.c` / `prims_stubs.h`: Hand-written integer operation stubs
- `main.c`: Hand-written test driver (acceptable pattern, also used in ch23-mst)

The prims stubs void verification guarantees because they replace verified
library code with unverified C implementations.

**Verdict: NO** — `prims_stubs.c` must be replaced with the standard
`krmllib/dist/generic/prims.c`.

### 4. C code generated for ImplTest files and dependencies only

**YES**

The `KRML_MODULES` list (lines 10–21) correctly lists the two ImplTest modules
and their dependencies. The bundle flags (lines 25–27) correctly bundle each
ImplTest with its implementation modules. The hide-bundle `FStar.*,Pulse.*,...`
correctly suppresses standard library output.

However, note that:
- `CLRS.Ch16.Huffman.Codec.ImplTest` is **NOT** included (see point 6 below)
- `TestHuffman.fst` is **NOT** included (this is a simpler test that just drops the tree)

**Verdict: YES** for the modules that are included, but incomplete coverage.

### 5. Extracted C code contains concrete runtime checks

**NO — Critical deficiency**

Comparing with ch23-mst's exemplary pattern:

**Ch23-mst pattern (good)**:
- ImplTest functions return `bool` indicating pass/fail
- Tests contain `sz_eq` comparisons that survive extraction to C
- `main.c` checks the return value and prints PASS/FAIL
- Additional direct-API runtime rechecks in `main.c`

**Ch16 pattern (deficient)**:
- **Activity Selection ImplTest**: `test_activity_selection_3` returns `unit`.
  All assertions (`assert (pure (SZ.v count == 2))`, etc.) are **ghost** —
  they are erased at extraction. The extracted C function
  `CLRS_Ch16_ActivitySelection_ImplTest_test_activity_selection_3` simply
  allocates arrays, calls the algorithm, and frees memory. It does **no
  runtime checking**. The `KRML_MAYBE_UNUSED_VAR(count)` in the extracted C
  confirms the count is never inspected at runtime.

- **Huffman ImplTest**: `test_huffman_2` also returns `unit`. The extracted C
  function allocates frequencies, calls `huffman_tree`, and frees memory.
  The tree pointer is discarded (`KRML_MAYBE_UNUSED_VAR(tree_ptr)`). No
  runtime checks at all. The `drop_` on `is_htree` means the tree is leaked
  in the C code.

- **`main.c` unconditionally prints "PASSED"**: The driver calls the test
  functions and prints "PASSED" regardless of any result, since the functions
  return void.

**Verdict: NO** — The tests have zero runtime checks. The ghost assertions are
erased at extraction, and the main.c unconditionally prints "PASSED". This is
fundamentally different from ch23-mst where tests return `bool` and the driver
checks it.

### 6. All Pulse code with Impl is extracted and tested

**NO — `CLRS.Ch16.Huffman.Codec.Impl` and `CLRS.Ch16.Huffman.Codec.ImplTest` are not extracted**

The chapter contains three Impl modules:

| Module | Extracted? | Has ImplTest? | ImplTest Extracted? |
|--------|-----------|---------------|-------------------|
| `CLRS.Ch16.ActivitySelection.Impl` | Yes | Yes | Yes |
| `CLRS.Ch16.Huffman.Impl` | Yes | Yes | Yes |
| `CLRS.Ch16.Huffman.Codec.Impl` | **No** | Yes (`Codec.ImplTest`) | **No** |

`CLRS.Ch16.Huffman.Codec.Impl` provides verified encode/decode operations
on Huffman trees. It has a corresponding `CLRS.Ch16.Huffman.Codec.ImplTest`
with `test_decode` and `test_encode` functions. Neither is included in the
Makefile's extraction targets.

Additionally, `TestHuffman.fst` exists but is not part of the ImplTest
convention and is not extracted.

**Verdict: NO** — The Codec Impl/ImplTest pair is completely missing from
extraction.

---

## Fixes Required

### Fix 1: Replace `prims_stubs.c` with standard krmllib prims ✅ DONE

Replaced `prims_stubs.c`/`prims_stubs.h` with `$(KRML_HOME)/krmllib/dist/generic/prims.c`
plus `fstar_support.c` (provides `FStar_Int32_to_string` and `FStar_SizeT_v`).
Removed `-add-include '"prims_stubs.h"'`, added `-add-include '"fstar_support.h"'`.

### Fix 2: Add runtime checks to ImplTest functions ✅ DONE

All three ImplTest functions now return `bool` with `ensures pure (r == true)`:
- **ActivitySelection.ImplTest**: `sz_eq` comparisons check `count==2, sel=[0,2]`
- **Huffman.ImplTest**: Checks input array preserved (`f0==3 && f1==5`)
- **Huffman.Codec.ImplTest**: Checks decode output `[0,1]` and encode output `[true,false]`
  (verified but not extracted — see Fix 3)

`main.c` checks return values and fails on `false` (ch23-mst pattern).

### Fix 3: Add `CLRS.Ch16.Huffman.Codec.ImplTest` to extraction ⚠️ BLOCKED

The Codec ImplTest functions (`test_decode`, `test_encode`) are fully verified with
machine-checked proofs and have runtime checks returning `bool`. However, they **cannot
be extracted to C** because `decode_impl`, `encode_impl`, and `free_htree` take
`HSpec.htree` as a non-erased parameter (used in `match ft { ... }` for runtime tree
traversal). Since `HSpec.htree` is not C-representable, KaRaMeL drops these functions.

The fix requires restructuring `Codec.Impl` to derive the tree structure from the
`hnode` struct (checking `left == None` vs `Some`) instead of matching on the spec tree.
This is a significant refactor beyond the scope of extraction review fixes.

### Fix 4: Eliminate `out.krml` dependency ✅ DONE

Removed `$(OUTPUT_DIR)/out.krml` from `KRML_EXTRA_INPUTS`. The `out.krml` was a tiny
23-byte artifact (empty module file) produced as a side effect of multi-module extraction.
All needed modules are now explicitly listed in `KRML_MODULES`.

### Fix 5: Eliminate custom krmllib extraction rules — DEFERRED

The custom rules for `FStar_Pervasives_Native.krml`, `FStar_Order.krml`, and
`FStar_Seq_Base.krml` remain. These are needed because the Huffman PQ comparator uses
`FStar.Order` at extraction. Eliminating them requires restructuring the PQ to avoid
`FStar.Order` in extraction-reachable paths.

### Fix 6: Fix memory leak in Huffman ImplTest ⚠️ BLOCKED

`test_huffman_2` still uses `drop_ (is_htree tree_ptr ft)`. Calling `free_htree tree_ptr ft`
is not possible because `ft` is existentially bound (ghost/erased) from the `huffman_tree`
postcondition, and `free_htree` matches on `ft` at runtime.

The Codec ImplTest (`test_decode`, `test_encode`) DOES use `free_htree` properly because
`test_tree` is a concrete module-level constant.

Fixing the Huffman ImplTest leak requires the same `is_htree` restructuring noted in Fix 3.

### Fix 7: Investigate warnings 11 and 15 ✅ DONE

Marked `start3`, `finish3`, `freq_seq2` as `noextract` so spec-only values no longer
leak into extracted C. Warnings 11/15 are still suppressed in `KRML_WARN_FLAGS` (same
as ch23-mst) because the Huffman PQ code uses `FStar.Order` in extraction-reachable paths.
