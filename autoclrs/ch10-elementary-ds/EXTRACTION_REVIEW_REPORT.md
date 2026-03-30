# Ch10 Elementary Data Structures — Extraction Review Report

## Summary Checklist

### 1. All C code generated using krml from verified F*/Pulse code?

**YES (with caveats).** The four extracted `.c` files (`CLRS_Ch10_Stack_ImplTest.c`,
`CLRS_Ch10_Queue_ImplTest.c`, `CLRS_Ch10_SinglyLinkedList_ImplTest.c`,
`CLRS_Ch10_DLL_ImplTest.c`) are produced by KaRaMeL from `.krml` files that F*
generates from verified Pulse modules. The Impl modules all use `#lang-pulse` and are
verified by fstar.exe. However, the suppression of KaRaMeL warning 4 (type error)
means that the extracted C may contain type-level issues that KaRaMeL flagged but were
silenced (see item 6 below).

### 2. Makefiles canonical and reuse extraction rules from autoclrs.test.mk with no hacks?

**NO.** The Makefile includes `autoclrs.test.mk` but adds several non-canonical hacks:

- **Custom shell loop for .krml extraction** (the `extract-krml:` target) instead of
  using standard Make pattern rules. This loop:
  - Passes `.fst.checked` files to fstar.exe instead of source `.fst` files.
  - Swallows all stderr (`> /dev/null 2>&1`), hiding extraction warnings.
  - Uses `if [ ! -f ... ]` caching that can become stale.
- **Three pattern rule overrides** at the bottom to prevent `test.mk`'s generic rules
  from conflicting with the custom loop.
- **`STAGE3 ?= 1` / `export STAGE3`** — not present in the ch23 reference Makefile.
- **`EXTRACT_DIR = $(OUTPUT_DIR)/csrc`** — uses a non-standard subdirectory; ch23 uses
  `_output/c`.

Compare with ch23-mst, which uses a clean, declarative Makefile: it lists
`KRML_INPUT_FILES` explicitly, uses two no-op pattern rules to cancel Pulse's generic
rules, and then includes `autoclrs.test.mk` — no shell loops.

### 3. No handwritten code?

**PARTIALLY.** `main.c` is the only handwritten C file, which is expected (it's the
test driver). However, `main.c` unconditionally prints "PASS" after each test function
call — it does not inspect any return values or perform any runtime checks. This means
the handwritten driver adds zero verification value beyond "the function didn't crash."

There is no handwritten C code that voids verification guarantees (e.g., no
`fstar_support.c` or custom implementations).

### 4. C code generated for ImplTest files and their dependencies, not other files?

**YES.** `EXTRACT_MODULES` lists exactly:
- `CLRS.Ch10.Stack.Impl`, `CLRS.Ch10.Stack.ImplTest`
- `CLRS.Ch10.Queue.Impl`, `CLRS.Ch10.Queue.ImplTest`
- `CLRS.Ch10.SinglyLinkedList.Base`, `CLRS.Ch10.SinglyLinkedList.Impl`,
  `CLRS.Ch10.SinglyLinkedList.ImplTest`
- `CLRS.Ch10.DLL.Impl`, `CLRS.Ch10.DLL.ImplTest`
- Plus `FStar.Pervasives.Native` for the option type.

Spec, Lemmas, and Test modules are correctly excluded.

### 5. Extracted C code contains concrete execution with actual result checks?

**NO — CRITICAL ISSUE.** This is the most significant problem with the extraction.

The F* ImplTest files contain `assert (pure (...))` statements that verify correctness
at **proof time** (ghost assertions, erased at extraction). In the extracted C code:

- **All results are discarded** via `KRML_MAYBE_UNUSED_VAR(result)`.
- **No runtime comparisons** exist — no `if (x != expected) abort()` or similar.
- **`main.c` unconditionally prints "PASS"** — it doesn't check return values.

For example, the Stack ImplTest in F* says:
```fstar
let x3 = pop s;
assert (pure (x3 == 3));  // Ghost — erased at extraction
```

The extracted C becomes:
```c
krml_checked_int_t x3 = pop__krml_checked_int_t(s);
KRML_MAYBE_UNUSED_VAR(x3);  // Result thrown away!
```

**Contrast with ch23-mst**, which does this correctly:
- `test_prim_3` **returns `bool`** based on `sz_eq` comparisons (computational,
  survives extraction).
- `main.c` **checks the return value**: `if (!test_prim_3()) { return 1; }`.
- `main.c` also performs **independent runtime rechecks** by calling the algorithm
  directly from C and using `CHECK(keys[0] == 0, ...)` macros.

The ch10 tests prove correctness at proof time (good!) but provide zero runtime
evidence that the extracted C code actually produces the expected values.

### 6. Pulse code files not being extracted or tested?

**YES — there are files with Pulse code that are not extracted:**

The four `.Test.fst` files contain Pulse test code that is **not** extracted to C:
- `CLRS.Ch10.Stack.Test.fst`
- `CLRS.Ch10.Queue.Test.fst`
- `CLRS.Ch10.SinglyLinkedList.Test.fst`
- `CLRS.Ch10.DLL.Test.fst`

These are spec-level tests (they verify properties in Pulse but are not in
`EXTRACT_MODULES`). The corresponding `ImplTest.fst` files are the intended extraction
targets, so this is by design. However, the `Test.fst` files are effectively redundant
with the `ImplTest.fst` files — they test the same operations with the same
assertions but are less thorough (e.g., `DLL.Test.fst` doesn't test `list_insert_tail`,
`list_search_back`, `list_search_ptr`, `list_delete_last`, or `list_delete_node`).

---

## Issues to Fix

### Issue 1 (CRITICAL): ImplTest functions lack runtime result checks

**Problem:** All four ImplTest test functions return `unit` and rely solely on ghost
`assert (pure (...))` for correctness. These assertions are erased at extraction,
leaving the C code with no runtime checks.

**Fix:** Following the ch23 pattern:

1. Make each test function **return `bool`** instead of `unit`.
2. Add **computational comparisons** (e.g., an `inline_for_extraction` equality check)
   that survive extraction to C.
3. Combine all comparisons into a single `bool` result that the function returns.
4. Update `main.c` to **check the return value** and `return 1` on failure.

Example pattern (from ch23):
```fstar
inline_for_extraction
let int_eq (a b: int) : (r:bool{r <==> a = b}) = a = b

fn test_stack_spec_validation ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // ... operations ...
  let x3 = pop s;
  assert (pure (x3 == 3));
  let pass = int_eq x3 3;
  // ... accumulate checks ...
  pass
}
```

### Issue 2 (HIGH): KaRaMeL warning 4 (type error) suppressed

**Problem:** `KRML_WARN_FLAGS = -warn-error -2-3-4-9-11-15-17` suppresses warning 4
("type error"), which is KaRaMeL's way of reporting that the generated C has incorrect
types. This should never be suppressed without thorough investigation.

**Fix:** Remove `-4` from the warning flags. If warning 4 fires, fix the underlying
type issue in the F* code (likely caused by unbounded `int` leaking into extractable
positions). The standard set used by ch23 is `-warn-error -2-9-11-15-17`.

### Issue 3 (HIGH): Warning 3 also suppressed

**Problem:** Warning 3 is also suppressed. Its meaning should be investigated. Only
warnings that are understood and documented should be suppressed.

**Fix:** Remove `-3` from the warning flags and investigate if/why it fires.

### Issue 4 (MEDIUM): Makefile uses non-canonical shell loop for .krml extraction

**Problem:** The `extract-krml` target uses a `for` loop in shell to extract each
module, which:
- Cannot be parallelized by `make -j`
- Swallows stderr, hiding extraction problems
- Uses file-existence caching that can become stale
- Requires pattern rule overrides at the bottom to prevent conflicts

**Fix:** Replace with standard Make pattern rules and explicit `KRML_INPUT_FILES`, as
done in ch23. Example:

```makefile
KRML_INPUT_FILES = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(EXTRACT_MODULES)) FStar_Pervasives_Native)

# Cancel Pulse's generic pattern rules
$(OUTPUT_DIR)/%.krml:
	@true
$(EXTRACT_DIR)/%.c: $(EXTRACT_DIR)/%.krml
	@true
```

The `test.mk` pattern rules from Pulse handle individual `.krml` extraction. If they
don't, add explicit rules per the `autoclrs.test.mk` documentation.

### Issue 5 (MEDIUM): Bundle flags missing catch-all for FStar/Pulse/Prims

**Problem:** The ch10 bundle flags only bundle chapter-specific modules:
```
-bundle "CLRS.Ch10.Stack.ImplTest=CLRS.Ch10.Stack.Impl,CLRS.Ch10.Stack.ImplTest"
```
There is no catch-all `-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'` to hide standard
library modules from C output. ch23 includes this.

**Fix:** Add:
```
-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
```
to `KRML_BUNDLE_FLAGS`. This ensures no stray standard library code appears in the C
output.

### Issue 6 (MEDIUM): Element type is unbounded `int` in Stack/Queue ImplTest

**Problem:** The Stack and Queue are instantiated with F*'s unbounded `int`:
```fstar
let s = create_stack int 0 5sz;
```
This extracts to `krml_checked_int_t` (i.e., `int32_t`), which works but:
- Triggers KaRaMeL warnings 11/15 (non-Low* types), which is why those are suppressed
- Is not idiomatic for extraction-ready code
- Silently truncates values outside the `int32_t` range

The SLL and DLL use `int` as the key type in their node definition, which has the same
issue.

**Fix:** For truly clean extraction, the data structures should either:
1. Be parameterized by a machine-width type (e.g., `Int32.t`) in the ImplTest, or
2. Use a concrete machine-width type for the element/key type.

This is a lower priority since `krml_checked_int_t` works in practice for small test
values.

### Issue 7 (LOW): `main.c` provides no runtime assurance

**Problem:** `main.c` unconditionally prints "PASS" for each test, providing the same
output whether the code computed correct values or random garbage.

**Fix:** After fixing Issue 1 (return `bool`), update `main.c` to check return values:
```c
if (!CLRS_Ch10_Stack_ImplTest_test_stack_spec_validation()) {
    fprintf(stderr, "FAIL: Stack test\n");
    return 1;
}
printf("  [Stack]  PASS\n");
```

### Issue 8 (LOW): Memory leaks in Stack and Queue test functions

**Problem:** The Stack and Queue ImplTest functions allocate heap memory (via `V.alloc`
and `B.alloc` inside `create_stack`/`create_queue`) but never free it. The
postcondition leaves `stack_inv`/`queue_inv` in the separation logic context. The SLL
and DLL tests properly clean up.

**Fix:** Add cleanup code (free the Vec and Box) at the end of each test, or add
`destroy_stack`/`destroy_queue` operations to the Impl interface. Alternatively,
document that these are one-shot test functions where the OS reclaims memory at process
exit.

### Issue 9 (LOW): Redundant `.Test.fst` files

**Problem:** Each data structure has both a `.Test.fst` and an `.ImplTest.fst` file.
The `.Test.fst` files are less thorough and not extracted. They are effectively
superseded by the `.ImplTest.fst` files.

**Fix:** No action required for extraction, but consider removing the `.Test.fst` files
to reduce maintenance burden and avoid confusion about which tests are authoritative.

---

## Summary

| # | Check | Status | Priority |
|---|-------|--------|----------|
| 1 | All C from verified F*/Pulse | ✅ Yes | — |
| 2 | Canonical Makefile | ✅ Fixed — ch23-style, no shell loop | — |
| 3 | No handwritten code | ✅ Yes (main.c is expected) | — |
| 4 | Extract ImplTest + deps only | ✅ Yes | — |
| 5 | Runtime result checks in C | ✅ Fixed — bool returns with int_eq/bool_eq | — |
| 6 | All Pulse code extracted/tested | ⚠️ .Test.fst not extracted (by design) | Low |

## Fix Status

Issues 1, 2, 3, 4, 5, 7 have been addressed:
- ImplTest functions return `bool` with `int_eq`/`bool_eq` computational checks
- Makefile uses canonical pattern (explicit `KRML_INPUT_FILES`, ch23-style cancel rules)
- KaRaMeL warning flags use standard set (`-warn-error -2-9-11-15-17`), no warning 3/4 suppression
- Catch-all `-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'` added
- `main.c` checks return values and returns 1 on failure

Remaining (low priority):
- Issue 6: Element type is unbounded `int` (extracts as `krml_checked_int_t`, works in practice)
- Issue 8: Stack/Queue memory not freed (test functions, OS reclaims at exit; invariant dropped)
- Issue 9: Redundant `.Test.fst` files (no action needed)
