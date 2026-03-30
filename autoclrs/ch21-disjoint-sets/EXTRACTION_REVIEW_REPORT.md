# Extraction Review Report — Ch21 Disjoint Sets (Union-Find)

## Summary Checklist

| # | Criterion | Pass? | Justification |
|---|-----------|-------|---------------|
| 1 | All C code generated from verified F*/Pulse via KaRaMeL | **Yes** | The extracted `CLRS_Ch21_UnionFind_ImplTest.c` is generated from verified code. `main.c` is a handwritten driver (acceptable pattern). |
| 2 | Makefiles canonical, reuse `autoclrs.test.mk` with no hacks | **Yes** | Uses `autoclrs.test.mk` correctly. `KRML_WARN_FLAGS` uses standard `-warn-error '-2-9-11-15-17'`. Hide-bundle includes `Pulse.*` and `PulseCore.*`. |
| 3 | No handwritten code voiding verification guarantees | **Yes** | `main.c` is a thin driver that calls `CLRS_Ch21_UnionFind_ImplTest_test_union_find()` and checks its return value. All union-find logic lives in verified F*/Pulse code. |
| 4 | C code generated for ImplTest and its dependencies only | **Yes** | `KRML_INPUT_FILES` lists only `ImplTest.krml` and `Impl.krml`. `EXTRACT_C_FILES` targets only `CLRS_Ch21_UnionFind_ImplTest.c`. Spec and Lemmas modules are correctly hidden by the bundle. |
| 5 | Extracted C contains concrete execution with actual result checks | **Yes** | `test_union_find` returns `bool`. Three pass variables (`pass1`, `pass2`, `pass3`) use `sz_eq` comparisons that survive extraction. Ghost proof `ensures pure (r == true)` guarantees the runtime check always passes. `main.c` checks the return value. |
| 6 | All Pulse files are extracted or tested (Impl/ImplTest convention) | **Yes** | Files correctly follow the naming convention: `Impl.fst`/`.fsti` (extracted), `ImplTest.fst` (test), `Spec.fst` (pure, hidden), `Lemmas.fst` (pure, hidden). No Pulse files are orphaned. |

## Issues — All Resolved

### 1. ✅ FIXED — ImplTest now has runtime checks that survive extraction

`test_union_find` returns `bool` with `ensures pure (r == true)`. Three computational
pass variables verify find_set/union results using `sz_eq` (inline_for_extraction).
Extracted C computes and returns `pass1 && pass2 && pass3`. `main.c` checks the return.

### 2. ✅ FIXED — Warning 4 no longer suppressed

`KRML_WARN_FLAGS` changed to `-warn-error '-2-9-11-15-17'` (standard defaults).

### 3. ✅ FIXED — Hide-bundle includes Pulse.* and PulseCore.*

Bundle flags changed to:
```
-bundle 'CLRS.Ch21.UnionFind.ImplTest=CLRS.Ch21.UnionFind.*'
-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,C'
```

### 4. ✅ FIXED — main.c checks return value

`main.c` checks `test_union_find()` return and exits with failure code on mismatch.
