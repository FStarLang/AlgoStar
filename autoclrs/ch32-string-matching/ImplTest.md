# Ch32 String Matching — Concrete Execution Results

All three ImplTest modules extract to C via KaRaMeL, compile, and run
successfully.

## Test output

```
=== Ch32 String Matching — Concrete Execution Tests ===

[1/3] Naive String Match (CLRS §32.1) ... PASS
[2/3] KMP String Match   (CLRS §32.4) ... PASS
[3/3] Rabin-Karp          (CLRS §32.2) ... PASS

All 3 tests passed.
```

## Build pipeline

| Step | Command | Status |
|------|---------|--------|
| F* verify | `make` | ✅ All modules check |
| Extract .krml | `make extract` | ✅ 6 modules → Ch32_StringMatch.c |
| Compile + link | `make test-c` | ✅ No warnings |
| Run tests | `_extract/ch32_test` | ✅ 3/3 pass |

## Notes

- **Prims_op_Star shim**: F* nightly (2026.03.24+) extracts `*` as
  `Prims.op_Star`, but the bundled krmllib still defines
  `Prims_op_Multiply`. The `ch32_shims.h` header maps the new name to the
  old one via `#define`.
- No admits, no assumes in any verified code.
- No changes to Impl.fsti or ImplTest.fst specifications.
