# Segments Spec Validation Test (CLRS §33.1)

## What Is Tested

`CLRS.Ch33.Segments.ImplTest.fst` tests all four functions in `CLRS.Ch33.Segments.Impl.fsti`:

| Function | Test Inputs | Expected Output | Proven? |
|----------|-------------|-----------------|---------|
| `cross_product` | (0,0),(1,0),(0,1) — CCW | 1 | ✅ |
| `cross_product` | (0,0),(0,1),(1,0) — CW | −1 | ✅ |
| `cross_product` | (0,0),(1,1),(2,2) — Collinear | 0 | ✅ |
| `direction` | (0,0),(1,0),(0,1) | 1 | ✅ |
| `on_segment` | (0,0)-(2,2), point (1,1) inside | true | ✅ |
| `on_segment` | (0,0)-(2,2), point (3,3) outside | false | ✅ |
| `on_segment` | (0,0)-(2,2), endpoint (0,0) | true | ✅ |
| `on_segment` | (0,0)-(2,2), endpoint (2,2) | true | ✅ |
| `segments_intersect` | (0,0)-(2,2) × (0,2)-(2,0) crossing | true | ✅ |
| `segments_intersect` | (0,0)-(1,1) and (2,2)-(3,3) separated | false | ✅ |

## What Is Proven

### Precondition Satisfiability
All four functions require only `emp` (no heap resources). Every test call
succeeds, proving the precondition is trivially satisfiable for any integer inputs.

### Postcondition Precision
Each postcondition has the form `result == spec(concrete_args)`. Since each
spec function evaluates to a unique value on concrete integer inputs, the
postcondition uniquely determines the output. The test explicitly asserts:
- `result == expected_value` (proves the unique output)
- `result <> other_value` (rules out alternatives, for selected cases)

### Coverage
- **Cross product**: all three orientation cases (CCW, CW, Collinear)
- **Direction**: confirms alias behavior (same as cross product)
- **On-segment**: interior, exterior, and both endpoints
- **Segments-intersect**: general crossing (straddle case) and non-crossing
  (collinear separated case)

## Spec Weaknesses Found

**None.** All postconditions are fully precise for the tested inputs:
- Each `result == spec(args)` postcondition evaluates to a unique concrete value
- No admits or assumes were needed
- The spec functions are non-recursive, so evaluation is immediate

The postconditions are as strong as possible: total functional equivalence
(`result == spec(args)`) leaves no room for imprecision.

## Concrete Execution (C Extraction)

All four test functions were extracted to C via KaRaMeL (`krml`) and executed
successfully:

```
--- Segments (§33.1) ---
  test_cross_product             PASS
  test_direction                 PASS
  test_on_segment                PASS
  test_segments_intersect        PASS
```

**Pipeline**: F* → krml → C (gcc) → native executable.
All functions use `krml_checked_int_t` (checked machine integers) for F* `int`.
No memory allocation required (all functions are pure arithmetic).
Run with `make test_c` from the ch33-comp-geometry directory.

## Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver settings**: default (no `#push-options` needed)
- **Verification time**: < 5 seconds
