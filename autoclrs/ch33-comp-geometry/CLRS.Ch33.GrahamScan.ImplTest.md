# Graham Scan Spec Validation Test (CLRS §33.3)

## What Is Tested

`CLRS.Ch33.GrahamScan.ImplTest.fst` tests three of four functions in
`CLRS.Ch33.GrahamScan.Impl.fsti`:

| Function | Test Instance | Expected Output | Proven? |
|----------|---------------|-----------------|---------|
| `find_bottom` | Triangle (0,0),(2,0),(1,2) | 0 (min y, tiebreak min x) | ✅ |
| `polar_cmp` | Pivot=0, a=1, b=2 | 4 (point 1 before point 2 in CCW order) | ✅ |
| `pop_while` | 4 points, hull=[0,1,2], new point=3 | 2 (pops one non-left-turn) | ✅ |

`graham_scan_step` is not tested separately because it composes `pop_while`
(tested above) with a simple array write, and its postcondition references
`scan_step_sz_spec` which directly invokes `pop_while_spec`.

## Test Instances

### find_bottom and polar_cmp: Triangle
Points: (0,0), (2,0), (1,2) — xs=[0,2,1], ys=[0,0,2]
- **find_bottom**: Points 0 and 1 both have y=0 (minimum). Tiebreaker: x=0 < x=2,
  so point 0 wins. Expected: 0.
- **polar_cmp**: Pivot at point 0 (0,0). Comparing point 1 (2,0) vs point 2 (1,2).
  cross_prod(0,0, 2,0, 1,2) = (2−0)·(2−0) − (1−0)·(0−0) = 4. Expected: 4 (positive
  means point 1 has smaller polar angle).

### pop_while: 4-Point Non-Convex Set
Points: (0,0), (2,0), (1,1), (0,2) — xs=[0,2,1,0], ys=[0,0,1,2]
Hull stack: [0, 1, 2] with top=3. New point: index 3 (0,2).

Step-by-step evaluation:
1. top=3: check cross_prod(point 1, point 2, point 3) = cross_prod(2,0, 1,1, 0,2) = 0.
   cp ≤ 0 → pop. top becomes 2.
2. top=2: check cross_prod(point 0, point 1, point 3) = cross_prod(0,0, 2,0, 0,2) = 4.
   cp > 0 → stop. Return top=2.

## What Is Proven

### Precondition Satisfiability
Each test allocates concrete arrays satisfying all preconditions:
- Array lengths match and are positive
- Indices are within bounds
- For `pop_while`: hull stack has ≥ 2 entries, all hull indices < len

### Postcondition Precision
Each postcondition asserts `result == spec(ghost_arrays, args)`. Helper lemmas
evaluate the recursive spec functions on the concrete inputs:
- `find_bottom_triangle_lemma`: proves `find_bottom_spec sxs sys == 0`
- `polar_cmp_triangle_lemma`: proves `polar_cmp_spec sxs sys 0 1 2 == 4`
- `pop_while_concrete_lemma`: proves `pop_while_spec sxs sys shull 3 3 == 2`

Each lemma verifies with `= ()` (trivial proof body), meaning SMT evaluates
the recursive spec fully on the concrete instance.

### Semantic Properties (Strengthened Postconditions)

The following properties are now proven directly from the strengthened
postconditions, without needing to invoke separate lemmas:

| Property | Function | Test Assertion |
|----------|----------|----------------|
| `is_bottommost sxs sys (SZ.v result)` | `find_bottom` | Point 0 is lexicographically minimum (y, then x) among all points |
| `SZ.v result >= 1` | `pop_while` | Stack is never emptied — at least 1 element remains |
| `ensures_left_turn sxs sys shull (SZ.v result) 3` | `pop_while` | When result ≥ 2, the top two hull elements with the new point form a left turn (cp > 0) |

These properties were previously only available via explicit lemma invocation
(`find_bottom_is_bottommost`, `pop_while_spec_ge_1`, `pop_while_ensures_left_turn`).
Now they are part of the Impl.fsti postconditions, making them available to
all clients automatically.

## Spec Weaknesses Found and Addressed

Three weaknesses were identified and fixed:

1. **`find_bottom` lacked geometric meaning.** The postcondition only said
   `result == find_bottom_spec sxs sys` without asserting that the result
   is the bottom-most point. **Fixed:** Added `is_bottommost sxs sys (SZ.v result)`.

2. **`pop_while` lacked stack-size lower bound.** The postcondition said
   `result <= top_in` but not `result >= 1`. Callers (e.g., `graham_scan_step`)
   needed this to index into the hull array. **Fixed:** Added `result >= 1`.

3. **`pop_while` lacked left-turn guarantee.** The key geometric invariant —
   that popping stops at a left turn — was not in the postcondition.
   **Fixed:** Added `ensures_left_turn` predicate (defined in Spec.fst with
   bounds-safe guards for Pulse compatibility).

## Concrete Execution (C Extraction)

All three test functions were extracted to C via KaRaMeL (`krml`) and executed
successfully:

```
--- Graham Scan (§33.3) ---
  test_find_bottom               PASS
  test_polar_cmp                 PASS
  test_pop_while                 PASS
```

**Pipeline**: F* → krml → C (gcc) → native executable.
Array allocation uses `KRML_HOST_CALLOC`/`KRML_HOST_FREE` (from `V.alloc`/`V.free`).
Coordinates use `krml_checked_int_t`; indices use `size_t` (from `SZ.t`).
Run with `make test_c` from the ch33-comp-geometry directory.

## Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver settings**: `--fuel 4 --ifuel 1` for recursive spec evaluation lemmas
- **Verification time**: < 30 seconds
