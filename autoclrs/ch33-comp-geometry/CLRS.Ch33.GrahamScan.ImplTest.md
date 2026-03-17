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

## Spec Weaknesses Found

**None.** All postconditions are fully precise for the tested inputs:
- `find_bottom`: correctly identifies the bottom-most point
- `polar_cmp`: correctly computes the polar angle comparison
- `pop_while`: correctly pops non-left-turn entries and stops at a left turn

The postconditions are as strong as possible: each result equals its pure
specification counterpart, which evaluates to a unique value.

## Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver settings**: `--fuel 4 --ifuel 1` for recursive spec evaluation lemmas
- **Verification time**: < 30 seconds
