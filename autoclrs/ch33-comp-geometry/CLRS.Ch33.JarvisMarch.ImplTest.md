# Jarvis March Spec Validation Test (CLRS §33.3)

## What Is Tested

`CLRS.Ch33.JarvisMarch.ImplTest.fst` tests three of four functions in
`CLRS.Ch33.JarvisMarch.Impl.fsti`:

| Function | Test Instance | Expected Output | Proven? |
|----------|---------------|-----------------|---------|
| `find_leftmost` | Triangle (0,0),(2,0),(1,2) | 0 (min x-coordinate) | ✅ |
| `find_next` | From vertex 0 of triangle | 1 (most clockwise from origin) | ✅ |
| `jarvis_march` | Triangle (0,0),(2,0),(1,2) | 3 (all points on hull) | ✅ |

`jarvis_march_with_hull` is not tested separately because it shares the same
postcondition as `jarvis_march` (the hull count equals `jarvis_march_spec`)
plus a `valid_jarvis_hull` structural property that is fully determined by
the individual `find_next` results (already tested).

## Test Instance: Triangle

Points: (0,0), (2,0), (1,2) — xs=[0,2,1], ys=[0,0,2]

This is a convex polygon where all 3 points are on the hull, giving the
strongest test of the complete algorithm: the Jarvis march must visit every point.

### Detailed Trace
- **find_leftmost**: Point 0 has x=0 (minimum). Point 2 has x=1, point 1 has x=2.
  Expected: 0.
- **find_next(0)**: Starting at (0,0). Candidate scan:
  - j=0: skip (j=current)
  - j=1: next=current, so set next=1
  - j=2: cross_prod(0,0, 2,0, 1,2) = 4 ≥ 0, don't update. Final: next=1.
- **find_next(1)**: Starting at (2,0). Candidate scan:
  - j=0: next=current=1, set next=0
  - j=1: skip
  - j=2: cross_prod(2,0, 0,0, 1,2) = −4 < 0, update next=2. Final: next=2.
- **find_next(2)**: Starting at (1,2). Candidate scan:
  - j=0: next=current=2, set next=0
  - j=1: cross_prod(1,2, 0,0, 2,0) = 4 ≥ 0, don't update. Final: next=0.
- **jarvis_march**: p0=0, loop: 0→1→2→0 (back to start). Hull count: 1+2 = 3.

## What Is Proven

### Precondition Satisfiability
Each test allocates concrete arrays of length 3 satisfying all preconditions:
- Array lengths match (`SZ.v len == Seq.length sxs == Seq.length sys`)
- `len > 1` for `find_next` and `jarvis_march`
- `current < len` for `find_next`

### Postcondition Precision
Each postcondition asserts `result == spec(ghost_arrays, args)`. Composable
helper lemmas evaluate the recursive spec functions:
- `find_leftmost_triangle_lemma`: proves `find_leftmost_spec sxs sys == 0`
- `find_next_from_0_lemma`: proves `find_next_spec sxs sys 0 == 1`
- `find_next_from_1_lemma`: proves `find_next_spec sxs sys 1 == 2`
- `find_next_from_2_lemma`: proves `find_next_spec sxs sys 2 == 0`
- `jarvis_march_triangle_lemma`: composes the above to prove
  `jarvis_march_spec sxs sys == 3`

The composed lemma demonstrates that the postconditions are precise enough to
determine the exact hull vertex count for a concrete triangle.

## Spec Weaknesses Found

**None.** All postconditions are fully precise for the tested inputs:
- `find_leftmost`: correctly identifies the leftmost point
- `find_next`: correctly selects the most clockwise next vertex
- `jarvis_march`: correctly counts all hull vertices

The postconditions are as strong as possible: each result equals its pure
specification counterpart, which evaluates to a unique value on concrete inputs.

### Note on `find_next_all_left_of` (from Lemmas module)
The `find_next_all_left_of` correctness lemma in `CLRS.Ch33.JarvisMarch.Lemmas`
requires general-position assumptions (no collinear triples, strict upper
half-plane). These assumptions are **not needed** for the functional-equivalence
postcondition tested here — the postcondition `result == find_next_spec` is
unconditional. The geometric correctness assumptions are a separate concern
from spec precision.

## Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver settings**: `--fuel 8 --ifuel 1` for `find_next_aux` unfolding;
  `--z3rlimit 50` for the composed `jarvis_march_triangle_lemma`
- **Verification time**: < 60 seconds
