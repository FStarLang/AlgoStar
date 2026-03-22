# Jarvis March Spec Validation Test (CLRS §33.3)

## What Is Tested

`CLRS.Ch33.JarvisMarch.ImplTest.fst` tests three of four functions in
`CLRS.Ch33.JarvisMarch.Impl.fsti`:

| Function | Test Instance | Expected Output | Proven? |
|----------|---------------|-----------------|---------|
| `find_leftmost` | Triangle (0,0),(2,0),(1,2) | 0 (min x-coordinate) | ✅ |
| `find_next` | From vertex 0 of triangle | 1 (most clockwise from origin) | ✅ |
| `find_next` | From vertex 1 of triangle | 2 (most clockwise from (2,0)) | ✅ |
| `find_next` | From vertex 2 of triangle | 0 (most clockwise from (1,2)) | ✅ |
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

### Semantic Properties (Strengthened Postconditions)

The following properties are now proven directly from the strengthened
postconditions, without needing to invoke separate lemmas:

| Property | Function | Test Assertion |
|----------|----------|----------------|
| `is_leftmost sxs sys (SZ.v result)` | `find_leftmost` | Point 0 is lexicographically leftmost (min x, tiebreak min y) |
| `SZ.v result <> SZ.v current` | `find_next` | Result always advances to a different point (guarantees progress) |

The `find_next` progress property is tested from all three vertices:
- From 0: result is 1 ≠ 0 ✅
- From 1: result is 2 ≠ 1 ✅
- From 2: result is 0 ≠ 2 ✅

This confirms the full cycle 0→1→2→0 and that the strengthened postcondition
correctly reflects the progress guarantee at every step.

## Spec Weaknesses Found and Addressed

Two weaknesses were identified and fixed:

1. **`find_leftmost` lacked geometric meaning.** The postcondition only said
   `result == find_leftmost_spec sxs sys` without asserting that the result
   is the leftmost point. **Fixed:** Added `is_leftmost sxs sys (SZ.v result)`.

2. **`find_next` lacked progress guarantee.** The postcondition did not assert
   `result <> current`, which is critical for Jarvis march termination. Without
   this, a caller could not prove the loop always advances. The lemma
   `find_next_spec_not_current` proved this, but it wasn't exposed in the spec.
   **Fixed:** Added `SZ.v result <> SZ.v current` to the postcondition.

### Note on `find_next_all_left_of` (from Lemmas module)
The `find_next_all_left_of` correctness lemma in `CLRS.Ch33.JarvisMarch.Lemmas`
requires general-position assumptions (no collinear triples, strict upper
half-plane). These assumptions are **not needed** for the functional-equivalence
postcondition tested here — the postcondition `result == find_next_spec` is
unconditional. The geometric correctness assumptions are a separate concern
from spec precision.

## Concrete Execution (C Extraction)

All three test functions were extracted to C via KaRaMeL (`krml`) and executed
successfully:

```
--- Jarvis March (§33.3) ---
  test_find_leftmost             PASS
  test_find_next                 PASS
  test_jarvis_march              PASS
```

**Pipeline**: F* → krml → C (gcc) → native executable.
Array allocation uses `KRML_HOST_CALLOC`/`KRML_HOST_FREE` (from `V.alloc`/`V.free`).
Coordinates use `krml_checked_int_t`; indices use `size_t` (from `SZ.t`).
`find_next` tested from all three vertices (0→1→2→0 full cycle) in a single
function call — all three invocations execute correctly in the same C function.
Run with `make test_c` from the ch33-comp-geometry directory.

## Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver settings**: `--fuel 8 --ifuel 1` for `find_next_aux` unfolding;
  `--z3rlimit 50` for the composed `jarvis_march_triangle_lemma`
- **Verification time**: < 60 seconds
