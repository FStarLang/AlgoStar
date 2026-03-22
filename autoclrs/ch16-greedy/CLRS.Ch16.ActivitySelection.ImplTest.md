# Activity Selection — Spec Validation Test

## Test Instance

Three activities sorted by finish time:

| Activity | Start | Finish |
|----------|-------|--------|
| 0        | 1     | 4      |
| 1        | 3     | 5      |
| 2        | 5     | 7      |

Expected output: `count = 2`, selected indices = `{0, 2}`.

## What Is Tested

The test calls `activity_selection` from `CLRS.Ch16.ActivitySelection.Impl.fsti`
on the concrete 3-activity instance and proves:

1. **Precondition satisfiability**: The precondition `activity_selection_pre`
   is satisfiable for this instance.
   - `finish_sorted [4; 5; 7]` — proven by `finish3_sorted`
   - `valid_activity` for all 3 activities — proven by `activities3_valid`

2. **Postcondition precision — count**: The postcondition uniquely determines
   `count = 2` via `max_compatible_count start3 finish3 3 == 2`.
   - Proven by showing `[0; 2]` is a compatible set of size 2 (`compatible_0_2`)
   - Proven by showing no compatible set of size 3 exists (`no_compatible_3`)
   - Combined in `max_compatible_is_2` using `reveal_opaque`

3. **Postcondition precision — selection**: The postcondition uniquely
   determines the output indices as `out[0] = 0, out[1] = 2`.
   - From `sel[0] == 0` (greedy always picks first activity)
   - From `pairwise_compatible`: `finish[0] <= start[sel[1]]`, i.e., `4 <= start[sel[1]]`
   - `sel[1] ≠ 1` because `start[1] = 3 < 4 = finish[0]` (incompatible)
   - Therefore `sel[1] = 2` (only remaining valid index)
   - `out_matches_sel` gives `out[i] == sel[i]`

4. **Complexity**: The ghost counter satisfies `cf - c0 == n - 1 = 2`,
   confirming exactly 2 comparisons.

## Proof Techniques

- `assert_norm` for concrete `Seq.seq_of_list` computations
- `reveal_opaque` to unfold `max_compatible_count` (marked `opaque_to_smt`)
- `find_max_compatible_lower_bound` and structural contradiction for upper bound
- Direct Z3 reasoning on the existential `sel` from the postcondition

## Result

**PASS** — All assertions verified. Zero admits, zero assumes.

The postcondition of `activity_selection` is precise enough to:
- Determine the exact count (via optimality guarantee)
- Determine the exact selected activities (via greedy choice + earliest compatible)
- Determine the exact comparison count (via complexity bound)

## Concrete Execution (C Extraction)

**PASS** — Extracted to C via KaRaMeL (`make test-c`), compiled with GCC, and executed successfully.

The extracted C code:
- Allocates arrays for start times `[1, 3, 5]` and finish times `[4, 5, 7]`
- Calls the verified `activity_selection` function
- Returns count=2 with selected indices `{0, 2}`
- Frees all allocated memory and exits cleanly

One implementation change was needed for extraction: the `>=` comparison in
`Impl.fst` was changed from the `Pulse.Lib.BoundedIntegers` typeclass
overload to `Prims.op_GreaterThanOrEqual` to avoid a typeclass dictionary
that KaRaMeL cannot inline for `int` types.

## Specification Quality Assessment

The `Impl.fsti` specification for Activity Selection is **excellent**:
- Precondition is not overly restrictive (handles `n = 0`)
- Postcondition is maximally precise — it uniquely determines the output
  for any concrete input
- The `earliest_compatible` property is key to output uniqueness
- The `max_compatible_count` optimality guarantee closes the count

No specification improvements needed.

## Attribution

Test pattern inspired by
[Test.Quicksort.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
from the intent-formalization repository.
