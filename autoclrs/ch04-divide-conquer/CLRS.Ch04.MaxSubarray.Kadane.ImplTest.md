# Kadane's Maximum Subarray — Spec Validation Test

## Test File

`CLRS.Ch04.MaxSubarray.Kadane.ImplTest.fst`

## What Is Tested

Two test functions exercise the `max_subarray` API from
`CLRS.Ch04.MaxSubarray.Kadane.fsti` on concrete instances:

### Test 1: `test_kadane_max_subarray` — Mixed array

- **Input**: array `[-1, 3, -2]` (3 elements)
- **Expected result**: `3` (the maximum contiguous subarray sum)
- **Optimal subarray**: `[3]` at index 1

### Test 2: `test_kadane_all_negative` — All-negative array

- **Input**: array `[-5, -3, -1]` (3 elements)
- **Expected result**: `-1` (the least-negative element)
- **Optimal subarray**: `[-1]` at index 2
- Tests the edge case where no positive contiguous sum exists.

### What Is Proven

1. **Precondition satisfiability**: `len > 0` and length constraints are
   easily satisfied for `len = 3`.

2. **Postcondition precision**: From `result == max_subarray_spec s0`, the
   tests prove exact results:
   - Test 1: `result == 3` via `kadane_test_lemma`
   - Test 2: `result == -1` via `kadane_all_negative_lemma`

3. **Complexity exactness**: Both tests assert `cf == 3` (exactly 3
   operations for 3 elements). This is now possible because
   `complexity_bounded_linear` was moved from an abstract `val` in
   `Kadane.fsti` to a transparent `let` in `CLRS.Ch04.MaxSubarray.Spec.fst`.

### Proof Technique

The key challenge is that the ghost sequence `s0` (a chain of `Seq.upd`
operations) is syntactically different from `Seq.seq_of_list [...]`.
Each helper lemma:

1. Takes `s` with known element values (from the `requires` clause)
2. Creates a concrete `s' = Seq.seq_of_list [...]`
3. Proves `s == s'` via `Seq.lemma_eq_intro` (extensional equality)
4. Uses `assert_norm` to evaluate `max_subarray_spec s'`

### Kadane Computation Traces

Test 1: `max_subarray_spec([-1, 3, -2])`
```
i=0: elem=-1, new_current=max(-1, 0+(-1))=-1,  new_best=max(-1,-1)=-1
i=1: elem=3,  new_current=max(3, -1+3)=3,       new_best=max(-1,3)=3
i=2: elem=-2, new_current=max(-2, 3+(-2))=1,    new_best=max(3,1)=3
→ return 3
```

Test 2: `max_subarray_spec([-5, -3, -1])`
```
i=0: elem=-5, new_current=max(-5, 0+(-5))=-5,  new_best=max(-5,-5)=-5
i=1: elem=-3, new_current=max(-3, -5+(-3))=-3,  new_best=max(-5,-3)=-3
i=2: elem=-1, new_current=max(-1, -3+(-1))=-1,  new_best=max(-3,-1)=-1
→ return -1
```

## Spec Strengthening Summary

### Change: `complexity_bounded_linear` made transparent

**Before**: Declared as `val complexity_bounded_linear (cf c0 n: nat) : prop`
in `Kadane.fsti`, with the definition hidden in `Kadane.fst`. Clients could
not unfold the predicate to verify complexity properties.

**After**: Definition moved to `CLRS.Ch04.MaxSubarray.Spec.fst`:
```fstar
let complexity_bounded_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n
```
This is consistent with how `complexity_bounded_log` (BinarySearch) and
`complexity_bounded_cubic` (MatrixMultiply) are defined in their respective
`Spec.fst` files.

**Impact**: Tests can now assert `cf == 3` (exact operation count), which
was previously impossible through the abstract interface.

## Spec Completeness Assessment

The `max_subarray` postcondition `result == max_subarray_spec s0` is
**fully precise**: it is a *functional* specification that uniquely
determines the output integer for any input array.

Combined with the optimality theorems in `CLRS.Ch04.MaxSubarray.Lemmas`
(`theorem_kadane_optimal` and `theorem_kadane_witness`), the spec provides
a complete correctness guarantee:

- The result equals `max_subarray_spec s0` (functional equivalence)
- `max_subarray_spec s0 >= sum_range s i j` for all `[i,j)` (optimality)
- There exist `i,j` such that `max_subarray_spec s0 == sum_range s i j`
  (witness)

**No remaining spec weaknesses.** The postcondition is both satisfiable,
fully precise, and the complexity bound is now transparent and verifiable.

## Verification Status

- **Zero admits, zero assumes**
- Verified with `--z3rlimit 10 --fuel 8 --ifuel 2`

## Runtime Assurance

Each test function returns `bool` with two layers of assurance:

1. **PROOF** (ghost, erased at extraction): Ghost assertions prove the
   postcondition uniquely determines the result. `ensures pure (r == true)`
   proves the runtime check always succeeds.
2. **RUNTIME** (computational, survives extraction to C): `result = expected`
   comparisons produce a `bool` checked by the C test driver (`main.c`).

## Concrete Execution Status

Successfully extracted to C and executed. The `Pulse.Lib.BoundedIntegers`
dependency was removed from `Kadane.fst` (operators on `SZ.t` use `+^` from
`FStar.SizeT`; operators on `int` come from `Prims`).

### Extraction pipeline

1. **F* → KaRaMeL IR**: `fstar --codegen krml --extract_module`
2. **KaRaMeL IR → C**: `krml -bundle ... -add-include '"krml/internal/compat.h"'`
3. **C → executable**: linked with `libkrmllib.a` (provides `Prims_op_*` for
   checked integer arithmetic)

### Test output

```
Kadane Max Subarray - mixed array... PASS
Kadane Max Subarray - all negative... PASS
```

### Build

```
make extract   # Extract to C
make test      # Extract, compile, link, and run
```
