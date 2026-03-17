# Kadane's Maximum Subarray — Spec Validation Test

## Test File

`CLRS.Ch04.MaxSubarray.Kadane.ImplTest.fst`

## What Is Tested

One test function exercises the `max_subarray` API from
`CLRS.Ch04.MaxSubarray.Kadane.fsti` on a small concrete instance:

### Test: `test_kadane_max_subarray`

- **Input**: array `[-1, 3, -2]` (3 elements)
- **Expected result**: `3` (the maximum contiguous subarray sum)
- **Optimal subarray**: `[3]` at index 1

### What Is Proven

1. **Precondition satisfiability**: `len > 0` and length constraints are
   easily satisfied for `len = 3`.

2. **Postcondition precision**: From `result == max_subarray_spec s0`, the
   test proves `result == 3` by:
   - A helper lemma `kadane_test_lemma` connects the ghost sequence `s0`
     (from array writes) to `Seq.seq_of_list [(-1); 3; (-2)]` via
     extensional equality (`Seq.lemma_eq_intro`)
   - `assert_norm` evaluates `max_subarray_spec` on the concrete sequence

### Proof Technique

The key challenge is that the ghost sequence `s0` (a chain of `Seq.upd`
operations) is syntactically different from `Seq.seq_of_list [-1; 3; -2]`.
The helper lemma:

1. Takes `s` with known element values (from the `requires` clause)
2. Creates a concrete `s' = Seq.seq_of_list [...]`
3. Proves `s == s'` via `Seq.lemma_eq_intro` (extensional equality)
4. Uses `assert_norm` to evaluate `max_subarray_spec s'` to `3`

### Kadane Computation Trace

```
max_subarray_spec([-1, 3, -2]) = kadane_spec s 0 0 (-1)

i=0: elem=-1, new_current=max(-1, 0+(-1))=-1,  new_best=max(-1,-1)=-1
i=1: elem=3,  new_current=max(3, -1+3)=3,       new_best=max(-1,3)=3
i=2: elem=-2, new_current=max(-2, 3+(-2))=1,    new_best=max(3,1)=3
i=3: return 3
```

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

**No spec weaknesses found.** The postcondition is both satisfiable and
fully precise.

## Verification Status

- **Zero admits, zero assumes**
- Verified with `--z3rlimit 80 --fuel 8 --ifuel 2`
