# Counting Sort — Spec Validation Test (CLRS §8.2)

## Source

Adapted from [Test.CountingSort.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch08-linear-sorting/Test.CountingSort.fst) in `microsoft/intent-formalization`.

## What Is Tested

Two of the three functions in `CLRS.Ch08.CountingSort.Impl.fsti`:

### Test 1: `counting_sort_inplace`

- **Input**: Array `[3; 1; 2]`, `k_val = 4`
- **Expected output**: Array `[1; 2; 3]`
- **Proved**:
  1. **Precondition satisfiability**: The concrete input `[3; 1; 2]` with
     `k_val = 4` satisfies all preconditions (`in_range`, `SZ.fits`, length
     constraints). The function call succeeds.
  2. **Postcondition precision**: Given `S.sorted s ∧ S.permutation s0 s`
     (where `s0 = [3;1;2]`), the output is uniquely determined as
     `[1; 2; 3]`. Proved via element counting: each of `{1,2,3}` appears
     exactly once, and neither `0` nor `4` appear, so sortedness forces
     the unique arrangement.
  3. **Concrete verification**: Each output element is read back and
     asserted equal to the expected value.

### Test 2: `counting_sort_impl` (CLRS-faithful, separate I/O)

- **Input**: Array `a = [3; 1; 2]`, output array `b = [0; 0; 0]`, `k_val = 3`
- **Expected output**: `b = [1; 2; 3]`, `a` unchanged
- **Proved**:
  1. **Precondition satisfiability**: Concrete inputs satisfy all
     preconditions including half-permission sharing (`#0.5R`) for the
     read-only input array.
  2. **Postcondition precision**: Given `S.sorted sb' ∧ S.permutation sb' sa`
     (note: permutation direction is output→input here, opposite from the
     inplace variant), the output is uniquely `[1; 2; 3]`. The completeness
     lemma handles the reversed permutation direction correctly since
     `SeqP.permutation` is symmetric.
  3. **Concrete verification**: Each element of the output array `b` is
     read and verified.
  4. **Resource management**: Demonstrates correct half-permission
     sharing (`A.share`/`A.gather`) for the read-only input array, and
     proper cleanup of both input and output arrays.

### Not Tested: `counting_sort_by_digit`

The third function, `counting_sort_by_digit`, is not tested in this file.
Its postcondition (`Stab.is_stable_sort_on_digit`) involves opaque
digit-level stability properties that would require substantial auxiliary
lemma work to verify in a concrete test. This function is primarily a
subroutine for radix sort and is exercised through the radix sort
implementation.

## Proof Technique

1. **`input_is_sort3`**: Proves `s0 = seq_of_list [3;1;2]` from
   concrete element values using `Seq.lemma_eq_intro`.

2. **`std_sort3_nat`**: Given a sorted permutation of `[3;1;2]`, uses
   `assert_norm` on `SP.count` to establish element multiplicities, then
   Z3 deduces the unique sorted arrangement.

3. **`completeness_inplace` / `completeness_impl`**: Bridges the gap
   between opaque `S.permutation` and `SP.permutation` via
   `reveal_opaque`, and between F* `<=` and `Prims.op_LessThanOrEqual`
   for the `S.sorted` predicate.

## Verdict

- **NO admits. NO assumes.** All proof obligations fully discharged.
- **Preconditions**: Satisfiable for the tested inputs. No issues found.
- **Postconditions**: Fully precise — `sorted ∧ permutation` uniquely
  determines the output for the tested input `[3;1;2]`.
- **Permutation direction**: `counting_sort_impl` uses
  `S.permutation sb' sa` (output→input) while `counting_sort_inplace`
  uses `S.permutation s0 s` (input→output). Both are correct since
  `SeqP.permutation` is symmetric, but this inconsistency is a minor
  API style concern.

## Spec Issues Found

1. **Permutation direction inconsistency** (minor): `counting_sort_impl`
   states `S.permutation sb' sa` while `counting_sort_inplace` states
   `S.permutation s0 s`. This is semantically equivalent but stylistically
   inconsistent. Not a correctness issue.

2. **No issues with precondition strength**: Preconditions are satisfiable
   for reasonable inputs. The `SZ.fits` constraints are non-restrictive
   for practical input sizes.

3. **No issues with postcondition weakness**: `sorted ∧ permutation` is
   the strongest functional specification for sorting. The postcondition
   uniquely determines the output.
