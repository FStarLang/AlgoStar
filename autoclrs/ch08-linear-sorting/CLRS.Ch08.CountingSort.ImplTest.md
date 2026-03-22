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
  4. **In-range verification**: The `S.in_range s 4` postcondition is
     verified, confirming all output elements are ≤ `k_val`.

### Test 2: `counting_sort_impl` (CLRS-faithful, separate I/O)

- **Input**: Array `a = [3; 1; 2]`, output array `b = [0; 0; 0]`, `k_val = 3`
- **Expected output**: `b = [1; 2; 3]`, `a` unchanged
- **Proved**:
  1. **Precondition satisfiability**: Concrete inputs satisfy all
     preconditions including half-permission sharing (`#0.5R`) for the
     read-only input array.
  2. **Postcondition precision**: Given `S.sorted sb' ∧ S.permutation sa sb'`
     (permutation direction: input→output, consistent with `counting_sort_inplace`),
     the output is uniquely `[1; 2; 3]`. The completeness lemma handles the
     permutation correctly since `SeqP.permutation` is symmetric.
  3. **Concrete verification**: Each element of the output array `b` is
     read and verified.
  4. **In-range verification**: The `S.in_range sb' 3` postcondition is
     verified, confirming all output elements are ≤ `k_val`.
  5. **Resource management**: Demonstrates correct half-permission
     sharing (`A.share`/`A.gather`) for the read-only input array, and
     proper cleanup of both input and output arrays.

### Not Tested: `counting_sort_by_digit`

The third function, `counting_sort_by_digit`, is not tested in this file.
Its postcondition (`Stab.is_stable_sort_on_digit`) involves opaque
digit-level stability properties that would require substantial auxiliary
lemma work to verify in a concrete test. This function is primarily a
subroutine for radix sort and is exercised through the radix sort
implementation.

## Spec Strengthening (2026-03-17)

The following spec improvements were made to `Impl.fsti`:

1. **Permutation direction normalized**: `counting_sort_impl` previously
   used `S.permutation sb' sa` (output→input) while `counting_sort_inplace`
   used `S.permutation s0 s` (input→output). The `counting_sort_impl`
   postcondition was changed to `S.permutation sa sb'` (input→output)
   for consistency across the API. This is semantically equivalent since
   `SeqP.permutation` is symmetric, but makes the API uniform.

2. **`in_range` postcondition added**: Both `counting_sort_impl` and
   `counting_sort_inplace` now include `S.in_range <output> (SZ.v k_val)`
   in their postconditions. This is derivable from `permutation + in_range(input)`
   but stating it explicitly saves callers from needing to prove it themselves.
   Two supporting lemmas were added to `Lemmas.fsti`/`.fst`:
   - `permutation_symmetric`: `permutation s1 s2 → permutation s2 s1`
   - `permutation_preserves_in_range`: `permutation s1 s2 ∧ in_range s1 k → in_range s2 k`

3. **Tests updated**: Both tests now verify the `in_range` postcondition
   in addition to the existing sorted/permutation checks.

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
- **Postconditions**: Fully precise — `sorted ∧ permutation ∧ in_range`
  uniquely determines the output for the tested input `[3;1;2]`.
- **Permutation direction**: Both `counting_sort_impl` and
  `counting_sort_inplace` now use `S.permutation <input> <output>`
  (input→output) consistently.
- **In-range**: Both tests verify the output satisfies
  `S.in_range <output> k_val`.

## Spec Issues Resolved

1. **Permutation direction inconsistency** (resolved): Both variants
   now use `S.permutation <input> <output>` consistently.

2. **Missing `in_range` postcondition** (resolved): Both variants now
   explicitly guarantee `S.in_range <output> (SZ.v k_val)`.

3. **No issues with precondition strength**: Preconditions are satisfiable
   for reasonable inputs. The `SZ.fits` constraints are non-restrictive
   for practical input sizes.

## Concrete Execution Results (C Extraction)

The verified Pulse implementation has been extracted to C via KaRaMeL and
executed concretely. Both test functions were extracted, compiled, and run
successfully.

### Extraction Pipeline

1. **F\* → .krml**: `ImplTest.fst` and `Impl.fst` extracted to `.krml`
   intermediate representation using `--codegen krml`.
2. **KaRaMeL → C**: `.krml` files bundled into `ImplTest.c` using
   `-bundle` options to include only reachable code.
3. **C Compilation**: Compiled with `cc -std=c11` against krmllib runtime.
4. **Execution**: Both tests run and pass.

### Changes for Extraction

- **`Impl.fst`**: Two uses of the `BoundedIntegers` typeclass `+` operator
  on `int`/`nat` types in `counting_sort_inplace` were replaced with
  explicit `Prims.op_Addition` calls. The BoundedIntegers typeclass dispatch
  extracts to a record pattern match that KaRaMeL cannot translate to C.
  SizeT arithmetic (using `+` on `SZ.t`) was unaffected.

### Test Output

```
=== Counting Sort C Extraction Tests ===

Test 1: counting_sort_inplace [3,1,2] -> [1,2,3] ...
  PASSED

Test 2: counting_sort_impl [3,1,2] -> [1,2,3] ...
  PASSED

All tests passed.
```

### Build Instructions

```bash
make test-c   # Extract to C, compile, and run tests
```
