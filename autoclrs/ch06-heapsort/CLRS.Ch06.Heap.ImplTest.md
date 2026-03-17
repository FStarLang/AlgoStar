# Heapsort Specification Validation Test

## Source Attribution

Adapted from
[Test.Quicksort.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
in the intent-formalization repository, following the spec-validation
methodology from [arXiv:2406.09757](https://arxiv.org/abs/2406.09757).

## What Is Tested

`CLRS.Ch06.Heap.ImplTest.fst` contains a single test function
`test_heapsort_3` that exercises the `heapsort` function from
`CLRS.Ch06.Heap.Impl.fsti`.

### Test Case

- **Input:** array `[3; 1; 2]` (3 elements, distinct values)
- **Operation:** `heapsort arr 3sz ctr`
- **Expected output:** `[1; 2; 3]`

### What Is Proven

1. **Precondition satisfiability.** The test constructs a concrete array
   and ghost counter, demonstrating that all preconditions are
   satisfiable:
   - `SZ.v n <= A.length a` (3 ≤ 3)
   - `Seq.length s0 == A.length a` (3 == 3)
   - `SZ.fits (op_Multiply 2 (Seq.length s0) + 2)` (`SZ.fits 8`, trivial)

2. **Postcondition precision (completeness).** After heapsort returns,
   the test proves that the postcondition uniquely determines the output:
   - `sorted_upto s 3` — the first 3 elements are sorted
   - `permutation s0 s` — the output is a permutation of the input
   - Together, these imply `s[0] == 1 ∧ s[1] == 2 ∧ s[2] == 3`

3. **Element-level verification.** Each output element is read from the
   array and individually asserted to equal its expected value.

### Proof Strategy

The completeness proof uses two auxiliary lemmas:

- **`std_sort3`**: A pure lemma proving that any sorted permutation of
  `[3; 1; 2]` must be `[1; 2; 3]`. Uses `SP.count` to establish that
  each element (1, 2, 3) appears exactly once, plus counts of 0 and 4
  to bound the element range.

- **`completeness_sort3`**: Bridges from heapsort's postcondition
  predicates (`sorted_upto`, `permutation`) to `std_sort3`. First
  establishes `Seq.equal s0 (Seq.seq_of_list [3; 1; 2])` from the known
  indices of `s0` (set by array writes), then delegates to `std_sort3`.

Unlike the quicksort test which requires a BoundedIntegers-to-Prims
bridge lemma, heapsort's `sorted_upto` already uses standard Prims
comparison operators, making the connection direct.

The opaque `permutation` wrapper is revealed via
`reveal_opaque (`%permutation) (permutation s0 s)` to expose the
underlying `SeqP.permutation int s0 s`.

## Verification Status

| Property | Status |
|----------|--------|
| Admits | **0** |
| Assumes | **0** |
| Precondition satisfiable | ✅ Proven |
| Postcondition precise | ✅ Proven (output uniquely determined) |

## Specification Assessment

The heapsort specification in `Impl.fsti` is **complete and precise**
for functional correctness:

- **`sorted_upto s n`** correctly captures that the first `n` elements
  are sorted, using standard Prims comparison operators.

- **`permutation s0 s`** correctly captures that the output is a
  rearrangement of the input.

- Together, `sorted_upto + permutation` is the **strongest possible
  functional specification** for an in-place sorting algorithm — it
  uniquely determines the output for any input with distinct elements.

- The `SZ.fits(2*n+2)` precondition is a reasonable overflow guard
  (limits arrays to ~half of `SizeT.max`).

- No specification gaps or weaknesses were found during testing.
