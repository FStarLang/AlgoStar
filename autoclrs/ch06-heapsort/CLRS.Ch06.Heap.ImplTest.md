# Heapsort Specification Validation Tests

## Source Attribution

Adapted from
[Test.Quicksort.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
in the intent-formalization repository, following the spec-validation
methodology from [arXiv:2406.09757](https://arxiv.org/abs/2406.09757).

## What Is Tested

`CLRS.Ch06.Heap.ImplTest.fst` contains five test functions exercising
the `heapsort` and `build_max_heap` APIs from `CLRS.Ch06.Heap.Impl.fsti`.

### Test 1: `test_heapsort_3` — Postcondition completeness

- **Input:** `[3; 1; 2]`, n=3
- **Operation:** `heapsort arr 3sz ctr`
- **Expected output:** `[1; 2; 3]`
- **What is proven:** `sorted_upto + permutation` uniquely determines
  the output for distinct elements. Each element is read and asserted.

### Test 2: `test_build_max_heap_3` — Root = maximum

- **Input:** `[3; 1; 2]`, n=3
- **Operation:** `build_max_heap arr 3sz ctr`
- **Expected output:** `s[0] == 3` (root is the maximum)
- **What is proven:** `is_max_heap + permutation` is strong enough to
  determine the root equals `max(input)`. Uses `root_ge_element` from
  Lemmas to establish `s[0] >= s[i]` for all `i < 3`, then count
  reasoning pins the root to 3.

### Test 3: `test_heapsort_0` — Identity (n=0)

- **Input:** `[5; 3; 7]`, n=0
- **Operation:** `heapsort arr 0sz ctr`
- **Expected output:** `[5; 3; 7]` (unchanged)
- **What is proven:** With n=0, the `forall k. 0 <= k < length s ==>
  s[k] == s0[k]` clause covers all indices, proving the array is
  completely unchanged. Validates that heapsort handles the empty-prefix
  edge case correctly.

### Test 4: `test_heapsort_prefix` — Prefix sorting (n < array length)

- **Input:** `[7; 5; 3]`, n=2
- **Operation:** `heapsort arr 2sz ctr`
- **Expected output:** `[5; 7; 3]` (first 2 sorted, third preserved)
- **What is proven:** The `sorted_upto s 2` clause sorts the prefix,
  and the preservation clause `forall k. 2 <= k < 3 ==> s[k] == s0[k]`
  keeps `s[2] == 3`. Combined with permutation, the output is uniquely
  determined: `s[0] == 5, s[1] == 7, s[2] == 3`.

### Test 5: `test_heapsort_duplicates` — Duplicate elements

- **Input:** `[2; 1; 2]`, n=3
- **Operation:** `heapsort arr 3sz ctr`
- **Expected output:** `[1; 2; 2]`
- **What is proven:** `sorted_upto + permutation` uniquely determines
  the output even with duplicate elements. Count reasoning with
  `count(1)=1, count(2)=2` pins the output.

### Postcondition Clauses Exercised

| Postcondition clause | Test 1 | Test 2 | Test 3 | Test 4 | Test 5 |
|---------------------|:------:|:------:|:------:|:------:|:------:|
| `sorted_upto s n` | ✅ | — | ✅ | ✅ | ✅ |
| `is_max_heap s n` | — | ✅ | — | — | — |
| `permutation s0 s` | ✅ | ✅ | ✅ | ✅ | ✅ |
| `forall k. n<=k<len ==> s[k]==s0[k]` | — | — | ✅ | ✅ | — |
| `Seq.length s == Seq.length s0` | ✅ | ✅ | ✅ | ✅ | ✅ |

### Proof Strategy

All completeness proofs use the same pattern:

1. **Establish `Seq.equal s0 (Seq.seq_of_list input)`** from the known
   array writes, enabling Z3 to use `assert_norm` count facts.

2. **Use `SP.count` to establish element multiplicities** — counts of
   each element plus boundary values (e.g., count of 0 and 4 for inputs
   in {1,2,3}) constrain the multiset.

3. **Apply ordering constraints** — `sorted_upto` (heapsort) or
   `root_ge_element` (build_max_heap) pins element positions.

The opaque `permutation` wrapper is revealed via
`reveal_opaque (`%permutation) (permutation s0 s)` to expose the
underlying `SeqP.permutation int s0 s`.

Unlike the quicksort test which requires a BoundedIntegers-to-Prims
bridge lemma, heapsort's `sorted_upto` already uses standard Prims
comparison operators, making the connection direct.

## Verification Status

| Property | Status |
|----------|--------|
| Admits | **0** |
| Assumes | **0** |
| Test functions | **5** |
| Preconditions satisfiable | ✅ All 5 proven |
| Postconditions precise | ✅ Output determined in all tests |
| Functions tested | `heapsort` (4 tests), `build_max_heap` (1 test) |

## Specification Assessment

The specifications in `Impl.fsti` are **complete and precise** for
functional correctness:

- **`sorted_upto s n`** correctly captures that the first `n` elements
  are sorted, using standard Prims comparison operators.

- **`permutation s0 s`** correctly captures that the output is a
  rearrangement of the input.

- **`is_max_heap s n`** correctly captures the max-heap property;
  combined with `permutation`, it determines the root equals the maximum
  of the input.

- Together, `sorted_upto + permutation` is the **strongest possible
  functional specification** for an in-place sorting algorithm — it
  uniquely determines the output for any input, including those with
  duplicate elements.

- The preservation clause `forall k. n <= k < len ==> s[k] == s0[k]`
  correctly supports prefix sorting, ensuring elements beyond the
  sorted range are untouched.

- The `SZ.fits(2*n+2)` precondition is a reasonable overflow guard
  (limits arrays to ~half of `SizeT.max`).

- **No specification gaps or weaknesses were found.** All five
  postcondition clauses are exercised by the test suite and found to
  be sufficiently constraining.
