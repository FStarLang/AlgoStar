# CLRS.Ch09.PartialSelectionSort.ImplTest — Spec Validation Report

## Overview

Tests `select` from `CLRS.Ch09.PartialSelectionSort.Impl` on a concrete
3-element array `[5, 2, 8]` with k=1, k=2, k=3 (1-indexed), expecting
results 2, 5, 8 respectively.

**Source:** Adapted from
[Test.PartialSelectionSort.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.PartialSelectionSort.fst)

## What is tested

| Test function    | Input     | k  | Expected |
|------------------|-----------|---:|----------|
| `test_select_k1` | [5, 2, 8] | 1  | 2        |
| `test_select_k2` | [5, 2, 8] | 2  | 5        |
| `test_select_k3` | [5, 2, 8] | 3  | 8        |

## What is proven

1. **Precondition satisfiability**: `select` can be called with `n > 0`,
   `k > 0`, `k <= n` (k is 1-indexed).

2. **Postcondition precision**: The strengthened postcondition includes
   `result == select_spec s0 (k-1)`, which directly links the result to the
   k-th smallest element of the sorted input. This is verified via
   `assert_norm` for each concrete input:
   - `select_spec [5;2;8] 0 = (pure_sort [5;2;8])[0] = [2;5;8][0] = 2`
   - `select_spec [5;2;8] 1 = (pure_sort [5;2;8])[1] = [2;5;8][1] = 5`
   - `select_spec [5;2;8] 2 = (pure_sort [5;2;8])[2] = [2;5;8][2] = 8`

3. **No admits, no assumes**: All assertions are proven by SMT + `assert_norm`.

## Spec strengthening

The `select` postcondition was strengthened to include
`result == PSSSpec.select_spec s0 (SZ.v k - 1)`, matching the approach used by
`quickselect`. This was achieved by:

1. Adding a `seq_perm_implies_is_perm` bridge lemma to
   `PartialSelectionSort.Lemmas` that converts from `Seq.Properties.permutation`
   to the `count_occ`-based `is_permutation` used by `pulse_correctness_hint`.

2. Adding a `select_correctness` helper in `Impl.fst` that:
   - Reveals the opaque `permutation` predicate
   - Bridges to `is_permutation`
   - Calls `pulse_correctness_hint` to establish `s_final[k-1] == select_spec s0 (k-1)`

**Previous approach**: The test required a custom `completeness_select_k1` lemma
using `reveal_opaque` and count-based reasoning (`SP.count`) to determine the
output from the opaque permutation. This was complex and only covered k=1.

**New approach**: The `result == select_spec s0 (k-1)` postcondition clause
is directly computable via `assert_norm`, making test validation trivial for
any value of k. No `reveal_opaque` or completeness lemmas needed in tests.

## Proof details

- `--z3rlimit 400 --fuel 8 --ifuel 4`
- The `select_spec_*` helper lemmas use `assert_norm` to normalize `select_spec`
  (via `pure_sort`, an insertion sort on sequences) for concrete inputs.

## Spec assessment

**Postcondition quality: PRECISE** — The `result == select_spec s0 (k-1)` clause
is the strongest possible specification for a selection algorithm. It directly
states that the result is the (k-1)-th element of the sorted input (k is
1-indexed in `select`). The sorted_prefix, prefix_leq_suffix, and permutation
properties are also maintained. This matches the precision of the Quickselect
specification.
