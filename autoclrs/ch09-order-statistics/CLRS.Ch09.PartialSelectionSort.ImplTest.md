# CLRS.Ch09.PartialSelectionSort.ImplTest — Spec Validation Report

## Overview

Tests `select` from `CLRS.Ch09.PartialSelectionSort.Impl` on a concrete
3-element array `[5, 2, 8]` with k=1 (1-indexed), expecting result == 2.

**Source:** Adapted from
[Test.PartialSelectionSort.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.PartialSelectionSort.fst)

## What is tested

| Test function  | Input     | k  | Expected |
|----------------|-----------|---:|----------|
| `test_select`  | [5, 2, 8] | 1  | 2        |

## What is proven

1. **Precondition satisfiability**: `select` can be called with `n > 0`,
   `k > 0`, `k <= n` (k is 1-indexed).

2. **Postcondition precision**: The postcondition provides:
   - `permutation s0 s_final` (opaque to SMT)
   - `sorted_prefix s_final k` — first k elements are sorted
   - `prefix_leq_suffix s_final k` — first k elements ≤ remaining
   - `result == s_final[k-1]` — result is the last sorted element

   For k=1, `prefix_leq_suffix s_final 1` means `s_final[0] ≤ s_final[j]`
   for all `j ≥ 1`. Combined with the permutation, this uniquely determines
   `s_final[0] == 2` (the minimum of {5, 2, 8}).

3. **No admits, no assumes**: All assertions are proven by SMT.

## Proof technique

The `permutation` predicate in `CLRS.Ch09.PartialSelectionSort.Impl` is
marked `[@@"opaque_to_smt"]`, so Z3 cannot directly reason about element
counts. The test uses:

1. **`with s_final cf.`** to bind the existential output sequence
2. **`reveal_opaque`** to expose `Seq.Properties.permutation int s0 s_final`
3. **`completeness_select_k1`** — a pure lemma that uses count-based reasoning:
   - `SP.count 2 [5;2;8] == 1`, `SP.count 5 ... == 1`, `SP.count 8 ... == 1`
   - Boundary counts: `SP.count 0 ... == 0`, `SP.count 1 ... == 0`, etc.
   - With permutation + minimum property, Z3 determines `s_final[0] == 2`

This pattern mirrors the completeness lemma used in `CLRS.Ch07.Quicksort.ImplTest`.

## Proof details

- `--z3rlimit 400 --fuel 8 --ifuel 4`
- Total verification time: ~6s
- The completeness lemma takes ~1.8s; the `completeness_select_k1 s_final`
  call inside the Pulse function takes ~2.7s.

## Spec assessment

**Postcondition quality: PRECISE but requires effort** — The postcondition
is mathematically precise (sorted prefix + prefix ≤ suffix + permutation
uniquely determines the result), but the opaque `permutation` requires
`reveal_opaque` and a completeness lemma to prove precision.

**Comparison with Quickselect**: The Quickselect postcondition includes
`result == select_spec s0 k`, which is directly computable via `assert_norm`
and does not require revealing the opaque permutation. The PartialSelectionSort
postcondition lacks this functional characterization, making spec validation
harder but not impossible.

**No spec weakness found**: The postcondition is strong enough to determine
the result for any concrete input, given sufficient proof effort.
