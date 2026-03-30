# CLRS.Ch09.Quickselect.ImplTest — Spec Validation Report

## Overview

Tests `quickselect` from `CLRS.Ch09.Quickselect.Impl` on a concrete 3-element
array `[5, 2, 8]` for two values of k:
- k=0 (minimum): expects 2
- k=2 (maximum): expects 8

**Source:** Adapted from
[Test.Quickselect.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.Quickselect.fst)

## What is tested

| Test function           | Input     | k  | Expected |
|-------------------------|-----------|---:|----------|
| `test_quickselect_min`  | [5, 2, 8] | 0  | 2        |
| `test_quickselect_max`  | [5, 2, 8] | 2  | 8        |

## What is proven

1. **Precondition satisfiability**: `quickselect` can be called with `n > 0`
   and `k < n` (0-indexed).

2. **Postcondition precision**: The strongest postcondition clause is
   `result == PSSSpec.select_spec s0 k`, which gives a functional specification
   linking the result to the sorted permutation of the input:
   - `select_spec [5;2;8] 0 = (pure_sort [5;2;8])[0] = [2;5;8][0] = 2`
   - `select_spec [5;2;8] 2 = (pure_sort [5;2;8])[2] = [2;5;8][2] = 8`
   - These are computed via `assert_norm` in helper lemmas.

3. **Additional postcondition verification**:
   - `result == Seq.index s_final k` — result is at position k
   - `∀i < k. s_final[i] ≤ result` — left partition ≤ result
   - `∀i > k. result ≤ s_final[i]` — right partition ≥ result
   - `permutation s0 s_final` — output is a permutation of input

4. **No admits, no assumes**: All assertions are proven by SMT + `assert_norm`.

## Proof technique

The `select_spec_0` and `select_spec_2` helper lemmas use `assert_norm` to
evaluate `select_spec` (which normalizes through `pure_sort`, an insertion sort
on sequences) for concrete inputs. The postcondition's
`result == select_spec s0 k` clause then directly connects the result to the
expected value.

## Proof details

- `--z3rlimit 400 --fuel 8 --ifuel 4`
- Total verification time: ~3s

## Spec assessment

**Postcondition quality: PRECISE** — The `result == select_spec s0 k` clause
is the strongest possible specification for a selection algorithm. It directly
states that the result is the k-th element of the sorted input. The partition
property and permutation are also verified. No weaknesses found.

## C Extraction & Concrete Execution

Each test function returns `bool` with `ensures pure (r == true)`:
1. **PROOF** (ghost, erased): Postcondition uniquely determines the result
2. **RUNTIME** (concrete, survives extraction): `int_eq` comparison returns bool

The extracted C code captures return values and performs concrete equality checks:

```
[Quickselect]
  PASS: quickselect([5,2,8], k=0) == 2
  PASS: quickselect([5,2,8], k=2) == 8
```

**Status: ✅ All concrete execution results match the verified specification.**
