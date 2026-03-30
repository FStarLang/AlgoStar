# CLRS.Ch09.SimultaneousMinMax.ImplTest — Spec Validation Report

## Overview

Tests `find_minmax` and `find_minmax_pairs` from
`CLRS.Ch09.SimultaneousMinMax.Impl` on a concrete 3-element array `[5, 2, 8]`.

**Source:** Adapted from
[Test.SimultaneousMinMax.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.SimultaneousMinMax.fst)

## What is tested

| Test function             | Input     | Expected min | Expected max |
|---------------------------|-----------|-------------|-------------|
| `test_find_minmax`        | [5, 2, 8] | 2           | 8           |
| `test_find_minmax_pairs`  | [5, 2, 8] | 2           | 8           |

## What is proven

1. **Precondition satisfiability**: Both functions can be called on a valid
   3-element array (`len >= 1`).

2. **Postcondition precision**: The postcondition uniquely determines both
   `result.min_val` and `result.max_val`:
   - *Min existence + universality*: exactly one value in `{5, 2, 8}` is ≤ all
     others → `min_val == 2`
   - *Max existence + universality*: exactly one value in `{5, 2, 8}` is ≥ all
     others → `max_val == 8`

3. **No admits, no assumes**: All assertions are proven by SMT.

## Proof details

- `--z3rlimit 400 --fuel 8 --ifuel 4`
- Total verification time: ~2s
- Read-only array (fractional permission `#p`), so input sequence is directly
  available in postcondition reasoning.

## Spec assessment

**Postcondition quality: PRECISE** — The postcondition for both functions is
identical in structure (existence + universality for both min and max) and
uniquely determines the output. No weaknesses found.

## C Extraction & Concrete Execution

Each test function returns `bool` with `ensures pure (r == true)`:
1. **PROOF** (ghost, erased): Postcondition uniquely determines the result
2. **RUNTIME** (concrete, survives extraction): `int_eq` comparison returns bool

The extracted C code captures return values and performs concrete equality checks:

```
[SimultaneousMinMax]
  PASS: find_minmax([5,2,8]) min==2 max==8
  PASS: find_minmax_pairs([5,2,8]) min==2 max==8
```

**Status: ✅ All concrete execution results match the verified specification.**
