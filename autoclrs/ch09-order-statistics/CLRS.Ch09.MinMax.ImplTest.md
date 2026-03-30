# CLRS.Ch09.MinMax.ImplTest — Spec Validation Report

## Overview

Tests `find_minimum` and `find_maximum` from `CLRS.Ch09.MinMax.Impl` on a
concrete 3-element array `[5, 2, 8]`.

**Source:** Adapted from
[Test.MinMax.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.MinMax.fst)

## What is tested

| Test function        | Input     | Expected | Assertion             |
|----------------------|-----------|----------|-----------------------|
| `test_find_minimum`  | [5, 2, 8] | 2        | `min_val == 2`        |
| `test_find_maximum`  | [5, 2, 8] | 8        | `max_val == 8`        |

## What is proven

1. **Precondition satisfiability**: The functions can be called on a valid
   3-element array. No issues — the precondition (`len > 0`, `len == length s`,
   `len == A.length a`) is satisfiable.

2. **Postcondition precision**: The postcondition is precise enough to uniquely
   determine the output:
   - *Existence*: `∃k. s0[k] == min_val` — the returned value is in the array
   - *Universality*: `∀k. min_val ≤ s0[k]` — no element is smaller
   - Together these uniquely determine `min_val == 2` for `[5, 2, 8]`
   - Analogously for `max_val == 8`

3. **No admits, no assumes**: All assertions are proven by SMT.

## Proof details

- `--z3rlimit 400 --fuel 8 --ifuel 4`
- Total verification time: ~2s
- The postcondition preserves the original sequence (`#p` permission, read-only)
  so Z3 can reason directly about `s0` values after the call.

## Spec assessment

**Postcondition quality: PRECISE** — The existence + universality postcondition
is the strongest possible specification for min/max. No weaknesses found.

## C Extraction & Concrete Execution

Each test function returns `bool` with `ensures pure (r == true)`:
1. **PROOF** (ghost, erased): Postcondition uniquely determines the result
2. **RUNTIME** (concrete, survives extraction): `int_eq` comparison returns bool

The extracted C code captures return values and performs concrete equality checks:

```
[MinMax]
  PASS: find_minimum([5,2,8]) == 2
  PASS: find_maximum([5,2,8]) == 8
```

**Status: ✅ All concrete execution results match the verified specification.**
