# Rabin-Karp — Spec Validation Test

**File**: `CLRS.Ch32.RabinKarp.ImplTest.fst`
**Algorithm**: Rabin-Karp String Matching (CLRS §32.2)
**Status**: ✅ Fully verified — no admits, no assumes

## Test Case

| Parameter | Value |
|-----------|-------|
| Text | `[1, 2, 1, 2, 1]` (length 5, `nat`) |
| Pattern | `[1, 2, 1]` (length 3, `nat`) |
| d (radix) | 10 |
| q (modulus) | 13 |
| Expected count | 2 |

## What Is Proven

### 1. Precondition satisfiability

The test constructs a valid call to `rabin_karp` with concrete `nat` arrays
and hash parameters `d=10`, `q=13`, demonstrating that all preconditions are
satisfiable:

- `SZ.v m > 0` — pattern length 3 > 0
- `SZ.v m <= SZ.v n` — 3 ≤ 5
- `SZ.fits (SZ.v n - SZ.v m + 2)` — `SZ.fits 4`
- `SZ.fits (SZ.v n + 1)` — `SZ.fits 6`

### 2. Postcondition precision

The postcondition states:
```
result >= 0 /\ result <= SZ.v n - SZ.v m + 1 /\
result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1)
```

The test proves via `rk_count_matches_is_2` that for the concrete input,
`count_matches_up_to` evaluates to exactly 2. This establishes that the
postcondition uniquely determines the result.

The assertion `assert (pure (count == 2))` is proven without admits.

Note: The Rabin-Karp `count_matches_up_to` is defined locally in
`CLRS.Ch32.RabinKarp.fst` and uses `RKSpec.matches_at_dec` — the count
is independent of the hash parameters `d` and `q`.

### 3. Hash parameter independence

The correctness of the count is proven for specific hash parameters (`d=10`,
`q=13`), but the postcondition guarantees `result == count_matches_up_to ...`
which does not depend on `d` or `q`. The hash parameters only affect
performance (number of spurious hash collisions), not correctness.

## Specification Assessment

The postcondition of `rabin_karp` is **precise**: for any concrete input, it
uniquely determines the output count regardless of hash parameters. The
specification correctly captures the CLRS Rabin-Karp algorithm's behavior.

**No specification weaknesses found.** The precondition is satisfiable and the
postcondition is precise.

## Proof Technique

- **Pure helper lemma** (`rk_count_matches_is_2`): Takes abstract `nat`
  sequences with known element values and proves the count via Z3 evaluation.
- **`A.op_Array_Assignment`**: Used for array writes (the `.(idx) <- val`
  sugar is not used to avoid potential type inference issues with `nat`).
- **Z3 evaluation**: `--fuel 8 --ifuel 4 --z3rlimit 100` is sufficient for
  Z3 to evaluate the recursive spec functions on concrete data.
