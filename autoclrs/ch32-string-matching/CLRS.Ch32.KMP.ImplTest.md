# KMP — Spec Validation Test

**File**: `CLRS.Ch32.KMP.ImplTest.fst`
**Algorithm**: KMP String Matching (CLRS §32.4)
**Status**: ✅ Fully verified — no admits, no assumes

## Test Case

| Parameter | Value |
|-----------|-------|
| Text | `[0, 1, 0, 1, 0]` (length 5, `int`) |
| Pattern | `[0, 1, 0]` (length 3, `int`) |
| Expected count | 2 |

## What Is Proven

### 1. Precondition satisfiability

The test constructs a valid call to `kmp_string_match` with concrete `int`
arrays, demonstrating that all preconditions are satisfiable:

- `SZ.v m > 0` — pattern length 3 > 0
- `SZ.v n >= SZ.v m` — 5 ≥ 3
- `SZ.fits (SZ.v n + 1)` — `SZ.fits 6`
- `SZ.fits (SZ.v m + 1)` — `SZ.fits 4`
- `SZ.fits (2 * SZ.v n)` — `SZ.fits 10`
- `SZ.fits (2 * (SZ.v m - 1))` — `SZ.fits 4`
- `SZ.fits (2 * SZ.v n + 2 * SZ.v m)` — `SZ.fits 16`

### 2. Postcondition precision

The postcondition states:
```
SZ.v count == Spec.count_matches_spec (reveal s_text) (reveal s_pat) (SZ.v n) (SZ.v m) /\
kmp_total_complexity_bound cf (reveal c0) (SZ.v n) (SZ.v m)
```

The test proves via `kmp_count_matches_is_2` that for the concrete input,
`Spec.count_matches_spec` evaluates to exactly 2. This establishes that the
postcondition uniquely determines the result.

The assertion `assert (pure (SZ.v count == 2))` is proven without admits.

### 3. Relationship to existing KMP.Test.fst

The existing `CLRS.Ch32.KMP.Test.fst` tests only precondition satisfiability
(it calls `kmp_string_match` but does not verify the output). This new
`KMP.ImplTest.fst` goes further by proving **postcondition precision**: the
output is uniquely determined to be 2.

## Specification Assessment

The postcondition of `kmp_string_match` is **precise**: for any concrete
input, `count_matches_spec` uniquely determines the output count. The
specification additionally proves the O(n+m) complexity bound
(`kmp_total_complexity_bound`).

**No specification weaknesses found.** The precondition is satisfiable and the
postcondition is precise.

## Proof Technique

- **Pure helper lemma** (`kmp_count_matches_is_2`): Takes abstract `int`
  sequences with known element values and proves the count via Z3 evaluation.
- **KMP spec path**: `count_matches_spec text pat 5 3` →
  `count_matches_up_to text pat 5 3 0` → evaluates `matches_at_dec` at each
  position → 2 matches found.
- **Z3 evaluation**: `--fuel 8 --ifuel 4 --z3rlimit 100` is sufficient.
  The recursion depth is modest: `count_matches_up_to` unfolds 3 times,
  `check_match_at` unfolds up to 4 times per position.
