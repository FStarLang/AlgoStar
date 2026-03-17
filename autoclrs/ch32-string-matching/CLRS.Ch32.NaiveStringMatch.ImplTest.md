# Naive String Match — Spec Validation Test

**File**: `CLRS.Ch32.NaiveStringMatch.ImplTest.fst`
**Algorithm**: Naive String Matching (CLRS §32.1)
**Status**: ✅ Fully verified — no admits, no assumes

## Test Case

| Parameter | Value |
|-----------|-------|
| Text | `[1, 2, 1, 2, 1]` (length 5, `int`) |
| Pattern | `[1, 2, 1]` (length 3, `int`) |
| Expected count | 2 |

### Match positions

| Position | Text slice | Match? |
|----------|-----------|--------|
| 0 | `[1,2,1]` | ✅ Proven via `match_at_0` |
| 1 | `[2,1,2]` | ❌ Proven via `no_match_at_1` (text[1]=2 ≠ pat[0]=1) |
| 2 | `[1,2,1]` | ✅ Proven via `match_at_2` |

## What Is Proven

### 1. Precondition satisfiability

The test constructs a valid call to `naive_string_match` with concrete arrays,
demonstrating that all preconditions are satisfiable:

- `SZ.v m > 0` — pattern length 3 > 0
- `SZ.v m <= SZ.v n` — 3 ≤ 5
- `SZ.fits (SZ.v n - SZ.v m + 2)` — `SZ.fits 4`
- `SZ.fits (op_Multiply (SZ.v n - SZ.v m + 1) (SZ.v m))` — `SZ.fits 9`

### 2. Postcondition precision

The postcondition states:
```
SZ.v result == count_matches_up_to s_text s_pat 3
```

The test proves via `count_matches_is_2` that for the concrete input,
`count_matches_up_to` evaluates to exactly 2. This establishes that the
postcondition uniquely determines the result.

The assertion `assert (pure (SZ.v count == 2))` is proven without admits.

### 3. Match position verification

Three auxiliary lemmas verify the individual match positions:
- `match_at_0`: proves `matches_at text pat 0` (propositional match at position 0)
- `no_match_at_1`: proves `~(matches_at text pat 1)` (no match at position 1)
- `match_at_2`: proves `matches_at text pat 2` (propositional match at position 2)

## Specification Assessment

The postcondition of `naive_string_match` is **precise**: for any concrete
input, it uniquely determines the output count. The specification is sufficient
to prove the exact match count, and the `matches_at` predicate correctly
captures the CLRS notion of a valid shift.

**No specification weaknesses found.** The precondition is satisfiable and the
postcondition is precise.

## Proof Technique

- **Pure helper lemma** (`count_matches_is_2`): Takes abstract sequences with
  known element values and proves the count via Z3 evaluation with
  `--fuel 8 --ifuel 4`.
- **Z3 evaluation**: The recursive `count_matches_up_to` (depth 3) and
  `check_match_at` (depth 3 per call) are evaluated by Z3 with sufficient fuel.
- **No `assert_norm`**: The proof relies entirely on Z3's ability to evaluate
  the pure spec functions on concrete data.
