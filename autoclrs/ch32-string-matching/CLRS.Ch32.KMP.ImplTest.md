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

### Match positions

| Position | Text slice | Match? |
|----------|-----------|--------|
| 0 | `[0,1,0]` | ✅ Proven via `kmp_match_at_0` |
| 1 | `[1,0,1]` | ❌ Proven via `kmp_no_match_at_1` (text[1]=1 ≠ pat[0]=0) |
| 2 | `[0,1,0]` | ✅ Proven via `kmp_match_at_2` |

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

The postcondition (strengthened in this pass) states:
```
SZ.v count <= SZ.v n - SZ.v m + 1 /\
SZ.v count == Spec.count_matches_spec (reveal s_text) (reveal s_pat) (SZ.v n) (SZ.v m) /\
kmp_total_complexity_bound cf (reveal c0) (SZ.v n) (SZ.v m)
```

The test proves via `kmp_count_matches_is_2` that for the concrete input,
`Spec.count_matches_spec` evaluates to exactly 2. This establishes that the
postcondition uniquely determines the result.

The assertion `assert (pure (SZ.v count == 2))` is proven without admits.

**Spec strengthening**: The upper bound was tightened from the previous
`SZ.v count <= SZ.v n + 1` to the precise `SZ.v count <= SZ.v n - SZ.v m + 1`.
This matches the Naive matcher's bound and correctly reflects that at most
`n - m + 1` positions can produce a match. The redundant `SZ.v count >= 0`
(always true for `SZ.t`) was also removed.

### 3. Match position verification

Three auxiliary lemmas verify the individual match positions using
`matches_at` from `CLRS.Ch32.KMP.PureDefs`:

- `kmp_match_at_0`: proves `matches_at text pat 0` (match at position 0)
- `kmp_no_match_at_1`: proves `~(matches_at text pat 1)` (no match at position 1)
- `kmp_match_at_2`: proves `matches_at text pat 2` (match at position 2)

### 4. Relationship to existing KMP.Test.fst

The existing `CLRS.Ch32.KMP.Test.fst` tests only precondition satisfiability
(it calls `kmp_string_match` but does not verify the output). This
`KMP.ImplTest.fst` goes further by proving **postcondition precision** and
**match position verification**.

## Specification Changes

### New lemmas in `CLRS.Ch32.KMP.Spec.fst`

| Lemma | Purpose |
|-------|---------|
| `check_match_at_correct` | Connects `check_match_at` to universal quantifier |
| `matches_at_dec_correct` | Connects `Spec.matches_at_dec` ↔ `PureDefs.matches_at` |
| `count_matches_up_to_bounded` | Proves `count_matches_up_to text pat n m s <= n-m+1-s` |
| `count_matches_spec_bounded` | Proves `count_matches_spec text pat n m <= n-m+1` |

### Postcondition tightening in `CLRS.Ch32.KMP.fst`

| Change | Old | New |
|--------|-----|-----|
| Upper bound | `SZ.v count <= SZ.v n + 1` | `SZ.v count <= SZ.v n - SZ.v m + 1` |
| Redundant bound | `SZ.v count >= 0` | Removed (always true for SZ.t) |

These changes apply to both `kmp_matcher` and `kmp_string_match`.

## Specification Assessment

The postcondition of `kmp_string_match` is **precise**: for any concrete
input, `count_matches_spec` uniquely determines the output count. The
specification additionally proves the O(n+m) complexity bound
(`kmp_total_complexity_bound`) and the tight upper bound on the count.

The new `matches_at_dec_correct` lemma in `KMP.Spec` bridges the decidable
check used by the count function to the propositional `matches_at` predicate,
paralleling the equivalent lemmas in the Naive and Rabin-Karp modules.

**No specification weaknesses remain.** The precondition is satisfiable, the
postcondition is precise, and the upper bound is tight.

## Proof Technique

- **Pure helper lemma** (`kmp_count_matches_is_2`): Takes abstract `int`
  sequences with known element values and proves the count via Z3 evaluation.
- **Match position lemmas**: `kmp_match_at_0`, `kmp_no_match_at_1`,
  `kmp_match_at_2` use Z3 with `--fuel 4 --ifuel 2` to evaluate the
  `matches_at` propositional predicate on concrete data.
- **KMP spec path**: `count_matches_spec text pat 5 3` →
  `count_matches_up_to text pat 5 3 0` → evaluates `matches_at_dec` at each
  position → 2 matches found.
- **Z3 evaluation**: `--fuel 8 --ifuel 4 --z3rlimit 100` is sufficient.
  The recursion depth is modest: `count_matches_up_to` unfolds 3 times,
  `check_match_at` unfolds up to 4 times per position.
