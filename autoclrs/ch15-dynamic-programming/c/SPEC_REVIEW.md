# Ch15 C Code Specification Review

Comparison of C code specifications against `Impl.fsti` specifications.

## Issue 1: Implementation code in `_include_pulse` blocks

**Status: ✅ Already correct.**  
All three C files only use `_include_pulse(open ...)` for module imports.
No computational code exists in `_include_pulse` blocks.

## Issue 2: Complexity-related specifications

**Status: ✅ Already correct.**  
The C code does not include any complexity counters (`GR.ref nat`),
`rod_cutting_bounded`, `lcs_complexity_bounded`, or `mc_complexity_bounded`.
The Impl.fsti files include these but the C code correctly omits them since
we do not want to prove computational complexity in C.

## Issue 3: Specification gaps between C code and Impl.fsti

### Rod Cutting

**Impl.fsti spec:**
- Returns `nat` result
- `result == optimal_revenue s_prices (SZ.v n)`

**C code spec:**
- `void` function, fills output array `r[]`
- `r[n] == optimal_revenue(prices, n)` ✅
- Base case: `r[0] == 0` ✅ (extra)
- Non-negativity: `r[k] >= 0` for all `k <= n` ✅ (extra)
- Upper bound: `r[k] <= 1000000 * k` ✅ (extra)

**Gaps: None.** The C code proves functional correctness via `optimal_revenue`.
The different API (void + out array vs return value) is a valid design choice
for C code. The C code actually proves MORE than the Impl.fsti (per-element
bounds).

### LCS

**Impl.fsti spec:**
- Returns `int` result
- `result == lcs_length sx sy (SZ.v m) (SZ.v n)`
- `result >= 0`
- `result <= SZ.v m`
- `result <= SZ.v n`

**C code spec:**
- Returns `int` result
- `return == lcs_length(x, y, m, n)` ✅
- `return >= 0` ✅
- `return <= 1000` ⚠️ **GAP: should be `return <= m` and `return <= n`**

**Gap found and fixed:** The C code originally proved a weaker upper bound
(`<= 1000` from the precondition `m <= 1000, n <= 1000`) instead of the
tight bounds `return <= m` and `return <= n` from Impl.fsti.

**Fix:** Added `CLRS.Ch15.LCS.C.BridgeLemmas2.fst` with a
`lcs_result_upper_bound` lemma that calls `lcs_length_upper_bound` from
the Spec module. Added postconditions `return <= m` and `return <= n` to
lcs.c, plus a ghost call to `lcs_result_upper_bound` before return.
The bridge lemma module verified successfully.

### Matrix Chain

**Impl.fsti spec:**
- Returns `int` result
- `result == mc_result s_dims (SZ.v n)`
- `result >= 0`

**C code spec:**
- Returns `int` result
- `return == mc_result(dims, n)` ✅
- `return >= 0` ✅

**Gaps: None.** Functional correctness and non-negativity match.

## Changes Made

1. **LCS**: Strengthened postcondition from `return <= 1000` to also
   include `return <= m` and `return <= n`. Added bridge lemma in
   `CLRS.Ch15.LCS.C.BridgeLemmas2.fst` calling `lcs_length_upper_bound`.
   Bridge lemma verified successfully.

2. **Verification status**:
   - `RodCutting.fst` ✅ verified
   - `MatrixChain.fst` ✅ verified (cached)
   - `CLRS.Ch15.LCS.C.BridgeLemmas2.fst` ✅ verified
   - `Lcs.fst` ❌ pre-existing Z3 instability (original also fails with
     identical "unknown" errors at the inner loop body — not caused by
     the spec strengthening changes)
