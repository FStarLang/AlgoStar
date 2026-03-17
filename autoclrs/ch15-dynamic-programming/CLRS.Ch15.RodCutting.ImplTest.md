# Rod Cutting — Spec Validation Test

**File:** `CLRS.Ch15.RodCutting.ImplTest.fst`
**Source:** Adapted from [Test.RodCutting.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch15-dynamic-programming/Test.RodCutting.fst)

## Test Instance

| Parameter | Value |
|-----------|-------|
| `prices`  | `[1, 5, 8, 9]` |
| `n`       | `4` |
| **Expected result** | `10` |

Optimal cut: two pieces of length 2 → revenue = 5 + 5 = 10.

## What Is Proven

### 1. Precondition satisfiability

The lemma `rod_cutting_pre_satisfiable` proves:
```fstar
SZ.fits (SZ.v 4sz + 1)
```

The array length and `n` matching constraints (`SZ.v n == Seq.length s_prices`,
`SZ.v n == A.length prices`) are established structurally via `A.pts_to_len`.

### 2. Postcondition precision

After calling `rod_cutting`, the postcondition gives:
```
result == optimal_revenue s_prices 4
```

The lemma `rod_cutting_expected` proves via `assert_norm`:
```fstar
optimal_revenue (Seq.seq_of_list [1; 5; 8; 9]) 4 == 10
```

Together these establish `result == 10` with full proof — the postcondition
is **precise enough** to determine the exact output for a concrete input.

### 3. No admits, no assumes

The test is fully verified by F* and Z3 with no admits or assumes.

## Findings

**The Rod Cutting specification is fully precise.** The postcondition
`result == optimal_revenue s_prices n` directly computes to the correct
concrete value. Non-negativity is guaranteed by the return type (`nat`),
which is stronger than what LCS and MatrixChain achieve through
postcondition constraints — it is enforced at the type level.
No spec weaknesses were found.
