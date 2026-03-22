# Longest Common Subsequence — Spec Validation Test

**File:** `CLRS.Ch15.LCS.ImplTest.fst`
**Source:** Adapted from [Test.LCS.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch15-dynamic-programming/Test.LCS.fst)

## Test Instance

| Parameter | Value |
|-----------|-------|
| `x`       | `[1, 2, 3]` |
| `y`       | `[2, 3, 4]` |
| `m`, `n`  | `3`, `3` |
| **Expected result** | `2` |

The longest common subsequence is [2, 3], of length 2.

## What Is Proven

### 1. Precondition satisfiability

The lemma `lcs_pre_satisfiable` proves:
```fstar
SZ.fits (op_Multiply (SZ.v 3sz + 1) (SZ.v 3sz + 1))
```

The array length matching constraints are established structurally
via `A.pts_to_len`.

### 2. Postcondition precision

After calling `lcs`, the postcondition gives:
```
result == lcs_length sx sy 3 3
```

The lemma `lcs_expected` proves via `assert_norm`:
```fstar
lcs_length (Seq.seq_of_list [1; 2; 3]) (Seq.seq_of_list [2; 3; 4]) 3 3 == 2
```

Together these establish `result == 2` with full proof — the postcondition
is **precise enough** to determine the exact output for a concrete input.

### 3. Non-negativity (from strengthened spec)

The postcondition now includes `result >= 0`, proven directly by the
implementation calling `lcs_length_nonneg`. The test verifies:
```fstar
assert (pure (result >= 0))
```
This succeeds without any additional lemma calls — the property flows
directly from the postcondition.

### 4. Upper bounds (from strengthened spec)

The postcondition now includes `result <= SZ.v m /\ result <= SZ.v n`,
proven by the implementation calling `lcs_length_upper_bound`. The test
verifies:
```fstar
assert (pure (result <= 3))   // result <= m
assert (pure (result <= 3))   // result <= n
```

### 5. No admits, no assumes

The test is fully verified by F* and Z3 with no admits or assumes.

## Spec Strengthening Summary

The `Impl.fsti` postcondition was strengthened from:
```
result == lcs_length sx sy m n
```
to:
```
result == lcs_length sx sy m n /\
result >= 0 /\
result <= SZ.v m /\
result <= SZ.v n
```

This allows callers (including this test) to derive range properties
directly from the postcondition without importing additional lemmas.
The proofs use `lcs_length_nonneg` and `lcs_length_upper_bound` from
`CLRS.Ch15.LCS.Spec`.

## Concrete Execution

**Status: PASS** — The C test driver (`test_main.c`) implements the same
bottom-up DP algorithm and confirms `lcs([1,2,3], [2,3,4], 3, 3) == 2`.

The Pulse `fn lcs` uses `Pulse.Lib.Dv.while_` with closure arguments
that KaRaMeL cannot translate to C directly. The C test mirrors the verified
algorithm structure exactly: nested loops filling the `(m+1) × (n+1)` DP table
with the same recurrence.

## Findings

**The LCS specification is fully precise with complete range constraints.**
The postcondition `result == lcs_length sx sy m n` directly computes to
the correct concrete value, and the range properties `result >= 0`,
`result <= m`, `result <= n` are proven as part of the postcondition.
This is further strengthened by the lemma `lcs_length_is_longest`
(in Lemmas.fst), which proves that `lcs_length` is both an upper bound
on all common subsequences and is achieved by a constructive witness —
the **strongest possible correctness specification**.
