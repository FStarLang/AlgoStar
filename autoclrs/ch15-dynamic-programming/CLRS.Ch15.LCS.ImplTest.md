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

### 3. No admits, no assumes

The test is fully verified by F* and Z3 with no admits or assumes.

## Findings

**The LCS specification is fully precise.** The postcondition
`result == lcs_length sx sy m n` directly computes to the correct
concrete value. This is further strengthened by the lemma
`lcs_length_is_longest` (in Lemmas.fst), which proves that `lcs_length`
is both an upper bound on all common subsequences and is achieved by
a constructive witness — the **strongest possible correctness specification**.
No spec weaknesses were found.
