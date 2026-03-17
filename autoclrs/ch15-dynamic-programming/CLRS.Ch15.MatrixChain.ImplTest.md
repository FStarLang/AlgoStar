# Matrix Chain Multiplication — Spec Validation Test

**File:** `CLRS.Ch15.MatrixChain.ImplTest.fst`
**Source:** Adapted from [Test.MatrixChain.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch15-dynamic-programming/Test.MatrixChain.fst)

## Test Instance

| Parameter | Value |
|-----------|-------|
| `dims`    | `[10, 30, 5, 60]` |
| `n`       | `3` (three matrices) |
| **Expected result** | `4500` |

Three matrices: A₁(10×30), A₂(30×5), A₃(5×60).
Optimal parenthesization: (A₁A₂)A₃ → cost = 10·30·5 + 10·5·60 = 1500 + 3000 = 4500.

## What Is Proven

### 1. Precondition satisfiability

The lemma `mc_pre_satisfiable` proves:
```fstar
SZ.v 3sz > 0 /\
SZ.fits (op_Multiply (SZ.v 3sz) (SZ.v 3sz))
```

The remaining preconditions — array length matching (`SZ.v n + 1 == Seq.length s_dims`)
and positive dimensions (`forall i. Seq.index s_dims i > 0`) — are established
structurally after array initialization.

### 2. Postcondition precision

After calling `matrix_chain_order`, the postcondition gives:
```
result == mc_result s_dims 3
```

The lemma `mc_expected` proves via `assert_norm`:
```fstar
mc_result (Seq.seq_of_list [10; 30; 5; 60]) 3 == 4500
```

Together these establish `result == 4500` with full proof — the postcondition
is **precise enough** to determine the exact output for a concrete input.

### 3. No admits, no assumes

The test is fully verified by F* and Z3 with no admits or assumes.

## Findings

**The Matrix Chain specification is precise for its primary postcondition.**
The postcondition `result == mc_result s_dims n` directly computes to the
correct concrete value.

**Note:** The postcondition uses `mc_result` (the imperative mirror spec),
not `mc_cost` (the enumerative recursive optimum). The bridge lemma
`mc_result_eq_mc_cost` connects them but requires `all_costs_bounded` —
a sentinel-dependent condition. This sentinel limitation
(documented in CLRS.Ch15.MatrixChain.Review.md) is not exercised by this
test since we validate `mc_result` directly.
