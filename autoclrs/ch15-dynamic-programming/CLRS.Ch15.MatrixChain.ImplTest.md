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

### 3. Non-negativity (from strengthened spec)

The postcondition now includes `result >= 0`, proven by the implementation
calling `mc_result_nonneg` (from `CLRS.Ch15.MatrixChain.Spec`). The test
verifies:
```fstar
assert (pure (result >= 0))
```
This succeeds without any additional lemma calls — the property flows
directly from the postcondition.

### 4. No admits, no assumes

The test is fully verified by F* and Z3 with no admits or assumes.
Uses `--z3rlimit 20` (localized).

## Spec Strengthening Summary

The `Impl.fsti` postcondition was strengthened from:
```
result == mc_result s_dims n
```
to:
```
result == mc_result s_dims n /\
result >= 0
```

The non-negativity proof works directly on the mirror spec (`mc_inner_k`,
`mc_inner_i`, `mc_outer`) by showing all table entries remain non-negative:
- Initial table: all zeros (non-negative)
- `mc_inner_k` returns a non-negative value when the accumulator is
  non-negative and all table entries and dimensions are non-negative
- `mc_inner_i` preserves table non-negativity by writing `mc_inner_k` results
- `mc_outer` propagates through chain lengths

This avoids the sentinel limitation: `result >= 0` is proven without
requiring `all_costs_bounded`, unlike the `mc_result_eq_mc_cost` bridge.

## Concrete Execution

**Status: PASS** — The C test driver (`test_main.c`) implements the same
bottom-up DP algorithm and confirms `matrix_chain_order([10,30,5,60], 3) == 4500`.

The Pulse `fn matrix_chain_order` uses `Pulse.Lib.Dv.while_` with closure
arguments that KaRaMeL cannot translate to C directly. The C test mirrors the
verified algorithm structure exactly: three nested loops (chain length, starting
position, split point) with the same sentinel-based minimum accumulator.

## Findings

**The Matrix Chain specification is precise with non-negativity guaranteed.**
The postcondition `result == mc_result s_dims n` directly computes to the
correct concrete value, and `result >= 0` is proven as part of the
postcondition.

**Note:** The postcondition uses `mc_result` (the imperative mirror spec),
not `mc_cost` (the enumerative recursive optimum). The bridge lemma
`mc_result_eq_mc_cost` connects them but requires `all_costs_bounded` —
a sentinel-dependent condition. This sentinel limitation
(documented in CLRS.Ch15.MatrixChain.Review.md) is not exercised by this
test since we validate `mc_result` directly.
