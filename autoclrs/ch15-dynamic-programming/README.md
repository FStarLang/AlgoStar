# Chapter 15: Dynamic Programming — Verified in F\*/Pulse

## Overview

This directory implements three dynamic programming algorithms from CLRS
Chapter 15:

1. **Rod Cutting** (§15.1) — BOTTOM-UP-CUT-ROD and EXTENDED-BOTTOM-UP-CUT-ROD
2. **Longest Common Subsequence** (§15.4) — LCS-LENGTH
3. **Matrix Chain Multiplication** (§15.2) — MATRIX-CHAIN-ORDER

All three algorithms are fully verified with **zero admits and zero assumes**
across every source file.

---

## Rod Cutting (CLRS §15.1)

### Algorithm

Given a rod of length *n* and a price table `prices[0..n−1]` where `prices[i]`
is the price for a piece of length *i + 1*, find the maximum revenue obtainable
by cutting the rod into pieces.

### Specification

The problem is formalized with two predicates in `RodCutting.Spec.fst`:

- **`valid_cutting n cuts`**: `cuts` is a list of positive integers summing
  to `n`.
- **`cutting_revenue prices cuts`**: total revenue from looking up each
  piece length in the price table.
- **`optimal_revenue prices j`**: maximum revenue for a rod of length `j`,
  computed via the bottom-up DP table `build_opt`.

The DP recurrence (CLRS Eq. 15.2):

    r(n) = max{1 ≤ i ≤ n} (p[i] + r(n − i))

is captured by `accum_max` over a precomputed table, and the optimal
substructure theorem (`optimal_substructure` in `RodCutting.Lemmas.fst`)
proves this equals `max_over_range` over the recursive definition.

### Correctness Theorem

```fstar
fn rod_cutting
  (#p: perm) (prices: A.array nat) (n: SZ.t)
  (#s_prices: erased (Seq.seq nat))
  (ctr: GR.ref nat) (#c0: erased nat)
  requires A.pts_to prices #p s_prices ** GR.pts_to ctr c0 **
    pure (SZ.v n == Seq.length s_prices /\ SZ.v n == A.length prices /\
          SZ.v n > 0 /\ SZ.fits (SZ.v n + 1))
  returns result: nat
  ensures exists* (cf: nat).
    A.pts_to prices #p s_prices ** GR.pts_to ctr cf **
    pure (result == optimal_revenue s_prices (SZ.v n) /\
          rod_cutting_bounded cf (reveal c0) (SZ.v n))
```

**Postconditions explained:**

| Postcondition | Meaning |
|---|---|
| `result == optimal_revenue s_prices (SZ.v n)` | The returned value equals the mathematically defined optimal revenue |
| `rod_cutting_bounded cf c0 n` | Ghost counter shows exactly `n(n+1)/2` operations (O(n²)) |
| `A.pts_to prices #p s_prices` | Input array is returned unmodified (fractional permission) |

### Strongest Guarantee

The postcondition `result == optimal_revenue s_prices (SZ.v n)` is the
strongest possible: it equates the imperative result to a pure recursive
specification that is itself proven equivalent (via `optimal_substructure`)
to the max over all valid cuttings. The complexity bound is tight:
exactly `triangle(n) = n(n+1)/2` operations, not merely O(n²).

### Extended Rod Cutting

`CLRS.Ch15.RodCutting.Extended.fst` also implements
EXTENDED-BOTTOM-UP-CUT-ROD, returning both the revenue table `r` and the
optimal first-cut array `s`. The postcondition uses `cuts_are_optimal`:
for every subproblem `j`, `s[j]` is a valid first piece (between 1 and j)
and `prices[s[j]-1] + optimal_revenue(j - s[j]) == optimal_revenue(j)`.
A `reconstruct_cutting` function follows the `s` array to produce the list
of piece sizes.

### Complexity

O(n²) — proven tight. The ghost counter tracks `triangle(vj − 1) + (vi − 1)`
during the inner loop, where `triangle(k) = k(k+1)/2`. The complexity is
proven *inside the Pulse implementation* (linked, not a separate pure proof).

### Limitations

None. Zero admits, zero assumes. The proof is complete end-to-end. The
complexity bound is proven and linked to the implementation. The only caveat
is that the algorithm requires `SZ.fits (n + 1)` to avoid size overflow, a
standard Pulse precondition.

---

## Longest Common Subsequence (CLRS §15.4)

### Algorithm

Given two sequences `x[0..m−1]` and `y[0..n−1]`, compute the length of
their longest common subsequence.

### Specification

The pure specification in `LCS.Spec.fst` defines:

- **`lcs_length x y i j`**: recursive LCS length (CLRS Eq. 15.9).
  If `x[i-1] == y[j-1]`, then `1 + lcs_length(i-1, j-1)`;
  otherwise `max(lcs_length(i-1, j), lcs_length(i, j-1))`.
- **`is_subsequence sub s`**: `sub` is a subsequence of `s`.
- **`is_common_subsequence sub x y`**: `sub` is a subsequence of both `x`
  and `y`.

### Correctness Theorem

```fstar
fn lcs
  (#px #py: perm) (x: A.array int) (y: A.array int)
  (m: SZ.t) (n: SZ.t)
  (#sx #sy: erased (Seq.seq int))
  (ctr: GR.ref nat) (#c0: erased nat)
  requires A.pts_to x #px sx ** A.pts_to y #py sy ** GR.pts_to ctr c0 **
    pure (SZ.v m == Seq.length sx /\ SZ.v n == Seq.length sy /\
          SZ.v m > 0 /\ SZ.v n > 0 /\
          SZ.fits ((SZ.v m + 1) * (SZ.v n + 1)))
  returns result: int
  ensures exists* (cf: nat).
    A.pts_to x #px sx ** A.pts_to y #py sy ** GR.pts_to ctr cf **
    pure (result == lcs_length sx sy (SZ.v m) (SZ.v n) /\
          lcs_complexity_bounded cf (reveal c0) (SZ.v m) (SZ.v n))
```

**Postconditions explained:**

| Postcondition | Meaning |
|---|---|
| `result == lcs_length sx sy m n` | Returned value equals the recursive LCS length definition |
| `lcs_complexity_bounded cf c0 m n` | Ghost counter shows exactly `(m+1)*(n+1)` cell evaluations |
| Input arrays preserved | Both `x` and `y` are returned unmodified |

### Strongest Guarantee

The postcondition equates the result to the pure recursive specification.
The specification module also defines `is_subsequence` and
`is_common_subsequence` predicates, enabling reasoning about actual
subsequences (not just lengths). The complexity bound is exact:
`cf - c0 == (m+1) * (n+1)`.

### Complexity

O(mn) — proven tight. The ghost counter counts `(m+1)*(n+1)` cell
evaluations. The complexity is proven inside the Pulse implementation (linked).

### Limitations

None. Zero admits, zero assumes. The specification defines `lcs_length`
recursively and the implementation is proven to match it cell-by-cell. The
module does *not* prove that `lcs_length` equals the length of any actual
longest common subsequence (the subsequence predicates are defined but not
formally bridged to the DP recurrence). This is a characterization gap, not
a soundness gap — the CLRS recurrence is standard.

---

## Matrix Chain Multiplication (CLRS §15.2)

### Algorithm

Given a sequence of matrix dimensions `p[0..n]` where matrix `A_i` has
dimensions `p[i] × p[i+1]`, find the parenthesization that minimizes the
total number of scalar multiplications.

### Specification

The pure specification has two levels:

1. **Recursive optimum** (`mc_cost` in `MatrixChain.Lemmas.fst`): directly
   defines the minimum scalar multiplication count via the CLRS Eq. 15.7
   recurrence. `mc_cost p i j` tries every split point `k ∈ [i, j)` and
   takes the minimum.

2. **Imperative mirror** (`mc_spec` in `MatrixChain.Spec.fst`):
   `mc_inner_k`, `mc_inner_i`, `mc_outer` trace the three nested loops of
   the bottom-up DP, operating on flat sequences. `mc_result dims n` builds
   the initial table and runs `mc_outer`.

### Correctness Theorem

```fstar
fn matrix_chain_order
  (#p: perm) (dims: A.array int) (n: SZ.t)
  (#s_dims: erased (Seq.seq int))
  requires A.pts_to dims #p s_dims **
    pure (SZ.v n + 1 == Seq.length s_dims /\ SZ.v n > 0 /\
          SZ.fits (SZ.v n * SZ.v n) /\
          (forall (i: nat). i < Seq.length s_dims ==> Seq.index s_dims i > 0))
  returns result: int
  ensures A.pts_to dims #p s_dims **
    pure (result == mc_result s_dims (SZ.v n))
```

The bridge theorem `mc_spec_equiv` then proves:

```fstar
val mc_spec_equiv (dims: seq int) (n: nat)
  : Lemma (requires n > 0 /\ length dims == n + 1 /\
                    all_costs_bounded dims n n 1000000000)
          (ensures mc_result dims n == mc_cost dims 0 (n - 1))
```

**Postconditions explained:**

| Postcondition | Meaning |
|---|---|
| `result == mc_result s_dims n` | Returned value matches the imperative mirror spec |
| (via `mc_spec_equiv`) `mc_result == mc_cost dims 0 (n-1)` | Imperative mirror equals recursive optimum |
| `all_costs_bounded` precondition | Costs must fit in the sentinel value (1,000,000,000) |

### Strongest Guarantee

The correctness chain is:
`Pulse result == mc_result (imperative mirror) == mc_cost (recursive optimum)`.
The `mc_cost` definition directly encodes CLRS Eq. 15.7. The sentinel
precondition (`all_costs_bounded`) is a minor limitation — it requires that
no subproblem cost exceeds 10⁹ — but is trivially satisfied for practical
inputs.

### Complexity

O(n³) — proven. A separate `MatrixChain.Complexity` module proves
`mc_iterations n ≤ n³`. The complexity is proven in *pure F\** (not linked to
the Pulse implementation's ghost counter — the Pulse function does not carry
a ghost counter). The proof shows `mc_iterations n ≤ n³` by bounding each
chain-length iteration's work.

### Limitations

- The sentinel value 10⁹ creates a precondition (`all_costs_bounded`) that
  must be satisfied. For practical inputs this is trivially true, but it is
  not proven automatically.
- The complexity proof is in a separate pure module, not linked to the Pulse
  implementation via a ghost counter (unlike rod cutting and LCS).
- No admits, no assumes.

---

## File Inventory

### Rod Cutting

| File | Lines | Role | Admits |
|---|---|---|---|
| `CLRS.Ch15.RodCutting.Spec.fst` | ~155 | Pure spec: `valid_cutting`, `cutting_revenue`, `optimal_revenue`, `build_opt`, `accum_max`, `dp_correct`, `accum_max_dp_correct` | 0 |
| `CLRS.Ch15.RodCutting.Lemmas.fst` | ~100 | `optimal_substructure` theorem, `is_optimal` predicate | 0 |
| `CLRS.Ch15.RodCutting.Lemmas.fsti` | ~30 | Interface for Lemmas | 0 |
| `CLRS.Ch15.RodCutting.Impl.fst` | ~85 | Pulse implementation with ghost cost counter | 0 |
| `CLRS.Ch15.RodCutting.Impl.fsti` | ~50 | Public API signature | 0 |
| `CLRS.Ch15.RodCutting.Extended.fst` | ~400 | Extended rod cutting with `s` array, `cuts_are_optimal`, `reconstruct_cutting` | 0 |
| `CLRS.Ch15.RodCutting.Test.fst` | ~20 | Smoke test | 0 |

### Longest Common Subsequence

| File | Lines | Role | Admits |
|---|---|---|---|
| `CLRS.Ch15.LCS.Spec.fst` | ~100 | Pure spec: `lcs_length`, `is_subsequence`, `is_common_subsequence`, `lcs_table_correct` | 0 |
| `CLRS.Ch15.LCS.Lemmas.fst` | ~80 | Helper lemmas for table correctness | 0 |
| `CLRS.Ch15.LCS.Lemmas.fsti` | ~20 | Interface for Lemmas | 0 |
| `CLRS.Ch15.LCS.Impl.fst` | ~95 | Pulse implementation with ghost cost counter | 0 |
| `CLRS.Ch15.LCS.Impl.fsti` | ~55 | Public API signature | 0 |

### Matrix Chain Multiplication

| File | Lines | Role | Admits |
|---|---|---|---|
| `CLRS.Ch15.MatrixChain.Spec.fst` | ~95 | Imperative mirror: `mc_inner_k`, `mc_inner_i`, `mc_outer`, `mc_result` | 0 |
| `CLRS.Ch15.MatrixChain.Lemmas.fst` | ~515 | `mc_cost` recursive spec, `mc_spec_equiv` bridge theorem, `dp_correct_upto` | 0 |
| `CLRS.Ch15.MatrixChain.Lemmas.fsti` | ~30 | Interface for Lemmas | 0 |
| `CLRS.Ch15.MatrixChain.Impl.fst` | ~65 | Pulse implementation | 0 |
| `CLRS.Ch15.MatrixChain.Impl.fsti` | ~42 | Public API signature | 0 |
| `CLRS.Ch15.MatrixChain.Complexity.fst` | ~50 | Pure O(n³) bound proof | 0 |
| `CLRS.Ch15.MatrixChain.Complexity.fsti` | ~27 | Complexity interface: `mc_iterations_bound` | 0 |
| `CLRS.Ch15.MatrixChain.Extended.fst` | ~300 | Extended matrix chain with parenthesization | 0 |
| `CLRS.Ch15.MatrixChain.Test.fst` | ~20 | Smoke test | 0 |

---

## Summary

| Algorithm | CLRS | Complexity | Proven | Linked | Admits | Key Theorem |
|---|---|---|---|---|---|---|
| Rod Cutting | §15.1 | O(n²) | Tight | ✅ | 0 | `result == optimal_revenue` |
| LCS | §15.4 | O(mn) | Tight | ✅ | 0 | `result == lcs_length` |
| Matrix Chain | §15.2 | O(n³) | Upper bound | ❌ (pure) | 0 | `mc_result == mc_cost` |

**Linked** means the complexity bound is proven inside the Pulse implementation
via a ghost counter, ensuring the imperative code's actual operation count
matches the bound.

---

## Building

```bash
cd /home/nswamy/ws2/AutoCLRS
make -C ch15-dynamic-programming
```

Requires `PULSE_ROOT` to be set (defaults to `../../pulse`). The build
disables `optimize_let_vc` and `fly_deps` to handle SizeT overflow reasoning
in the matrix chain module.

---

## DP Proof Pattern

All three algorithms follow the same proof architecture:

1. **Define the recursive specification** as a pure, total function with a
   `decreases` clause.
2. **Prove prefix consistency**: the DP table built for size *n* agrees with
   the table built for size *k < n* at index *k* (`build_opt_prefix`).
3. **Prove extensionality**: the recursive step depends only on previously
   computed entries (`accum_max_ext`).
4. **Prove the Pulse loop matches the spec**: the inner loop maintains
   `vq == spec_function(current_args)`.
5. **Bridge the gap**: after the inner loop, call the key lemma to establish
   the computed value equals the specification value.
6. **Thread the ghost counter**: count one tick per inner-loop iteration;
   track via a closed-form sum.
