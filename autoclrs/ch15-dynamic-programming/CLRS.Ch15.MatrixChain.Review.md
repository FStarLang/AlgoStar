# Matrix Chain Multiplication (CLRS §15.2)

## Top-Level Signature

Here is the top-level signature proven about Matrix Chain Multiplication in
`CLRS.Ch15.MatrixChain.Impl.fsti`:

```fstar
fn matrix_chain_order
  (#p: perm)
  (dims: A.array int)
  (n: SZ.t)
  (#s_dims: erased (Seq.seq int))
  requires
    A.pts_to dims #p s_dims **
    pure (
      SZ.v n + 1 == Seq.length s_dims /\
      SZ.v n + 1 == A.length dims /\
      SZ.v n > 0 /\
      SZ.fits (op_Multiply (SZ.v n) (SZ.v n)) /\
      (forall (i: nat). i < Seq.length s_dims ==> Seq.index s_dims i > 0)
    )
  returns result: int
  ensures
    A.pts_to dims #p s_dims **
    pure (
      result == mc_result s_dims (SZ.v n)
    )
```

### Parameters

* `dims` is a read-only array of `int` containing dimension values
  `p[0..n]` for `n` matrices, where matrix `i` has dimensions
  `p[i] × p[i+1]`.

* `n` is the number of matrices, of type `SZ.t`.

### Preconditions

* `SZ.v n + 1 == Seq.length s_dims`: The dimension array has `n+1` entries.

* `SZ.v n > 0`: At least one matrix.

* `SZ.fits (op_Multiply (SZ.v n) (SZ.v n))`: The `n×n` DP table fits in
  machine integers.

* `forall i. Seq.index s_dims i > 0`: All dimensions are positive.

### Postcondition

* `result == mc_result s_dims (SZ.v n)` — The result equals the pure
  specification's computation of optimal scalar multiplication count.

## Auxiliary Definitions

### `mc_result` (from `CLRS.Ch15.MatrixChain.Spec`)

```fstar
let mc_result (dims: seq int) (n: nat) : int =
  if n = 0 || length dims <> n + 1 then 0
  else begin
    let table = create (n * n) 0 in
    let final_table = mc_outer table dims n 2 in
    lemma_mc_outer_len table dims n 2;
    assert (length final_table == n * n);
    index final_table (n - 1)
  end
```

This is an **imperative mirror specification**: it mirrors the three nested
loops of CLRS's MATRIX-CHAIN-ORDER as pure recursive functions
(`mc_inner_k`, `mc_inner_i`, `mc_outer`). The Pulse implementation's
correctness is proven by showing its state matches this pure computation at
each step.

### `mc_inner_k`, `mc_inner_i`, `mc_outer` (from `CLRS.Ch15.MatrixChain.Spec`)

```fstar
let rec mc_inner_k (table: seq int) (dims: seq int) (n i j k: nat) (min_acc: int)
  : Tot int (decreases (j - k))
  = if k >= j || i >= n || j >= n || length table <> n * n || length dims <> n + 1 then min_acc
    else
      let cost_ik = index table (i * n + k) in
      let cost_k1j = index table ((k + 1) * n + j) in
      let dim_i = index dims i in
      let dim_k1 = index dims (k + 1) in
      let dim_j1 = index dims (j + 1) in
      let q = cost_ik + cost_k1j + dim_i * dim_k1 * dim_j1 in
      let new_min = if q < min_acc then q else min_acc in
      mc_inner_k table dims n i j (k + 1) new_min
```

These mirror the three nested loops: `mc_outer` iterates chain lengths
`l = 2..n`, `mc_inner_i` iterates starting positions, and `mc_inner_k`
iterates split points.

### `mc_cost` (from `CLRS.Ch15.MatrixChain.Lemmas`)

```fstar
val mc_cost (p: seq int) (i j: nat) : Tot int
```

The recursive optimal cost function (CLRS Eq. 15.7):
`mc_cost(p, i, i) = 0` and `mc_cost(p, i, j) = min_{i≤k<j}(mc_cost(i,k) + mc_cost(k+1,j) + p[i]·p[k+1]·p[j+1])`.

### `paren` and `paren_cost` (from `CLRS.Ch15.MatrixChain.Lemmas`)

```fstar
noeq
type paren : nat -> nat -> Type =
  | PLeaf : (i:nat) -> paren i i
  | PSplit : #i:nat -> #j:nat{j > i} -> (k:nat{k >= i /\ k < j})
             -> paren i k -> paren (k+1) j -> paren i j

val paren_cost (p: seq int) (#i #j: nat) (t: paren i j) : Tot int
```

A parenthesization is an inductive tree of split decisions. `paren_cost`
computes the scalar multiplication count for a given parenthesization.

## What Is Proven

**Imperative correctness.** The Pulse implementation is proven to return
`mc_result s_dims n`, which is the result of the imperative mirror spec.
The proof uses a "remaining-work" invariant: after processing chain length
`l`, the remaining computation from the current table state equals the
total computation from the initial state.

**DP correctness.** The Lemmas module proves:

* **`mc_spec_equiv`**: `mc_result dims n == mc_cost dims 0 (n-1)` — the
  bottom-up DP result equals the recursive optimum, under a cost boundedness
  assumption (`all_costs_bounded dims n n 1000000000`).

* **Upper bound** (`mc_cost_le_paren_cost`): For any parenthesization `t`,
  `mc_cost p i j ≤ paren_cost p t`.

* **Achievability** (`optimal_paren`): There exists a parenthesization
  whose cost equals `mc_cost`.

Together, these establish that `mc_cost` is the minimum over all
parenthesizations.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Sentinel value `1000000000`.** The inner loop initializes `min_cost`
   to `1000000000` instead of `INT_MAX` or a proper infinity. The lemma
   `mc_spec_equiv` requires `all_costs_bounded dims n n 1000000000` as a
   precondition. This is discharged by `discharge_all_costs_bounded`, which
   requires all dimensions to be bounded by some `d` with
   `(n-1)·d³ ≤ 1000000000`. This is a **real limitation**: for large
   dimensions or long chains, the sentinel may be too small. The
   postcondition on the `.fsti` does NOT include this bound — the interface
   is stated in terms of `mc_result`, which bakes in the sentinel. If the
   sentinel is exceeded, `mc_result` may not equal the true optimum.

2. **Imperative mirror spec, not enumerative.** The top-level postcondition
   is `result == mc_result`, where `mc_result` is defined by replaying the
   loops. The connection to the enumerative optimum `mc_cost` is proven in
   `Lemmas.fst` but only under the sentinel bound.

3. **0-indexed matrices.** CLRS uses 1-indexed matrices `A₁..Aₙ` with
   dimension array `p[0..n]`. This implementation uses 0-indexed matrices
   `A₀..Aₙ₋₁` with the same dimension array. The DP table stores
   `m[i][j]` for `0 ≤ i,j < n` in a flat array of size `n²`.

4. **No complexity ghost counter in the Pulse code.** Unlike Rod Cutting
   and LCS, the Pulse implementation does NOT carry a ghost tick counter.
   The O(n³) complexity bound is proven separately in
   `CLRS.Ch15.MatrixChain.Complexity`, but it is proven on the pure loop
   model, not directly linked to the imperative code.

5. **Extended variant has weaker split correctness.** The extended variant
   (`CLRS.Ch15.MatrixChain.Extended`) returns a split-point table and
   proves `cost == mc_result`, but the split-point table's correctness is
   documented as "not fully formally verified for split correctness."

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Inner-loop iterations | O(n³) ≤ n³ | ⚠️ Pure model only | Upper bound |

From `CLRS.Ch15.MatrixChain.Complexity`:

```fstar
val mc_iterations_bound (n: nat)
  : Lemma (ensures mc_iterations n <= n * n * n)
```

The exact count is `Σ_{l=2}^{n} (n-l+1)(l-1) = (n³-n)/6`, but only the
`≤ n³` upper bound is formally proven. The bound is proven on the pure
`mc_inner_sum` function, not directly linked to the Pulse implementation
via a ghost counter.

## Proof Structure

The Pulse proof uses a three-level "remaining-work" invariant:

* **Outer loop**: `mc_outer sm s_dims n vl == mc_outer (create (n*n) 0) s_dims n 2`
  — the remaining outer-loop computation from the current state equals the
  total computation.

* **Middle loop**: `mc_outer (mc_inner_i sm_i s_dims n vl vi) s_dims n (vl+1) == ...`
  — remaining i-work then remaining l-work equals total.

* **Inner loop**: `mc_inner_k sm_k s_dims n vi vj vk vmin_cost == mc_inner_k sm_k s_dims n vi vj vi 1000000000`
  — the k-loop accumulator tracks the remaining k-work.

## Files

| File | Role |
|------|------|
| `CLRS.Ch15.MatrixChain.Impl.fsti` | Public interface |
| `CLRS.Ch15.MatrixChain.Impl.fst` | Pulse implementation |
| `CLRS.Ch15.MatrixChain.Spec.fst` | `mc_result`, `mc_inner_k`, `mc_inner_i`, `mc_outer` |
| `CLRS.Ch15.MatrixChain.Lemmas.fsti` | Lemma signatures (`mc_cost`, `paren`, optimality) |
| `CLRS.Ch15.MatrixChain.Lemmas.fst` | Lemma proofs |
| `CLRS.Ch15.MatrixChain.Complexity.fsti` | Complexity interface (`mc_iterations ≤ n³`) |
| `CLRS.Ch15.MatrixChain.Complexity.fst` | Complexity proofs |
| `CLRS.Ch15.MatrixChain.Extended.fst` | Extended variant with split-point table |
| `CLRS.Ch15.MatrixChain.Test.fst` | Test cases |
