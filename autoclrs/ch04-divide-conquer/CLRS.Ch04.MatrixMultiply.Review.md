# Matrix Multiply (CLRS §4.2, pp. 75–76)

## Top-Level Signature

Here is the top-level signature proven about Matrix Multiply in
`CLRS.Ch04.MatrixMultiply.Impl.fsti`:

```fstar
fn matrix_multiply
  (#pa #pb: perm)
  (a: array int)
  (b: array int)
  (c: array int)
  (#sa: Ghost.erased (Seq.seq int))
  (#sb: Ghost.erased (Seq.seq int))
  (#sc: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to a #pa sa **
    A.pts_to b #pb sb **
    A.pts_to c sc **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length sa == SZ.v n * SZ.v n /\
      Seq.length sb == SZ.v n * SZ.v n /\
      Seq.length sc == SZ.v n * SZ.v n
    )
  ensures exists* sc' (cf: nat).
    A.pts_to a #pa sa **
    A.pts_to b #pb sb **
    A.pts_to c sc' **
    GR.pts_to ctr cf **
    pure (
      mat_mul_correct sa sb sc' (SZ.v n) /\
      complexity_bounded_cubic cf (reveal c0) (SZ.v n)
    )
```

### Parameters

* `a` and `b` are read-only input arrays (with fractional permissions `#pa`
  and `#pb`), representing `n × n` matrices in row-major flat layout. Ghost
  variables `sa` and `sb` capture their contents.

* `c` is the mutable output array, also `n × n` in row-major layout. Ghost
  variable `sc` captures the initial contents (overwritten by the result).

* `n` is the matrix dimension (both rows and columns), of type `SZ.t`.

* `ctr` is a **ghost counter** for counting multiply-add operations. Initial
  value `c0`.

### Preconditions

* `SZ.v n > 0`: The matrix dimension must be positive.

* `SZ.fits (SZ.v n * SZ.v n)`: The flattened matrix size fits in machine-sized
  integers (no overflow).

* `Seq.length sa == SZ.v n * SZ.v n` (and similarly for `sb`, `sc`): All
  arrays have exactly `n²` elements.

### Postcondition

The `ensures` clause states that there exist a final sequence `sc'` and a
final counter value `cf` such that:

* `mat_mul_correct sa sb sc' (SZ.v n)` — The output matrix is the correct
  product of the input matrices.

* `complexity_bounded_cubic cf (reveal c0) (SZ.v n)` — Exactly `n³`
  multiply-add operations were performed.

## Auxiliary Definitions

### `flat_index` (from `CLRS.Ch04.MatrixMultiply.Spec`)

```fstar
let flat_index (n i j: nat) : nat = i * n + j
```

Row-major index computation for an `n × n` matrix. Element `(i, j)` is stored
at position `i * n + j` in the flat array.

### `dot_product_spec` (from `CLRS.Ch04.MatrixMultiply.Spec`)

```fstar
let rec dot_product_spec (sa sb: Seq.seq int) (n i j: nat) (limit: nat)
  : Tot int (decreases limit)
  = if limit = 0 || i >= n || j >= n || n = 0 then 0
    else if limit > n then dot_product_spec sa sb n i j n
    else let k = limit - 1 in
         if flat_index n i k >= Seq.length sa || flat_index n k j >= Seq.length sb then 0
         else dot_product_spec sa sb n i j (limit - 1) +
              Seq.index sa (flat_index n i k) * Seq.index sb (flat_index n k j)
```

Specification of the dot product: `C[i][j] = Σ_{k=0}^{limit-1} A[i][k] * B[k][j]`.
The `limit` parameter allows expressing partial dot products (used in the
inner loop invariant). Guard conditions (`i >= n`, index out of bounds) return 0.

### `mat_mul_correct` (from `CLRS.Ch04.MatrixMultiply.Spec`)

```fstar
let mat_mul_correct (sa sb sc: Seq.seq int) (n: nat) : prop =
  Seq.length sc == n * n /\
  (forall (i j: nat). i < n /\ j < n ==> 
    Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j n)
```

Full correctness: for every position `(i, j)`, the output `C[i][j]` equals
the complete dot product `Σ_{k=0}^{n-1} A[i][k] * B[k][j]`.

### `mat_mul_partial_k` (from `CLRS.Ch04.MatrixMultiply.Spec`)

```fstar
let mat_mul_partial_k (sa sb sc: Seq.seq int) (n i j k: nat) : prop =
  Seq.length sc == n * n /\ i < n /\ j < n /\ k <= n /\
  Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j k
```

Partial result predicate for the inner loop: position `(i, j)` has accumulated
the dot product up to index `k`.

### `mat_mul_partial_ij` (from `CLRS.Ch04.MatrixMultiply.Spec`)

```fstar
let mat_mul_partial_ij (sa sb sc: Seq.seq int) (n ri cj: nat) : prop =
  Seq.length sc == n * n /\
  (forall (i j: nat). (i < ri \/ (i == ri /\ j < cj)) /\ i < n /\ j < n ==> 
    Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j n)
```

Partial result predicate for the outer loops: all positions in rows `< ri`,
plus positions `(ri, j)` for `j < cj`, have their final correct values.

### `complexity_bounded_cubic` (from `CLRS.Ch04.MatrixMultiply.Spec`)

```fstar
let complexity_bounded_cubic (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n * n * n
```

Exactly `n³` multiply-add operations. This is an **exact** count, not just
an upper bound.

## What Is Proven

The postcondition `mat_mul_correct sa sb sc' n` is the **standard
mathematical definition** of matrix multiplication: every entry of the result
matrix is the dot product of the corresponding row of A and column of B.

The complexity bound `cf - c0 == n³` is **exact** — it proves the naive
triple-loop algorithm performs precisely `n³` multiply-add operations.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Only square matrices.** The implementation and specification only handle
   `n × n` matrices. CLRS's SQUARE-MATRIX-MULTIPLY (pp. 75–76) is also for
   square matrices, so this matches CLRS. However, general matrix
   multiplication (m × p times p × n) is not supported.

2. **`SZ.fits (n * n)` precondition.** The flat layout requires `n²` to fit
   in a machine-sized integer. This limits the matrix dimension on 64-bit
   systems (though the limit is very large in practice).

3. **No initial-value independence for `c`.** The implementation initializes
   `C[i][j] = 0` before the inner loop, so the initial contents `sc` are
   irrelevant. However, the interface accepts arbitrary `sc`, which might
   confuse callers into thinking `c` must be pre-initialized.

4. **Fractional permissions for A and B but not C.** The input matrices use
   fractional permissions (`#pa`, `#pb`), allowing concurrent reading. The
   output matrix `c` uses full permission. This is a good design — noted for
   completeness.

5. **Flat array representation.** The spec uses row-major flat arrays rather
   than nested sequences. This is a practical choice for imperative code but
   differs from the mathematical notation in CLRS (which uses 2D array
   indexing). The `flat_index` function bridges this gap.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Multiply-adds | O(n³) = exactly n³ | ✅ Ghost counter | ✅ Exact (cf − c0 == n³) |

The complexity is **fully linked** and **exact**: the ghost counter `ctr` is
incremented once per multiply-add operation via `tick ctr` in the innermost
loop, and the postcondition asserts `cf - c0 == n * n * n` (equality).

## Proof Structure

The proof uses three nested while loops with invariants:

1. **Outer loop** (rows `i`): Maintains `mat_mul_partial_ij sa sb sc_i n vi 0`
   — all rows before `vi` are complete.

2. **Middle loop** (columns `j`): Maintains
   `mat_mul_partial_ij sa sb sc_ij n vi vj` — within row `vi`, all columns
   before `vj` are complete.

3. **Inner loop** (dot product accumulation `k`): Maintains
   `mat_mul_partial_k sa sb sc_ijk n vi vj vk` — position `(vi, vj)` has
   accumulated the partial dot product up to `k`.

The counter invariant tracks `vc - c0 == vi * n * n + vj * n + vk`, proving
the exact `n³` count.

The `index_bounds_lemma` helper verifies that flat indices are in-bounds:

```fstar
let index_bounds_lemma (n: nat{n > 0}) (i j k: nat) : Lemma
  (requires i < n /\ j < n /\ k < n)
  (ensures flat_index n i k < n * n /\ flat_index n k j < n * n /\ flat_index n i j < n * n)
```

## Files

| File | Role |
|------|------|
| `CLRS.Ch04.MatrixMultiply.Impl.fsti` | Public interface (this signature) |
| `CLRS.Ch04.MatrixMultiply.Impl.fst` | Pulse implementation (triple nested loop) |
| `CLRS.Ch04.MatrixMultiply.Spec.fst` | `flat_index`, `dot_product_spec`, `mat_mul_correct`, complexity predicate |
