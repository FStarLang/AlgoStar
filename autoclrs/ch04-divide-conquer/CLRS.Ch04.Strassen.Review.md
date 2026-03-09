# Strassen's Algorithm (CLRS §4.2, pp. 79–82)

## Top-Level Signature

This is a **pure** (non-imperative) implementation. The main function is in
`CLRS.Ch04.Strassen.Spec.fst`:

```fstar
let rec strassen_multiply (a b:matrix{cols a == rows b /\ is_square a /\ is_square b /\ pow2_size a})
  : Tot (m:matrix{rows m == rows a /\ cols m == cols b /\ is_square m}) (decreases rows a)
```

### Parameters

* `a` and `b` are square matrices of type `matrix` (a sequence of sequences
  of `int`).

### Preconditions (encoded in the refinement type)

* `cols a == rows b`: Matrices are conformable for multiplication.

* `is_square a /\ is_square b`: Both matrices must be square.

* `pow2_size a`: The matrix dimension must be a **power of 2**. This is the
  key restriction of the Strassen implementation.

### Postcondition (encoded in the return type)

The return type guarantees:

* `rows m == rows a /\ cols m == cols b /\ is_square m` — The result has the
  correct dimensions.

Note: Correctness (equality with standard multiply) is proven as a separate
lemma, not in the return type.

## Auxiliary Definitions

### `matrix` type (from `CLRS.Ch04.Strassen.Spec`)

```fstar
type matrix = s:Seq.seq (Seq.seq int){
  Seq.length s > 0 /\
  Seq.length (Seq.index s 0) > 0 /\
  (forall (i:nat). i < Seq.length s ==> 
    Seq.length (Seq.index s i) == Seq.length (Seq.index s 0))
}
```

A matrix is a non-empty sequence of rows, where each row is a non-empty
sequence of `int`, and all rows have the same length. This is a
sequence-of-sequences representation, not a flat array.

### `rows`, `cols`, `get_elem` (from `CLRS.Ch04.Strassen.Spec`)

```fstar
let rows (m:matrix) : pos = Seq.length m
let cols (m:matrix) : pos = Seq.length (Seq.index m 0)
let get_elem (m:matrix) (i:nat{i < rows m}) (j:nat{j < cols m}) : int =
  Seq.index (Seq.index m i) j
```

Standard accessors.

### `is_square`, `is_pow2`, `pow2_size` (from `CLRS.Ch04.Strassen.Spec`)

```fstar
let is_square (m:matrix) : prop = rows m == cols m

let rec is_pow2 (n:pos) : bool =
  if n = 1 then true
  else if n % 2 = 1 then false
  else is_pow2 (n / 2)

let pow2_size (m:matrix{is_square m}) : prop =
  is_pow2 (rows m)
```

The power-of-2 constraint is critical: Strassen recursively halves the
matrix dimension, so it must divide evenly at every level.

### `standard_multiply` (from `CLRS.Ch04.Strassen.Spec`)

```fstar
let standard_multiply (a b:matrix{cols a == rows b}) 
  : m:matrix{rows m == rows a /\ cols m == cols b}
  = let n = rows a in
    let m = cols b in
    let p = cols a in
    Seq.init n (fun i ->
      Seq.init m (fun j ->
        dot_product a b i j p))
```

The naive O(n³) matrix multiplication used as the reference specification.
Strassen is proven to produce the same result.

### `dot_product` (from `CLRS.Ch04.Strassen.Spec`)

```fstar
let rec dot_product (a b:matrix) (i:nat{i < rows a}) (j:nat{j < cols b})
                    (k:nat{k <= cols a /\ k <= rows b})
  : Tot int (decreases k)
  = if k = 0 then 0
    else dot_product a b i j (k-1) + get_elem a i (k-1) * get_elem b (k-1) j
```

Standard dot product on the sequence-of-sequences matrix type. Note this is
a different function from `CLRS.Ch04.MatrixMultiply.Spec.dot_product_spec`
(which operates on flat arrays).

### `submatrix` (from `CLRS.Ch04.Strassen.Spec`)

```fstar
let submatrix (m:matrix)
              (row_start:nat) (row_end:nat{row_start < row_end /\ row_end <= rows m})
              (col_start:nat) (col_end:nat{col_start < col_end /\ col_end <= cols m})
  : sub:matrix{rows sub == row_end - row_start /\ cols sub == col_end - col_start}
```

Extracts a rectangular submatrix. Used to partition into quadrants.

### `assemble_quadrants` (from `CLRS.Ch04.Strassen.Spec`)

```fstar
let assemble_quadrants (c11 c12 c21 c22:matrix)
  : Pure matrix
    (requires rows c11 == rows c12 /\ ... /\ rows c11 == cols c11)
    (ensures fun m -> rows m == 2 * rows c11 /\ cols m == 2 * cols c11)
```

Assembles four `n/2 × n/2` quadrants into an `n × n` matrix.

### `strassen_mult_count` (from `CLRS.Ch04.Strassen.Complexity`)

```fstar
let rec strassen_mult_count (n:pos{is_pow2 n}) : Tot nat =
  if n = 1 then 1
  else 7 * strassen_mult_count (n / 2)
```

The number of scalar multiplications in Strassen's algorithm:
`T(n) = 7·T(n/2)`, `T(1) = 1`. Solves to `T(n) = 7^(log₂ n) = n^(log₂ 7)`.

### `standard_mult_count` (from `CLRS.Ch04.Strassen.Complexity`)

```fstar
let standard_mult_count (n:pos) : nat = n * n * n
```

Standard multiply uses n³ scalar multiplications.

### `pow7` (from `CLRS.Ch04.Strassen.Complexity`)

```fstar
let rec pow7 (n:nat) : Tot pos =
  if n = 0 then 1
  else 7 * pow7 (n - 1)
```

Power-of-7 function. `pow7 k = 7^k`.

### `log2_floor` (from `CLRS.Ch04.Strassen.Complexity`)

```fstar
let rec log2_floor (n:pos) : Tot nat =
  if n = 1 then 0
  else 1 + log2_floor (n / 2)
```

Floor of log base 2. For powers of 2, `pow2(log2_floor n) == n`.

## What Is Proven

### Correctness

The central correctness theorem in `CLRS.Ch04.Strassen.Lemmas`:

```fstar
val lemma_strassen_correct (a b:matrix{cols a == rows b /\ is_square a /\ is_square b /\ pow2_size a})
  : Lemma (ensures (forall (i:nat) (j:nat). i < rows a /\ j < cols b ==>
                    get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j))
```

**Strassen produces the same result as standard multiplication, element by
element.** This is proven by induction on the matrix size, with the inductive
step verifying Strassen's algebraic identities for each of the four quadrants.

### Complexity

```fstar
val lemma_strassen_better_than_cubic (n:pos{is_pow2 n /\ n > 1})
  : Lemma (ensures strassen_mult_count n < standard_mult_count n)
```

**Strassen uses strictly fewer scalar multiplications than standard multiply**
for all power-of-2 sizes `n > 1`.

```fstar
val lemma_strassen_mult_closed_form (n:pos{is_pow2 n})
  : Lemma (ensures (let k = log2_floor n in
                    strassen_mult_count n == pow7 k))
```

**Closed form**: `strassen_mult_count n == 7^(log₂ n) = n^(log₂ 7) ≈ n^2.807`.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Power-of-2 restriction.** The algorithm **only works on matrices whose
   dimension is a power of 2**. The `pow2_size a` precondition is enforced in
   the type. CLRS discusses padding to the next power of 2, but this
   implementation does not include padding. This is a significant practical
   limitation.

2. **Pure, not imperative.** This is a pure functional implementation — no
   mutable arrays, no Pulse code. The complexity analysis counts scalar
   multiplications in a separate recurrence function (`strassen_mult_count`),
   which is **not linked** to the actual implementation via a ghost counter.

3. **Correctness is element-wise, not structural.** The theorem states
   `get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j`
   for all `(i, j)`, which is **full functional correctness**. However, it
   does not prove structural equality (`strassen_multiply a b == standard_multiply a b`)
   because the matrices may have different internal sequence representations.

4. **Complexity counts only scalar multiplications.** The `strassen_mult_count`
   function counts multiplications, not additions. Strassen's advantage is
   specifically in reducing multiplications (7 vs. 8 per recursive step), but
   it increases the number of additions. The total operation count (additions
   + multiplications) is not analyzed.

5. **No comparison with the asymptotic O(n^{lg 7}) bound.** The closed-form
   theorem gives `strassen_mult_count n == 7^(log₂ n)`, and the comparison
   with cubic proves `7^(log₂ n) < n³` for `n > 1`. The asymptotic class
   O(n^{2.807}) is noted in comments but not formally expressed.

6. **Sequence-of-sequences representation.** The matrix is represented as
   `Seq.seq (Seq.seq int)`, not a flat array. This representation makes
   submatrix extraction natural but does not model cache behavior or practical
   performance. The flat-array imperative `MatrixMultiply` uses a different
   representation.

7. **Base case uses standard multiply.** When `n = 1`, Strassen falls through
   to `standard_multiply`. This is correct but means the "7 multiplications"
   recurrence counts the base case as 1 multiplication (a 1×1 product).

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Scalar multiplications | O(n^{lg 7}) = 7^(log₂ n) | ❌ Separate recurrence | ✅ Exact count |
| vs. standard | < n³ for n > 1 | ❌ | Strict inequality |

The complexity is **not linked** to the implementation — `strassen_mult_count`
is a separate pure function. The proof establishes:
1. `strassen_mult_count n == pow7(log2_floor n)` (closed form)
2. `strassen_mult_count n < standard_mult_count n` for `n > 1` (strictly better)

## Proof Structure

### Correctness proof (`CLRS.Ch04.Strassen.Lemmas`)

The main theorem `lemma_strassen_correct` is proven via element-wise
verification. For each element `(i, j)`, `lemma_strassen_elem_correct` does
induction on `rows a`:

* **Base case** (`n = 1`): Both Strassen and standard multiply compute the
  single-element product.

* **Inductive case** (`n > 1`): The element falls in one of four quadrants.
  For each quadrant, the proof:
  1. Applies the induction hypothesis to the 7 recursive Strassen calls.
  2. Uses distributivity lemmas (`lemma_matrix_product_add_left`,
     `lemma_matrix_product_sub_right`, etc.) to expand each product.
  3. Uses `lemma_standard_multiply_quadrant_decomp` to show that the standard
     multiply decomposes as `A_{i1}·B_{1j} + A_{i2}·B_{2j}`.
  4. Verifies the Strassen combination formulas by linear arithmetic
     (e.g., `C11 = P5 + P4 − P2 + P6 = A11·B11 + A12·B21`).

### Complexity proof (`CLRS.Ch04.Strassen.Complexity`)

* `lemma_strassen_mult_closed_form`: By induction, `strassen_mult_count n = 7 * strassen_mult_count(n/2)` unfolds to `7^(log₂ n)`.
* `lemma_strassen_better_than_cubic`: By induction, `7^k < (2^k)³ = 8^k` for `k ≥ 1`.
* `lemma_pow2_log2_inverse`: For powers of 2, `2^(log₂ n) = n`.

## Files

| File | Role |
|------|------|
| `CLRS.Ch04.Strassen.Spec.fst` | Matrix type, operations, standard_multiply, strassen_multiply |
| `CLRS.Ch04.Strassen.Lemmas.fsti` | Correctness lemma signatures |
| `CLRS.Ch04.Strassen.Lemmas.fst` | Correctness proofs (element-wise algebraic verification) |
| `CLRS.Ch04.Strassen.Complexity.fsti` | Complexity interface (strassen_mult_count, bounds) |
| `CLRS.Ch04.Strassen.Complexity.fst` | Complexity proofs (closed form, comparison with cubic) |
