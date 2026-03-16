# CLRS Chapter 4: Divide and Conquer

Verified implementations of divide-and-conquer algorithms from CLRS Chapter 4,
covering binary search, the maximum subarray problem (Kadane's O(n) and the
classic D&C O(n lg n)), standard matrix multiplication (O(n³) in Pulse), and
Strassen's algorithm (pure F*, O(n^{lg 7})). All proofs are mechanically checked
by F\* and Pulse. **ZERO admits. ZERO assumes.**

## Algorithms

### 1. Binary Search (CLRS §4, Exercise 2.3-5)

**Specification.** The `is_sorted` predicate and the `complexity_bounded_log`
bound are defined in the pure Spec module:

```fstar
let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let complexity_bounded_log (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= log2f n + 1
```

**Correctness Theorem.** The exact `Impl.fsti` signature:

```fstar
val binary_search
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (key: int)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  : stt SZ.t
    (A.pts_to a #p s0 ** GR.pts_to ctr c0 **
     pure (
       SZ.v len == Seq.length s0 /\
       Seq.length s0 <= A.length a /\
       is_sorted s0
     ))
    (fun result -> exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
     pure (
       SZ.v result <= SZ.v len /\
       (SZ.v result < SZ.v len ==> (
         SZ.v result < Seq.length s0 /\
         Seq.index s0 (SZ.v result) == key
       )) /\
       (SZ.v result == SZ.v len ==> (
         forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= key
       )) /\
       complexity_bounded_log cf (reveal c0) (SZ.v len)
     ))
```

Postcondition conjuncts:

| Conjunct | Meaning |
|----------|---------|
| `SZ.v result <= SZ.v len` | Result is a valid index or the sentinel `len` |
| `result < len ==> s0[result] == key` | If found, the element at that index equals the key |
| `result == len ==> ∀i. s0[i] ≠ key` | If not found, the key is absent from the entire array |
| `complexity_bounded_log cf c0 len` | At most ⌊log₂ n⌋ + 1 comparisons (O(lg n)), linked to ghost counter |

**Strongest Guarantee.** The postcondition is the strongest functional guarantee:
it gives an exact index when found and a universal absence proof when not found.
The complexity bound of ⌊log₂ n⌋ + 1 is tight (worst case is exactly that many
comparisons).

**Limitations.** The array must be sorted (precondition). The bound is worst-case;
best case (key at midpoint) is 1 comparison, but this is not tracked. The
implementation uses a found-flag pattern because Pulse `while` loops cannot
return values directly — this adds a boolean check per iteration but does not
affect the asymptotic bound.

**Complexity.** O(lg n) proven via a ghost counter linked to the imperative
implementation. The loop invariant tracks a *budget*:
`comparisons_used + log2f(remaining_range) <= log2f(n)`. Each iteration
consumes one comparison and halves the range, so `log2f` decreases by at
least 1. The `lemma_log2f_step` lemma formalizes this halving step.

### 2. Maximum Subarray — Kadane's Algorithm (CLRS §4.1, Exercise)

**Specification.** The shared `Spec` module defines the Kadane recurrence and
the canonical `max_subarray_spec`:

```fstar
let rec kadane_spec (s: Seq.seq int) (i: nat) (current_sum: int) (best_sum: int)
  : Pure int (requires i <= Seq.length s) (ensures fun _ -> True)
  = if i >= Seq.length s then best_sum
    else let elem = Seq.index s i in
         let new_current = max_int elem (current_sum + elem) in
         let new_best = max_int best_sum new_current in
         kadane_spec s (i + 1) new_current new_best

let max_subarray_spec (s: Seq.seq int) : Tot int =
  if Seq.length s = 0 then 0
  else kadane_spec s 0 0 (Seq.index s 0)
```

**Correctness Theorem.** The exact `Kadane.fsti` signature:

```fstar
val max_subarray
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  : stt int
    (A.pts_to a #p s0 ** GR.pts_to ctr c0 **
     pure (
       SZ.v len == Seq.length s0 /\
       Seq.length s0 <= A.length a /\
       SZ.v len > 0
     ))
    (fun result -> exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf ** pure (
       result == max_subarray_spec s0 /\
       complexity_bounded_linear cf (reveal c0) (SZ.v len)
     ))
```

Postcondition conjuncts:

| Conjunct | Meaning |
|----------|---------|
| `result == max_subarray_spec s0` | Result exactly equals the pure Kadane specification |
| `complexity_bounded_linear cf c0 len` | Exactly n operations (Θ(n), linked to ghost counter) |

**Strongest Guarantee.** The result is proven equal to the pure specification,
which the Lemmas module proves optimal: `theorem_kadane_optimal` shows
`max_subarray_spec s >= sum_range s i j` for all subarrays `[i,j)`, and
`theorem_kadane_witness` shows the max is achieved by some subarray.

**Limitations.** The specification uses `Seq.index s 0` (the first element) as
the initial `best_sum`. The optimality theorems hold unconditionally for any
integer sequence — no bounded-element precondition is needed.

**Complexity.** Exactly n operations, linked to ghost counter. The loop invariant
tracks `vc == c0 + i`; at exit `i == n` gives `cf - c0 == n`.

### 3. Maximum Subarray — Divide & Conquer (CLRS §4.1)

**This is a pure F\* implementation, NOT Pulse.**

**Specification.** `find_maximum_subarray_dc` follows CLRS exactly — split at
midpoint, recurse on both halves, find crossing subarray, return the maximum
of the three.

**Correctness.** Two key theorems:
- `lemma_dc_sum_correct`: the returned range `[left, right)` has the claimed sum.
- `lemma_dc_optimal`: for any subarray `[qi, qj)`, the D&C result is ≥ `sum_range s qi qj`.

**Equivalence (Proven).** `dc_kadane_equivalence` proves that the D&C result
equals `max_subarray_spec` (Kadane's answer) for non-empty arrays. This
is the strongest possible result: both algorithms compute the
*unique* maximum subarray sum.

**Complexity.** The pure cost function `dc_ops_count` models T(n) = 2T(n/2) + n,
T(1) = 1. The bound `T(n) ≤ 4n(⌈log₂ n⌉ + 1)` is proven by induction
(`lemma_dc_complexity_bound`). **This is a pure recurrence analysis, NOT linked
to an imperative ghost counter** — there is no Pulse implementation of the D&C
variant.

**Limitations.** The complexity is O(n log n) — worse than Kadane's O(n). CLRS
presents this as the motivating example for the Master Theorem. The cost function
counts recursive calls + linear work per level but is not linked to any
imperative execution.

### 4. Standard Matrix Multiply (CLRS §4.2)

**Specification.** Matrices are stored as flat row-major arrays. The spec defines:

```fstar
let flat_index (n i j: nat) : nat = i * n + j

let mat_mul_correct (sa sb sc: Seq.seq int) (n: nat) : prop =
  Seq.length sc == n * n /\
  (forall (i j: nat). i < n /\ j < n ==>
    Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j n)

let complexity_bounded_cubic (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n * n * n
```

**Correctness Theorem.** The Pulse `matrix_multiply` function (in `Impl.fsti`)
ensures `mat_mul_correct sa sb sc' n /\ complexity_bounded_cubic cf c0 n`.

**Strongest Guarantee.** Every output element equals the exact dot product sum.
The complexity bound is tight: exactly n³ multiply-add operations.

**Limitations.** Only square n×n matrices are supported. The precondition
`SZ.fits (n * n)` limits matrix sizes to what fits in `SizeT`. Integer overflow
in element values is not addressed (F\* `int` is mathematical integers).

**Complexity.** Exactly n³ operations, linked via ghost counter. The three-level
invariant tracks `vc - c0 == vi * n² + vj * n + vk`.

### 5. Strassen's Algorithm (CLRS §4.2)

**This is a pure F\* implementation, NOT Pulse.**

**Specification.** Uses a sequence-of-sequences matrix representation. The
`strassen_multiply` function requires square, power-of-2 (`is_pow2`) matrices.

**Correctness.** `lemma_strassen_correct` (in `Strassen.Lemmas`) proves
element-wise equality with `standard_multiply`:

```fstar
val lemma_strassen_correct (a b:matrix{cols a == rows b /\ is_square a /\ is_square b /\ pow2_size a})
  : Lemma (ensures (forall (i:nat) (j:nat). i < rows a /\ j < cols b ==>
                    get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j))
```

**Complexity.** `strassen_mult_count n` counts scalar multiplications (T(n) = 7T(n/2), T(1) = 1).
Two key results:
- `lemma_strassen_better_than_cubic`: for n > 1, `strassen_mult_count n < n³`.
- `lemma_strassen_mult_closed_form`: `strassen_mult_count n == pow7 (log2_floor n)` = 7^{log₂ n} = n^{lg 7}.

**Limitations.**
- **Power-of-2 only**: the `pow2_size` precondition restricts input to 2^k × 2^k
  matrices. CLRS handles arbitrary sizes by padding; we do not.
- **No imperative version**: Strassen is pure F\* only. There is no Pulse implementation
  and no ghost-counter-linked complexity.
- **Counts multiplications only**: the Θ(n²) additions per recursion level are not
  counted. This matches CLRS's focus on the multiplication recurrence.
- **No comparison with standard multiply's ghost counter**: the Pulse O(n³) and the
  pure O(n^{lg 7}) use different formalisms and cannot be directly compared in the proof.

## File Inventory

| File | Role | Language |
|------|------|---------|
| `CLRS.Ch04.BinarySearch.Spec.fst` | Pure spec: `is_sorted`, `log2f`, `complexity_bounded_log` | F\* |
| `CLRS.Ch04.BinarySearch.Lemmas.fsti` | Lemma interface: `log2f` monotonicity, halving step | F\* |
| `CLRS.Ch04.BinarySearch.Lemmas.fst` | Lemma proofs | F\* |
| `CLRS.Ch04.BinarySearch.Impl.fsti` | Public interface for `binary_search` | Pulse |
| `CLRS.Ch04.BinarySearch.Impl.fst` | Imperative binary search with ghost counter | Pulse |
| `CLRS.Ch04.MaxSubarray.Spec.fst` | Shared spec: `kadane_spec`, `max_subarray_spec`, `sum_range`, `max_suffix_sum`, `max_sub_sum` | F\* |
| `CLRS.Ch04.MaxSubarray.Lemmas.fsti` | Lemma interface: Kadane correctness, optimality, witnesses | F\* |
| `CLRS.Ch04.MaxSubarray.Lemmas.fst` | Lemma proofs | F\* |
| `CLRS.Ch04.MaxSubarray.Kadane.fsti` | Public interface for Kadane's `max_subarray` | Pulse |
| `CLRS.Ch04.MaxSubarray.Kadane.fst` | Imperative Kadane with ghost counter | Pulse |
| `CLRS.Ch04.MaxSubarray.DivideConquer.fst` | Pure D&C implementation + correctness + equivalence | F\* |
| `CLRS.Ch04.MaxSubarray.DivideConquer.Lemmas.fsti` | D&C lemma interface | F\* |
| `CLRS.Ch04.MaxSubarray.DivideConquer.Lemmas.fst` | D&C optimality proofs + equivalence proof | F\* |
| `CLRS.Ch04.MaxSubarray.DivideConquer.Complexity.fsti` | D&C complexity interface | F\* |
| `CLRS.Ch04.MaxSubarray.DivideConquer.Complexity.fst` | D&C cost function + O(n log n) bound | F\* |
| `CLRS.Ch04.MatrixMultiply.Spec.fst` | Pure spec: `flat_index`, `dot_product_spec`, `mat_mul_correct`, `complexity_bounded_cubic` | F\* |
| `CLRS.Ch04.MatrixMultiply.Impl.fsti` | Public interface for `matrix_multiply` | Pulse |
| `CLRS.Ch04.MatrixMultiply.Impl.fst` | Imperative matrix multiply with ghost counter | Pulse |
| `CLRS.Ch04.Strassen.Spec.fst` | Pure spec: `matrix` type, `standard_multiply`, `strassen_multiply` | F\* |
| `CLRS.Ch04.Strassen.Lemmas.fsti` | Strassen correctness lemma interface | F\* |
| `CLRS.Ch04.Strassen.Lemmas.fst` | Strassen element-wise correctness proof | F\* |
| `CLRS.Ch04.Strassen.Complexity.fsti` | Strassen complexity interface | F\* |
| `CLRS.Ch04.Strassen.Complexity.fst` | `strassen_mult_count`, closed form, cubic comparison | F\* |
| `Test.BinarySearch.fst` | Executable test for binary search | F\* |
| `Test.MaxSubarray.fst` | Executable test for max subarray | F\* |

## Summary

| Algorithm | CLRS Section | Style | Correctness | Complexity | Linked? | Admits |
|-----------|-------------|-------|-------------|-----------|---------|--------|
| Binary Search | §4 (Ex. 2.3-5) | Pulse | Found ⟹ match, ¬found ⟹ absent | O(lg n): ≤ ⌊log₂ n⌋ + 1 | Yes (ghost ctr) | 0 |
| Kadane | §4.1 (Exercise) | Pulse | `result == max_subarray_spec s0` | Θ(n): exactly n ops | Yes (ghost ctr) | 0 |
| D&C Max Subarray | §4.1 | Pure F\* | Optimal + sum correct | O(n log n): ≤ 4n(⌈log₂ n⌉+1) | No (pure) | 0 |
| D&C ≡ Kadane | §4.1 | Pure F\* | `dc_kadane_equivalence` | — | — | 0 |
| Matrix Multiply | §4.2 | Pulse | `mat_mul_correct` (∀ i,j dot product) | Θ(n³): exactly n³ ops | Yes (ghost ctr) | 0 |
| Strassen | §4.2 | Pure F\* | Element-wise == `standard_multiply` | O(n^{lg 7}): 7^{log₂ n} mults | No (pure) | 0 |

## Building

```bash
cd ch04-divide-conquer && make
```
