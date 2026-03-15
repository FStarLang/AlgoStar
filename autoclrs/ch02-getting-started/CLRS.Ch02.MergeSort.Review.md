# Merge Sort (CLRS §2.3)

## Top-Level Signature

Here is the top-level signature proven about Merge Sort in
`CLRS.Ch02.MergeSort.Impl.fsti`:

```fstar
val merge_sort
  (a: A.array int)
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  (#s0: erased (Seq.seq int))
  : stt unit
    (A.pts_to a s0 **
     GR.pts_to ctr c0 **
     pure (
       SZ.v len == Seq.length s0 /\ 
       Seq.length s0 <= A.length a))
    (fun _ -> exists* s (cf: nat).
       A.pts_to a s **
       GR.pts_to ctr cf **
       pure (
         Seq.length s == Seq.length s0 /\
         sorted s /\
         permutation s0 s /\
         sort_complexity_bounded cf (reveal c0) 0 (SZ.v len)))
```

There is also a `merge` subroutine exposed in the same interface:

```fstar
val merge
  (a: array int) (lo mid hi: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  (#s1 #s2: Ghost.erased (Seq.seq int))
  : stt unit
    (pts_to_range a (SZ.v lo) (SZ.v mid) s1 **
     pts_to_range a (SZ.v mid) (SZ.v hi) s2 **
     GR.pts_to ctr c0 **
     pure (SZ.v lo <= SZ.v mid /\ SZ.v mid <= SZ.v hi /\ sorted s1 /\ sorted s2))
    (fun _ -> exists* s_out (cf: nat).
       pts_to_range a (SZ.v lo) (SZ.v hi) s_out **
       GR.pts_to ctr cf **
       pure (
         sorted s_out /\ 
         permutation (Seq.append s1 s2) s_out /\
         merge_complexity_bounded cf (reveal c0) (SZ.v lo) (SZ.v hi)))
```

### Parameters

* `a` is a mutable array of `int` (mathematical, unbounded integers in F\*).
  The ghost variable `s0` captures the initial contents of the array.

* `len` is the number of elements to sort, of type `SZ.t` (machine-sized,
  analogous to `size_t` in C).

* `ctr` is a **ghost counter** — a ghost reference to a natural number used to
  count comparisons. The initial value is `c0`. Ghost values are erased at
  runtime; they exist only for specification and proof.

### Preconditions

* `SZ.v len == Seq.length s0`: The length parameter matches the logical
  sequence length.

* `Seq.length s0 <= A.length a`: The logical sequence fits within the physical
  array length, matching insertion sort's style. (Since `A.pts_to a s0`
  implies `Seq.length s0 == A.length a`, this is always satisfied.)

### Postcondition

The `ensures` clause states that there exist a final sequence `s` and a final
counter value `cf` such that:

* `Seq.length s == Seq.length s0` — The output has the same length as the input.

* `sorted s` — The output is sorted.

* `permutation s0 s` — The output is a permutation of the input.

* `sort_complexity_bounded cf (reveal c0) 0 (SZ.v len)` — The number of
  comparisons is bounded by `ms_cost(len)`.

## Auxiliary Definitions

### `sorted` (from `CLRS.Common.SortSpec`)

```fstar
let sorted (s: Seq.seq int) : prop
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j
```

Standard all-pairs sorted definition: for all indices `i ≤ j`, the element at
`i` is less than or equal to the element at `j`.

### `permutation` (from `CLRS.Common.SortSpec`)

```fstar
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)
```

Wraps F\*'s standard library notion of permutation. The `opaque_to_smt`
attribute prevents the SMT solver from unfolding the definition; the proofs
use explicit permutation lemmas instead.

### `sort_complexity_bounded` (from `CLRS.Ch02.MergeSort.Spec`)

```fstar
let sort_complexity_bounded (cf c0: nat) (lo hi: nat) : prop =
  lo <= hi /\ cf >= c0 /\ cf - c0 <= ms_cost (hi - lo)
```

This says the number of comparisons (`cf - c0`) is at most `ms_cost(n)` where
`n = hi - lo`.

### `ms_cost` (from `CLRS.Ch02.MergeSort.Spec`)

```fstar
let ms_cost (len: int) : nat = if len <= 0 then 0 else merge_sort_ops len
```

Bridges to `merge_sort_ops` from the Complexity module. For trivial inputs
(`len ≤ 0`), cost is zero.

### `merge_sort_ops` (from `CLRS.Ch02.MergeSort.Complexity`)

```fstar
let rec merge_sort_ops (n: pos) : Tot nat (decreases n)
  = if n = 1 then 0
    else 2 * merge_sort_ops (ceil_div2 n) + n
```

This is the standard merge sort recurrence: `T(n) = 2·T(⌈n/2⌉) + n` for
`n > 1`, and `T(1) = 0`. The `+n` term accounts for the merge step.

### `merge_sort_bound` (from `CLRS.Ch02.MergeSort.Complexity`)

```fstar
let merge_sort_bound (n: pos) : nat = 4 * n * log2_ceil n + 4 * n
```

The closed-form upper bound proven in `merge_sort_is_n_log_n`:

```fstar
val merge_sort_is_n_log_n (n: pos)
  : Lemma (ensures merge_sort_ops n <= merge_sort_bound n)
```

This establishes that `merge_sort_ops n ≤ 4n⌈log₂ n⌉ + 4n`, i.e., O(n log n).

### `merge_complexity_bounded` (from `CLRS.Ch02.MergeSort.Spec`)

```fstar
let merge_complexity_bounded (cf c0: nat) (lo hi: nat) : prop =
  lo <= hi /\ cf >= c0 /\ cf - c0 <= hi - lo
```

The merge subroutine uses at most `hi - lo` comparisons (linear in the number
of elements merged).

### `seq_merge` (from `CLRS.Ch02.MergeSort.Spec`)

```fstar
let rec seq_merge (s1 s2: Seq.seq int) 
  : Tot (Seq.seq int) (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then s2
    else if Seq.length s2 = 0 then s1
    else let h1 = Seq.head s1 in
         let h2 = Seq.head s2 in
         if h1 <= h2 
         then Seq.cons h1 (seq_merge (Seq.tail s1) s2)
         else Seq.cons h2 (seq_merge s1 (Seq.tail s2))
```

Pure recursive merge of two sorted sequences. The imperative merge loop is
proven to produce the same result as this pure specification, which is then
shown to be sorted and a permutation of the concatenation of the two inputs.

### `all_ge` (from `CLRS.Ch02.MergeSort.Spec`)

```fstar
let all_ge (v: int) (s: Seq.seq int) : prop =
  forall (i: nat). i < Seq.length s ==> v <= Seq.index s i
```

Predicate stating all elements of `s` are ≥ `v`. Used internally in the
proof that `seq_merge` preserves sortedness.

## What Is Proven

The postcondition `sorted s /\ permutation s0 s` is the **strongest possible
functional correctness specification** for an in-place sorting algorithm: the
output is both sorted and a rearrangement of the input.

The complexity bound chains through two levels:

1. `sort_complexity_bounded` bounds comparisons by `merge_sort_ops(n)` (the
   exact recurrence).
2. `merge_sort_is_n_log_n` bounds `merge_sort_ops(n) ≤ 4n⌈log₂ n⌉ + 4n`,
   establishing O(n log n).

The merge subroutine is independently specified: it takes two sorted
sub-ranges, produces a single sorted range that is a permutation of their
concatenation, and uses at most `hi - lo` comparisons.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **~~`len == A.length a` precondition.~~** *(Addressed.)* The precondition now
   uses `Seq.length s0 <= A.length a`, matching insertion sort's style. Since
   `A.pts_to a s0` implies `Seq.length s0 == A.length a`, this is semantically
   equivalent but removes the redundant explicit constraint.

2. **Complexity constant is loose.** The closed-form bound
   `4n⌈log₂ n⌉ + 4n` is a deliberate overestimate. The actual merge sort
   typically uses ≈ `n⌈log₂ n⌉` comparisons. The constant 4 simplifies the
   formal proof but inflates the stated bound.

3. **Only upper bound, not tight.** The specification proves
   `cf - c0 ≤ merge_sort_ops(n)` (and `merge_sort_ops(n) ≤ 4n log n + 4n`),
   not that the count is exactly `merge_sort_ops(n)`. The actual count depends
   on the input.

4. **`len = 0` handled but trivially.** When `len ≤ 1`, the implementation
   returns immediately using `singl_sorted` and `permutation_refl`. This is
   correct but not exercised by the recurrence.

5. **Heap allocation in merge.** The merge subroutine allocates temporary
   vectors (`V.alloc`) for the left and right halves, which are freed after
   merging. This is an O(n) space overhead per merge call. CLRS describes
   the same approach, but the specification does not bound memory usage.

6. **Recurrence uses ⌈n/2⌉, implementation uses ⌊n/2⌋.** The recurrence
   `T(n) = 2·T(⌈n/2⌉) + n` slightly overestimates the left-half cost.
   The implementation splits at `⌊n/2⌋` (left half) and `n - ⌊n/2⌋` (right
   half). The `merge_sort_ops_split` lemma bridges this gap by proving
   `T(⌊n/2⌋) + T(n - ⌊n/2⌋) + n ≤ T(n)`.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Comparisons | O(n log n) = 4n⌈log₂ n⌉ + 4n | ✅ Ghost counter | Upper bound only |
| Merge comparisons | O(n) = hi − lo | ✅ Ghost counter | Upper bound only |

The complexity is **fully linked** to the imperative implementation: the ghost
counter `ctr` is incremented inside the merge loop on each comparison (via
`tick ctr`), and the postcondition directly constrains `cf - c0`.

## Proof Structure

The proof is structured in two layers:

1. **Merge**: A loop that writes `seq_merge s1 s2` into the array. The loop
   invariant maintains that the first `k` positions match the ghost target
   `seq_merge s1 s2`, while the remaining suffix is tracked via
   `suffix_step_left` / `suffix_step_right` lemmas.

2. **Recursive sort** (`merge_sort_aux`): Splits the range at the midpoint,
   recursively sorts both halves, then merges. The complexity invariant uses
   `ms_cost_split` to show that the cost of sorting both halves plus merging
   fits within `ms_cost(n)`. The `append_permutations` lemma composes the
   permutation witnesses from the two recursive calls.

Key lemmas in `CLRS.Ch02.MergeSort.Lemmas`:

* `seq_merge_sorted`: Merging two sorted sequences yields a sorted sequence.
* `seq_merge_permutation`: The merge result is a permutation of `append s1 s2`.
* `suffix_step_left` / `suffix_step_right`: Step the suffix invariant.
* `ms_cost_split`: `T(⌊n/2⌋) + T(n - ⌊n/2⌋) + n ≤ T(n)`.

## Files

| File | Role |
|------|------|
| `CLRS.Ch02.MergeSort.Impl.fsti` | Public interface (merge + merge_sort signatures) |
| `CLRS.Ch02.MergeSort.Impl.fst` | Pulse implementation (merge loop + recursive sort) |
| `CLRS.Ch02.MergeSort.Spec.fst` | `seq_merge`, `all_ge`, `ms_cost`, complexity predicates |
| `CLRS.Ch02.MergeSort.Complexity.fsti` | Complexity interface (`merge_sort_ops`, `merge_sort_bound`) |
| `CLRS.Ch02.MergeSort.Complexity.fst` | Complexity proofs (recurrence, O(n log n) bound, monotonicity) |
| `CLRS.Ch02.MergeSort.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch02.MergeSort.Lemmas.fst` | Lemma proofs (merge correctness, suffix stepping) |
| `CLRS.Common.SortSpec.fst` | `sorted`, `permutation` definitions |
