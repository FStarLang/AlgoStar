# Linear-Time Sorting in Pulse (CLRS Chapter 8)

This directory contains formally verified implementations of the three
linear-time sorting algorithms from CLRS Chapter 8: **Counting Sort** (§8.2),
**Radix Sort** (§8.3), and **Bucket Sort** (§8.4). These algorithms bypass
the Ω(n log n) comparison-based lower bound by exploiting key structure.

**All proofs are complete with zero admits, zero assumes, and zero assume_ calls.**

## Summary Table

| Algorithm | CLRS | Implementation | Postcondition | Complexity | Admits |
|-----------|------|----------------|---------------|------------|--------|
| Counting Sort (CLRS-style) | §8.2 | Pulse (`Impl.fst`) | `sorted ∧ permutation` | Θ(n+k) implicit | 0 |
| Counting Sort (in-place) | §8.2 | Pulse (`Impl.fst`) | `sorted ∧ permutation` | Θ(n+k) implicit | 0 |
| Counting Sort (by digit) | §8.2 | Pulse (`Impl.fst`) | `is_stable_sort_on_digit` | Θ(n+k) implicit | 0 |
| Radix Sort (single-digit) | §8.3 | Pulse (`RadixSort.fst`) | `sorted ∧ permutation` | Θ(n+k) | 0 |
| Radix Sort (multi-digit, Pulse) | §8.3 | Pulse (`RadixSort.fst`) | `sorted ∧ permutation` | Θ(d(n+b)) | 0 |
| Radix Sort (multi-digit, pure) | §8.3 | Pure F\* (`MultiDigit.fst`) | `sorted ∧ permutation` | — | 0 |
| Bucket Sort | §8.4 | Pure F\* (`BucketSort.Lemmas.fst`) | `sorted ∧ is_permutation` | — | 0 |

## Counting Sort (CLRS §8.2)

### Specification

The core predicates are defined in `CountingSort.Spec`:

```fstar
let sorted (s: Seq.seq nat)
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let permutation (s1 s2: Seq.seq nat) : prop = (SeqP.permutation nat s1 s2)

let in_range (s:Seq.seq nat) (k:nat) : prop =
  forall (i:nat). i < Seq.length s ==> Seq.index s i <= k
```

The `permutation` predicate is `[@@"opaque_to_smt"]` — SMT only sees it through
explicitly invoked lemmas, preventing combinatorial blowup.

### Correctness Theorem: `counting_sort_impl`

The CLRS-faithful variant takes a read-only input `a` (at half permission `#0.5R`)
and writes sorted output to `b`:

```fstar
fn counting_sort_impl (a: array nat) (b: array nat) (len: SZ.t) (k_val: SZ.t)
  (#sa: erased (Seq.seq nat)) (#sb: erased (Seq.seq nat))
requires
  A.pts_to a #0.5R sa ** A.pts_to b sb **
  pure (SZ.v len <= A.length a /\ SZ.v len <= A.length b /\ ...
        S.in_range sa (SZ.v k_val) /\ SZ.v len > 0 /\ ...)
ensures exists* sb'.
  A.pts_to a #0.5R sa ** A.pts_to b sb' **
  pure (Seq.length sb' == Seq.length sa /\ S.sorted sb' /\ S.permutation sb' sa)
```

**Postcondition conjuncts:**
1. `Seq.length sb' == Seq.length sa` — output has the same length as input
2. `S.sorted sb'` — output is sorted (∀ i ≤ j, sb'[i] ≤ sb'[j])
3. `S.permutation sb' sa` — output is a permutation of the input

**Strongest guarantee?** Yes. `sorted ∧ permutation` fully characterizes a
correct sort: the output contains exactly the same multiset of elements in
non-decreasing order. No stronger functional property exists for sorting.

### Variant: `counting_sort_inplace`

Modifies the array in-place. Same postcondition (`sorted ∧ permutation`),
full ownership of `a` required.

### Variant: `counting_sort_by_digit`

Used as the stable subroutine for radix sort. Postcondition is
`is_stable_sort_on_digit sa sb' d base` rather than plain `sorted`,
encoding three properties: permutation, digit-wise sorted, and stability
(equal-key elements preserve relative input order).

### Complexity

No explicit ghost comparison counter. Linear Θ(n+k) time is implicit from
the algorithm's structure: one pass to count, one pass to place.

### Limitations

- **Range restriction**: All elements must be ≤ k, and `SZ.fits(k+2)` is
  required — this limits k to machine-representable sizes.
- **No complexity ghost counter**: The Θ(n+k) bound is not mechanically
  proven with a linked counter; it follows from the loop structure.

## Radix Sort (CLRS §8.3)

### Single-Digit Wrapper

For values bounded by k, radix sort with d=1 reduces to one pass of
in-place counting sort:

```fstar
fn radix_sort (a: array nat) (len: SZ.t) (k_val: SZ.t) (#s0: erased (Seq.seq nat))
requires A.pts_to a s0 ** pure (... S.in_range s0 (SZ.v k_val) ...)
ensures exists* s. A.pts_to a s **
  pure (Seq.length s == Seq.length s0 /\ S.sorted s /\ S.permutation s0 s)
```

### Multi-Digit Pulse Implementation

The full CLRS RADIX-SORT loops d times, calling `counting_sort_by_digit`
at each digit position:

```fstar
fn radix_sort_multidigit (a: array nat) (len: SZ.t) (base_val: SZ.t) (bigD: SZ.t)
  (#s0: erased (Seq.seq nat))
requires A.pts_to a s0 ** pure (...
  (forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i < B.pow (SZ.v base_val) (SZ.v bigD)) ...)
ensures exists* s. A.pts_to a s **
  pure (Seq.length s == Seq.length s0 /\ S.sorted s /\ S.permutation s0 s)
```

**Key precondition**: All elements must be less than `base^bigD`.

**Loop invariant** tracks:
- `B.permutation s0 s_curr` — overall permutation maintained across passes
- `sorted_up_to_digit s_curr (vd-1) base` — sorted on digits 0..vd−1

After all d passes, `lemma_sorted_up_to_all_digits_implies_sorted` bridges
digit-wise ordering to full value ordering.

### Multi-Digit Pure Specification

`RadixSort.MultiDigit.fst` provides a pure functional radix sort using
insertion sort as the stable subroutine:

```fstar
let rec radix_sort (s: seq nat) (num_digits: nat) (base: nat)
  : Tot (seq nat) (decreases num_digits)
  = if num_digits = 0 then s
    else let s' = radix_sort s (num_digits - 1) base in
         stable_sort_on_digit s' (num_digits - 1) base
```

The correctness theorem:

```fstar
let radix_sort_correct (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\ distinct s /\
                    (forall (i:nat). i < length s ==> index s i < pow base num_digits))
          (ensures (let result = radix_sort s num_digits base in
                   permutation s result /\ sorted result))
```

### Stability Theory

The `is_stable_sort_by` predicate (in `RadixSort.Spec`) has three conjuncts:

```fstar
let is_stable_sort_by (s_in s_out: seq nat) (key: nat -> nat) : prop =
  permutation s_in s_out /\                              (* 1. permutation *)
  (forall (i j:nat). i < j /\ j < length s_out ==>      (* 2. key-sorted *)
    key (index s_out i) <= key (index s_out j)) /\
  (forall (i1 i2 j1 j2:nat). ...                        (* 3. stability *)
    key (index s_in i1) == key (index s_in i2) ==> j1 < j2)
```

**CLRS Lemma 8.3** (`lemma_stable_pass_preserves_ordering`): A stable sort
on digit d preserves ordering established by digits 0..d−1.

### Strongest Guarantee?

Yes — `sorted ∧ permutation` is the strongest functional specification for
sorting. The stability property is additionally proven at the digit level,
which is necessary for the multi-digit inductive argument.

### Limitations

- **Pure `radix_sort_correct` requires `distinct s`**: The distinctness
  precondition is needed for the stability argument in the pure spec.
  The Pulse implementation does not require distinctness.
- **No standalone complexity proof**: Θ(d(n+b)) follows from d passes of
  Θ(n+b) counting sort but is not mechanized with a ghost counter.

## Bucket Sort (CLRS §8.4)

### Implementation

Bucket sort is implemented in **pure F\*** (not Pulse), operating on lists:

```fstar
let bucket_sort (xs: list int) (k: pos)
  : Pure (list int)
    (requires Cons? xs)
    (ensures fun ys -> sorted ys /\ List.length ys == List.length xs /\ is_permutation xs ys)
```

**Postcondition conjuncts:**
1. `sorted ys` — output list is sorted (recursive: each adjacent pair x ≤ y)
2. `List.length ys == List.length xs` — length preserved
3. `is_permutation xs ys` — count-based permutation (∀ x. count x xs == count x ys)

### Proof Structure

1. **Bucket distribution**: `filter_bucket` assigns each element to a bucket
   via `bucket_index`. The lemma `bucket_index_monotone` (using `lemma_div_le`)
   ensures that if v₁ ≤ v₂, their bucket indices are non-decreasing.

2. **Intra-bucket sorting**: Each bucket is sorted with `insertion_sort`.
   `insertion_sort_correct` proves sortedness; `insertion_sort_count` proves
   element preservation.

3. **Inter-bucket ordering**: `concat_sorted_ordered` proves that concatenating
   sorted buckets with disjoint value ranges yields a sorted list. The key
   lemma is `append_sorted_with_ordering`.

4. **Permutation**: `create_all_buckets_perm` + `sort_all_buckets_count`
   establish that the concatenated sorted buckets have the same element
   counts as the input, via `filter_bucket_count`.

### Strongest Guarantee?

Yes. `sorted ∧ length_preserved ∧ is_permutation` is the strongest
functional specification for sorting over lists.

### Limitations

- **List-based only**: No array/Pulse implementation. This limits practical
  applicability but provides a clean mathematical formalization.
- **Precondition `Cons? xs`**: Input must be non-empty.
- **No complexity proof**: Expected O(n) (when k ≈ n with uniform distribution)
  is not mechanized.
- **`bucket_index` edge cases**: When `max_val <= min_val` or values are
  out of range, `bucket_index` maps to bucket 0 — this is handled correctly
  but is a design artifact.

## File Inventory

| File | Role | Lines | Admits |
|------|------|-------|--------|
| `CLRS.Ch08.CountingSort.Spec.fst` | Core predicates: `sorted`, `permutation`, `in_range` | ~33 | 0 |
| `CLRS.Ch08.CountingSort.Impl.fsti` | Interface: three counting sort variants | ~108 | 0 |
| `CLRS.Ch08.CountingSort.Impl.fst` | Pulse implementation of all three variants | large | 0 |
| `CLRS.Ch08.CountingSort.Lemmas.fsti` | Proof helper definitions (`counts_match_prefix`, etc.) | ~30 | 0 |
| `CLRS.Ch08.CountingSort.Lemmas.fst` | Lemma proofs for counting sort correctness | large | 0 |
| `CLRS.Ch08.CountingSort.StableLemmas.fst` | Stability lemmas for CLRS-faithful variant | large | 0 |
| `CLRS.Ch08.CountingSort.DigitSortLemmas.fst` | Digit extraction lemmas for by-digit variant | medium | 0 |
| `CLRS.Ch08.RadixSort.Base.fst` | Digit extraction, `pow`, `permutation` base defs | medium | 0 |
| `CLRS.Ch08.RadixSort.Spec.fst` | Digit decomposition, `is_stable_sort_by` | ~32K | 0 |
| `CLRS.Ch08.RadixSort.Stability.fst` | CLRS Lemma 8.3: `sorted_up_to_digit` inductive invariant | large | 0 |
| `CLRS.Ch08.RadixSort.FullSort.fst` | Bridge: digit-wise sorted → value sorted | medium | 0 |
| `CLRS.Ch08.RadixSort.Bridge.fst` | Bridge: Base module sorted/perm → Spec module sorted/perm | small | 0 |
| `CLRS.Ch08.RadixSort.Lemmas.fst` | Aggregation module re-exporting key results | ~81 | 0 |
| `CLRS.Ch08.RadixSort.MultiDigit.fst` | Pure functional multi-digit radix sort + correctness | ~1100 | 0 |
| `CLRS.Ch08.RadixSort.fst` | Pulse wrappers: `radix_sort`, `radix_sort_multidigit` | ~197 | 0 |
| `CLRS.Ch08.BucketSort.Spec.fst` | Pure bucket sort spec: `sorted`, `bucket_index`, helpers | ~153 | 0 |
| `CLRS.Ch08.BucketSort.Lemmas.fst` | Bucket sort correctness + main `bucket_sort` function | ~446 | 0 |
| `Makefile` | Build configuration | 2 | — |

## Building

```bash
# From the ch08-linear-sorting directory:
make

# Or from the project root:
make -C ch08-linear-sorting
```

Requires the Pulse toolchain. Set `PULSE_ROOT` if not at `../../pulse`.
