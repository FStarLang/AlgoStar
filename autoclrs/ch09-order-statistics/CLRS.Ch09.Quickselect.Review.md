# Quickselect (CLRS §9.2)

## Top-Level Signatures

Here are the top-level signatures proven about `partition_in_range` and
`quickselect` in `CLRS.Ch09.Quickselect.Impl.fsti`:

### `partition_in_range`

```fstar
fn partition_in_range
  (a: A.array int)
  (#s0: Ghost.erased (Seq.seq int))
  (lo: SZ.t)
  (hi: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v lo < SZ.v hi /\
      SZ.v hi <= Seq.length s0 /\
      Seq.length s0 == A.length a
    )
  returns pivot_pos: SZ.t
  ensures exists* s1 (cf: nat).
    A.pts_to a s1 ** GR.pts_to ctr cf **
    pure (
      Seq.length s1 == Seq.length s0 /\
      SZ.v lo <= SZ.v pivot_pos /\
      SZ.v pivot_pos < SZ.v hi /\
      permutation s0 s1 /\
      partition_ordered s1 (SZ.v lo) (SZ.v pivot_pos) (SZ.v hi) /\
      unchanged_outside s0 s1 (SZ.v lo) (SZ.v hi) /\
      cf >= reveal c0 /\
      cf - reveal c0 == SZ.v hi - SZ.v lo - 1
    )
```

### `quickselect`

```fstar
fn quickselect
  (a: A.array int)
  (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (k: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s0 /\
      SZ.v n == A.length a /\
      SZ.v n > 0 /\
      SZ.v k < SZ.v n
    )
  returns result: int
  ensures exists* s_final (cf: nat).
    A.pts_to a s_final ** GR.pts_to ctr cf **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      SZ.v k < Seq.length s_final /\
      result == Seq.index s_final (SZ.v k) /\
      (forall (i: nat). i < SZ.v k /\ i < Seq.length s_final ==>
        Seq.index s_final i <= result) /\
      (forall (i: nat). SZ.v k < i /\ i < Seq.length s_final ==>
        result <= Seq.index s_final i) /\
      result == PSSSpec.select_spec s0 (SZ.v k) /\
      complexity_bounded_quickselect cf (reveal c0) (SZ.v n)
    )
```

### Parameters

* `a` is a mutable array of `int`. The ghost variable `s0` captures the initial
  contents.

* `n` / `len`: number of elements; `lo`, `hi`: subrange bounds for partition.

* `k` is the rank to select (0-indexed): `k = 0` selects the minimum, `k = n-1`
  selects the maximum.

* `ctr` is a ghost counter for comparison counting.

### Preconditions

For `partition_in_range`:
* `SZ.v lo < SZ.v hi`: Non-empty subrange.
* `SZ.v hi <= Seq.length s0`: Subrange within bounds.
* `Seq.length s0 == A.length a`: Logical and physical lengths match.

For `quickselect`:
* `SZ.v n > 0`: Non-empty array.
* `SZ.v k < SZ.v n`: Rank is within bounds.

### Postconditions

For `partition_in_range`:
* `permutation s0 s1` — Output is a permutation of input.
* `partition_ordered s1 lo pivot_pos hi` — Elements left of pivot are ≤ pivot,
  elements right are ≥ pivot.
* `unchanged_outside s0 s1 lo hi` — Elements outside `[lo, hi)` are untouched.
* `cf - c0 == hi - lo - 1` — Exactly `hi - lo - 1` comparisons (one pass).

For `quickselect`:
* `permutation s0 s_final` — Output is a permutation of input.
* `result == Seq.index s_final k` — Result is the element at position k.
* `forall i < k. s_final[i] <= result` — Left partition property.
* `forall i > k. result <= s_final[i]` — Right partition property.
* `result == PSSSpec.select_spec s0 k` — **Correctness bridge**: the result
  equals the k-th element of the sorted input.
* `complexity_bounded_quickselect cf c0 n` — Worst-case O(n²) bound.

## Auxiliary Definitions

### `permutation` (from `CLRS.Ch09.Quickselect.Spec`)

```fstar
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)
```

Wraps F\*'s standard library permutation, kept opaque for SMT performance.

### `partition_ordered` (from `CLRS.Ch09.Quickselect.Spec`)

```fstar
let partition_ordered (s: Seq.seq int) (lo p hi: nat) : prop =
  lo <= p /\ p < hi /\ hi <= Seq.length s /\
  (forall (idx: nat). idx < Seq.length s ==>
    (lo <= idx /\ idx < p) ==> Seq.index s idx <= Seq.index s p) /\
  (forall (idx: nat). idx < Seq.length s ==>
    (p < idx /\ idx < hi) ==> Seq.index s idx >= Seq.index s p)
```

Standard Lomuto-style partition ordering: elements in `[lo, p)` are ≤ pivot,
elements in `(p, hi)` are ≥ pivot.

### `unchanged_outside` (from `CLRS.Ch09.Quickselect.Spec`)

```fstar
let unchanged_outside (s1 s2: Seq.seq int) (lo hi: nat) : prop =
  Seq.length s1 == Seq.length s2 /\
  lo <= hi /\ hi <= Seq.length s1 /\
  (forall (i: nat). i < Seq.length s1 ==>
    (i < lo \/ hi <= i) ==>
    Seq.index s1 i == Seq.index s2 i)
```

Elements at indices outside `[lo, hi)` are unchanged.

### `select_spec` (from `CLRS.Ch09.PartialSelectionSort.Spec`)

```fstar
let select_spec (s: seq int) (k: nat{k < Seq.length s}) : int =
  pure_sort_length s;
  Seq.index (pure_sort s) k
```

The k-th smallest element is defined as the element at index k of the sorted
sequence. `pure_sort` is a pure insertion sort on sequences (not the imperative
one). This provides a reference definition independent of any algorithm.

### `complexity_bounded_quickselect` (from `CLRS.Ch09.Quickselect.Impl.fsti`)

```fstar
let complexity_bounded_quickselect (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= QC.qs_cost n
```

Where `qs_cost` is the worst-case recurrence (from `CLRS.Ch09.Quickselect.Complexity`):

```fstar
let rec qs_cost (n: nat) : nat =
  if n <= 1 then 0
  else n + qs_cost (n - 1)
```

This solves to `qs_cost n = n(n+1)/2 = O(n²)`. The module also proves:
* `qs_bound`: `qs_cost n <= n * (n + 1) / 2`
* `qs_quadratic`: `qs_cost n <= n * n`

## What Is Proven

1. **Partition correctness**: `partition_in_range` rearranges a subarray such
   that elements left of the pivot are ≤ the pivot and elements right are ≥,
   while leaving elements outside the range untouched.

2. **Selection correctness**: `quickselect` returns `select_spec s0 k`, the k-th
   smallest element of the original input. This is the strongest possible
   correctness statement — it connects the imperative result to a pure
   mathematical definition.

3. **Partition property**: The final array is partitioned at position k —
   all elements before k are ≤ the result, all elements after are ≥.

4. **Worst-case complexity**: O(n²) comparisons, proven via the recurrence
   `T(n) = n + T(n-1)`.

**Zero admits, zero assumes.** All proof obligations are mechanically discharged.

## Specification Gaps and Limitations

1. **Only worst-case O(n²) proven, NOT expected O(n).** CLRS proves that
   RANDOMIZED-SELECT has O(n) expected time complexity. This implementation is
   deterministic (always picks the last element as pivot), so the expected-case
   analysis does not apply. The proven bound is the tight worst case.

2. **No randomization.** The deterministic pivot selection means adversarial
   inputs trigger O(n²) behavior. CLRS's randomized version avoids this.

3. **`k` is 0-indexed.** CLRS uses 1-indexed ranks (the i-th order statistic).
   This implementation uses 0-indexing: `k = 0` is the minimum.

4. **~~`complexity_bounded_quickselect` is abstract in the `.fsti`.~~**
   *(Addressed.)* The definition `cf - c0 <= qs_cost n` is now exposed as a
   transparent `let` in the `.fsti`, so clients can directly see the bound.

5. **Two permutation notions.** Quickselect uses `Seq.Properties.permutation`
   (wrapped in an opaque `permutation`), while `select_spec` uses
   `PartialSelectionSort.Spec.is_permutation` (count-based). A bridge lemma
   `seq_perm_implies_is_perm` in `Quickselect.Lemmas` connects them.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Partition comparisons | hi − lo − 1 | ✅ Ghost counter | ✅ Exact |
| Quickselect comparisons | O(n²) = n(n+1)/2 | ✅ Ghost counter | Upper bound only |

## Proof Structure

The proof uses three key lemma modules:

* **`CLRS.Ch09.Quickselect.Lemmas`**: Bound preservation through partitions
  (`perm_unchanged_lower_bound_forall`, `perm_unchanged_upper_bound_forall`)
  and a bridge from `Seq.Properties.permutation` to count-based
  `is_permutation` (`seq_perm_implies_is_perm`).

* **`CLRS.Ch09.PartialSelectionSort.Lemmas`**: The `pulse_correctness_hint`
  lemma bridges the partition property to `select_spec`: if `s_final` is a
  permutation of `s0` and is partitioned at k, then `s_final[k] == select_spec
  s0 k`.

* **`CLRS.Ch09.Quickselect.Complexity`**: Defines `qs_cost`, proves the
  recurrence solves to O(n²), and establishes monotonicity.

## Files

| File | Role |
|------|------|
| `CLRS.Ch09.Quickselect.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch09.Quickselect.Impl.fst` | Pulse implementation + `complexity_bounded_quickselect` |
| `CLRS.Ch09.Quickselect.Spec.fst` | `permutation`, `partition_ordered`, `unchanged_outside` |
| `CLRS.Ch09.Quickselect.Complexity.fsti` | `qs_cost` signature and bound lemmas |
| `CLRS.Ch09.Quickselect.Complexity.fst` | `qs_cost` definition and proofs |
| `CLRS.Ch09.Quickselect.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch09.Quickselect.Lemmas.fst` | Bound preservation and bridge proofs |
| `CLRS.Ch09.PartialSelectionSort.Spec.fst` | `select_spec`, `pure_sort`, `is_permutation` |
| `CLRS.Ch09.PartialSelectionSort.Lemmas.fst` | `pulse_correctness_hint` |
