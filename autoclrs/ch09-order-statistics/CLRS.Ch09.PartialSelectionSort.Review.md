# Partial Selection Sort (CLRS §9)

## Top-Level Signatures

Here are the top-level signatures proven about `find_min_index_from` and
`select` in `CLRS.Ch09.PartialSelectionSort.Impl.fsti`:

### `find_min_index_from`

```fstar
fn find_min_index_from
  (#p: perm)
  (a: array int)
  (#s: Ghost.erased (Seq.seq int))
  (start: SZ.t)
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s ** GR.pts_to ctr c0 **
    pure (
      SZ.v start < SZ.v len /\
      SZ.v len == Seq.length s /\
      SZ.v len == A.length a
    )
  returns min_idx: SZ.t
  ensures exists* (cf: nat).
    A.pts_to a #p s ** GR.pts_to ctr cf **
    pure (
      SZ.v start <= SZ.v min_idx /\
      SZ.v min_idx < SZ.v len /\
      is_min_in_range s (SZ.v min_idx) (SZ.v start) (SZ.v len) /\
      cf >= reveal c0 /\
      cf - reveal c0 == SZ.v len - SZ.v start - 1
    )
```

### `select`

```fstar
fn select
  (a: array int)
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
      SZ.v k > 0 /\
      SZ.v k <= SZ.v n
    )
  returns result: int
  ensures exists* s_final (cf: nat).
    A.pts_to a s_final ** GR.pts_to ctr cf **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      sorted_prefix s_final (SZ.v k) /\
      prefix_leq_suffix s_final (SZ.v k) /\
      SZ.v k > 0 /\
      result == Seq.index s_final (SZ.v k `Prims.op_Subtraction` 1) /\
      complexity_bounded_select cf (reveal c0) (SZ.v n) (SZ.v k)
    )
```

### Parameters

* `a` is a mutable array of `int`. For `find_min_index_from`, it is borrowed
  read-only (`#p: perm`).

* `n` is the total array length; `k` is the number of smallest elements to
  place (1-indexed: `k = 1` finds the minimum).

* `start` is the beginning of the unsorted suffix for `find_min_index_from`.

* `ctr` is a ghost counter for comparison counting.

### Preconditions

For `find_min_index_from`:
* `SZ.v start < SZ.v len`: Start is within bounds.

For `select`:
* `SZ.v n > 0`: Non-empty array.
* `SZ.v k > 0 /\ SZ.v k <= SZ.v n`: k is at least 1 and at most n.

### Postconditions

For `find_min_index_from`:
* `is_min_in_range s min_idx start len` — The returned index holds the minimum
  of the range.
* `cf - c0 == len - start - 1` — Exact comparison count.

For `select`:
* `permutation s0 s_final` — Output is a permutation of input.
* `sorted_prefix s_final k` — The first k elements are sorted.
* `prefix_leq_suffix s_final k` — Every element in the first k positions is ≤
  every element in the remaining positions.
* `result == Seq.index s_final (k - 1)` — The result is the k-th smallest.
* `complexity_bounded_select cf c0 n k` — Bounded comparisons.

## Auxiliary Definitions

### `permutation` (defined locally in `CLRS.Ch09.PartialSelectionSort.Impl.fsti`)

```fstar
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)
```

**Note:** This is a *local* definition — it does NOT import from
`CLRS.Common.SortSpec`. It wraps the same standard library notion, but is
defined independently in this module.

### `is_min_in_range` (from `CLRS.Ch09.PartialSelectionSort.Impl.fsti`)

```fstar
let is_min_in_range (s: Seq.seq int) (i: nat) (start: nat) (len: nat) : prop =
  start <= i /\ i < len /\ len <= Seq.length s /\
  (forall (j: nat). start <= j /\ j < len ==> Seq.index s i <= Seq.index s j)
```

### `sorted_prefix` (from `CLRS.Ch09.PartialSelectionSort.Impl.fsti`)

```fstar
let sorted_prefix (s: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length s /\
  (forall (i j: nat). i < j /\ j < bound ==> Seq.index s i <= Seq.index s j)
```

The first `bound` elements are sorted.

### `prefix_leq_suffix` (from `CLRS.Ch09.PartialSelectionSort.Impl.fsti`)

```fstar
let prefix_leq_suffix (s: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length s /\
  (forall (i j: nat). i < bound /\ bound <= j /\ j < Seq.length s ==>
    Seq.index s i <= Seq.index s j)
```

Every element in `[0, bound)` is ≤ every element in `[bound, n)`.

### `complexity_bounded_select` (from `CLRS.Ch09.PartialSelectionSort.Impl.fst`)

```fstar
let complexity_bounded_select (cf c0 n k: nat) : prop =
  k > 0 /\ k <= n /\ n > 0 /\
  cf >= c0 /\
  cf - c0 <= op_Multiply k (n - 1)
```

The bound is k × (n−1) comparisons: k rounds, each scanning up to n−1 elements.
This is O(nk) worst case.

## What Is Proven

1. **Functional correctness**: The first k elements of the output are the k
   smallest elements of the input, in sorted order. The output is a permutation
   of the input. The k-th smallest element is returned.

2. **Partition property**: `prefix_leq_suffix` ensures a clean split between
   the sorted prefix and the unsorted suffix.

3. **Complexity**: At most k × (n−1) comparisons.

**Zero admits, zero assumes.** All proof obligations are mechanically discharged.

## Specification Gaps and Limitations

1. **Own permutation definition.** This module defines its own
   `permutation` predicate locally rather than importing from a common module.
   This is the same underlying `Seq.Properties.permutation`, but clients cannot
   directly interchange with the `permutation` from `SortSpec` or
   `Quickselect.Spec` without a bridge lemma.

2. **`k` is 1-indexed.** Unlike quickselect (which uses 0-indexed k), this
   function uses `k >= 1`. The result is `s_final[k-1]`. This mismatch could
   confuse users combining the two APIs.

3. **`complexity_bounded_select` is abstract in the `.fsti`.** The definition
   `cf - c0 <= k * (n - 1)` is only visible in the `.fst` file. Clients see
   `val complexity_bounded_select (cf c0 n k: nat) : prop`.

4. **O(nk) not O(n) for median.** For k = n/2, this is O(n²). CLRS's
   RANDOMIZED-SELECT achieves O(n) expected. The Complexity module documents this
   trade-off explicitly.

5. **Simplified complexity model.** The actual number of comparisons per round
   is n−i−1 (shrinking), but the specification uses n−1 per round. The
   Complexity module provides a tighter model (`select_comparisons_tight`) and
   proves it is strictly better when k > 1, but the implementation's
   postcondition uses the simpler bound.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| `find_min_index_from` comparisons | len − start − 1 | ✅ Ghost counter | ✅ Exact |
| `select` comparisons | O(nk) = k × (n−1) | ✅ Ghost counter | Upper bound only |

The Complexity module also proves:
* Exact closed form: `select_comparisons n k == k * (n - 1)`
* Tighter model: `2 * select_comparisons_tight n k == k * (2*n - k - 1)`
* Tight is strictly better when k > 1

## Proof Structure

* **`CLRS.Ch09.PartialSelectionSort.Lemmas`**: Key lemma
  `sorted_permutation_equal` proves that two sorted permutations of the same
  multiset are equal. Partition correctness lemmas
  (`partition_left_part_correct`, `partition_right_part_correct`,
  `partition_pivot_is_kth`) bridge from the partition property to `select_spec`.
  `pulse_correctness_hint` provides the final bridge for the Pulse
  implementation.

* **`CLRS.Ch09.PartialSelectionSort.Spec`**: Defines `select_spec` via
  `pure_sort` (a pure insertion sort on sequences), and proves the partition
  property of `select_spec` and permutation invariance of `count_lt`/`count_le`.

* **`CLRS.Ch09.PartialSelectionSort.Complexity`**: Defines and analyzes the
  comparison count.

## Files

| File | Role |
|------|------|
| `CLRS.Ch09.PartialSelectionSort.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch09.PartialSelectionSort.Impl.fst` | Pulse implementation + `complexity_bounded_select` |
| `CLRS.Ch09.PartialSelectionSort.Spec.fst` | `select_spec`, `pure_sort`, `is_permutation`, counting predicates |
| `CLRS.Ch09.PartialSelectionSort.Complexity.fsti` | Complexity analysis signatures |
| `CLRS.Ch09.PartialSelectionSort.Complexity.fst` | `select_comparisons`, bounds, tight model |
| `CLRS.Ch09.PartialSelectionSort.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch09.PartialSelectionSort.Lemmas.fst` | `sorted_permutation_equal`, partition correctness |
