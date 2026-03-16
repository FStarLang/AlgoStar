# Bucket Sort (CLRS §8.4)

## Top-Level Signature

Bucket Sort is implemented as a **pure function** (not Pulse, not
array-based) in `CLRS.Ch08.BucketSort.Lemmas.fst`:

```fstar
let bucket_sort (xs: list int) (k: pos)
  : Pure (list int)
    (requires Cons? xs)
    (ensures fun ys -> sorted ys /\ List.length ys == List.length xs /\ is_permutation xs ys)
```

### Parameters

* `xs` is a **list** of `int` (not an array). This is a pure
  functional implementation.

* `k` is the number of buckets (`pos`, i.e., `k ≥ 1`).

### Preconditions

* `Cons? xs` — the input list must be non-empty.

### Postcondition

The return value `ys` satisfies:

* `sorted ys` — the output is sorted.

* `List.length ys == List.length xs` — length is preserved.

* `is_permutation xs ys` — the output is a permutation of the input.

## Auxiliary Definitions

### `sorted` (from `CLRS.Ch08.BucketSort.Spec`)

```fstar
let rec sorted (xs: list int) : prop =
  match xs with
  | [] -> True
  | [x] -> True
  | x :: y :: rest -> x <= y /\ sorted (y :: rest)
```

Adjacent-pairs sorted, over `list int`. Note: this is a different
definition from the sequence-based `sorted` used in other chapters —
it operates on lists and uses the recursive adjacent-pairs
characterization.

### `is_permutation` (from `CLRS.Ch08.BucketSort.Spec`)

```fstar
let is_permutation (xs ys: list int) : prop =
  forall x. List.count x xs == List.count x ys
```

Count-based permutation: every value has the same count in both lists.
This is also a different definition from the `SeqP.permutation`-based
definitions used elsewhere.

### `in_range` (from `CLRS.Ch08.BucketSort.Spec`)

```fstar
let rec in_range (xs: list int) (lb ub: int) : prop =
  match xs with
  | [] -> True
  | x :: rest -> lb <= x /\ x < ub /\ in_range rest lb ub
```

All elements in the half-open interval `[lb, ub)`.

### `bucket_index` (from `CLRS.Ch08.BucketSort.Spec`)

```fstar
let bucket_index (v min_val max_val: int) (k: pos) : nat =
  if max_val <= min_val || v < min_val || v >= max_val then 0
  else
    let range_size = max_val - min_val in
    let bucket_size = if range_size / k = 0 then 1 else range_size / k in
    let bi = (v - min_val) / bucket_size in
    if bi >= k then k - 1 else bi
```

Maps a value to its bucket index. The range `[min_val, max_val)` is
divided into `k` buckets of equal size, with the last bucket absorbing
overflow.

### `buckets_correct` (from `CLRS.Ch08.BucketSort.Spec`)

```fstar
let rec buckets_correct (buckets: list (list int)) (min_val max_val: int) (k: pos) (offset: nat) : prop =
  match buckets with
  | [] -> True
  | b :: bs ->
    (forall x. List.mem x b ==> min_val <= x /\ x < max_val /\ bucket_index x min_val max_val k = offset) /\
    buckets_correct bs min_val max_val k (offset + 1)
```

Each bucket contains only elements that map to its index.

### `all_sorted` (from `CLRS.Ch08.BucketSort.Spec`)

```fstar
let rec all_sorted (buckets: list (list int)) : prop =
  match buckets with
  | [] -> True
  | b :: bs -> sorted b /\ all_sorted bs
```

Every bucket is individually sorted.

## What Is Proven

1. **Functional correctness**: `bucket_sort` returns a sorted
   permutation of the input with preserved length.

2. **Insertion sort correctness** (`insertion_sort_correct`): The
   per-bucket sort produces a sorted list.

3. **Insertion sort is a permutation** (`insertion_sort_count`): Count
   of each element is preserved.

4. **Bucket index monotonicity** (`bucket_index_monotone`): `v1 ≤ v2
   ⟹ bucket_index v1 ≤ bucket_index v2`. This ensures inter-bucket
   ordering.

5. **Inter-bucket ordering** (`bucket_index_strict`): If `v1` and
   `v2` are in different buckets with `bucket(v1) < bucket(v2)`, then
   `v1 < v2`. This enables sorted concatenation.

6. **Sorted concatenation** (`concat_sorted_ordered`): Concatenating
   individually sorted buckets in order produces a globally sorted
   list, given inter-bucket ordering.

7. **Permutation preservation** (`create_all_buckets_perm`,
   `sort_all_buckets_count`): The count of each value is preserved
   through bucket distribution and per-bucket sorting.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **NOT Pulse, NOT array-based.** This is a pure functional
   implementation over `list int`, not an imperative Pulse
   implementation over arrays. It cannot be compiled to efficient
   imperative code.

2. **No complexity bounds.** The expected O(n) average-case complexity
   (CLRS Theorem 8.1, assuming uniform distribution) is not proven.
   The use of insertion sort per bucket gives O(n²) worst case when
   all elements fall into one bucket.

3. ~~**`Cons? xs` precondition.** The input must be non-empty. An empty
   list is trivially sorted but is not handled.~~
   **RESOLVED.** `bucket_sort` now accepts empty lists, returning `[]`
   trivially. The empty list is sorted and a permutation of itself.

4. **Uses `list_min`/`list_max` internally.** The algorithm computes
   `min_val = list_min xs` and `max_val = list_max xs`, then uses
   `max_val + 1` as the exclusive upper bound. The special case
   `min_val == max_val` (all elements equal) is handled separately by
   returning the input unchanged.

5. **Different definitions from other chapters.** Uses `list int`
   instead of `Seq.seq int`, and custom `sorted` (recursive on lists)
   and `is_permutation` (count-based on lists) definitions. These are
   not connected to the canonical `CLRS.Common.SortSpec` definitions.

6. **No stability guarantee.** The specification does not state
   stability.

7. **Bucket size edge case.** When `range_size / k = 0` (range smaller
   than number of buckets), `bucket_size` defaults to 1. When
   `bi >= k` (last bucket overflow), it is clamped to `k - 1`. These
   edge cases are correct but add specification complexity.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Time | O(n) average-case expected | ❌ Not proven | N/A |
| Time | O(n²) worst-case | ❌ Not proven | N/A |

No complexity analysis is formally verified. The algorithm uses
insertion sort per bucket, giving O(n²) worst case. The O(n)
average-case analysis from CLRS (assuming uniform distribution)
requires probabilistic reasoning not present in this framework.

## Proof Structure

**`bucket_sort`** (in `Lemmas.fst`):
1. Compute `min_val = list_min xs`, `max_val = list_max xs`.
2. If `min_val == max_val`, all elements are equal → return `xs`
   (proved sorted by `all_equal_sorted`).
3. Otherwise:
   a. Create buckets: `create_all_buckets xs 0 k min_val (max_val+1)`.
   b. Sort each bucket: `sort_all_buckets buckets`.
   c. Concatenate: `concat_all sorted_buckets`.
4. Prove sorted via `concat_sorted_ordered` (inter-bucket ordering +
   per-bucket sortedness).
5. Prove length via `filter_all_length` + `sort_all_buckets_preserves_sum`
   + `concat_all_length`.
6. Prove permutation via `create_all_buckets_perm` +
   `sort_all_buckets_count`.

Key lemmas:
* `bucket_index_monotone`/`bucket_index_strict`: inter-bucket ordering.
* `append_sorted_with_ordering`: concatenating sorted lists with
  cross-list ordering gives a sorted result.
* `filter_bucket_count`: counting through bucket distribution.

## Files

| File | Role |
|------|------|
| `CLRS.Ch08.BucketSort.Spec.fst` | Definitions (`sorted`, `is_permutation`, `bucket_index`, `insertion_sort`, bucket functions) |
| `CLRS.Ch08.BucketSort.Lemmas.fsti` | Public interface for correctness lemmas and `bucket_sort` (new) |
| `CLRS.Ch08.BucketSort.Lemmas.fst` | Proofs and main `bucket_sort` function |

## Rubric Compliance (per `autoclrs/audit/RUBRIC.md`)

| Rubric Slot | File | Status |
|-------------|------|:------:|
| `Spec.fst` | `BucketSort.Spec.fst` | ✅ |
| `Lemmas.fst` | `BucketSort.Lemmas.fst` | ✅ |
| `Lemmas.fsti` | `BucketSort.Lemmas.fsti` | ✅ (new) |
| `Impl.fst` | — | ❌ Pure F* only (no Pulse implementation) |
| `Impl.fsti` | — | ❌ N/A (no Pulse implementation) |
| `Complexity.fst` | — | ❌ Not present |
| `Complexity.fsti` | — | ❌ Not present |

## Profiling (Build from clean, -j4, wall-clock completion times)

| File | Completion (s) | Max z3rlimit | z3refresh | split_queries |
|------|---------------:|:------------:|:---------:|:-------------:|
| Spec.fst | 2 | 30 | 0 | 0 |
| Lemmas.fsti | 504 | — | — | — |
| **Lemmas.fst** | **660** | **200** | **0** | **0** |

**Note**: Warning 349 on `bucket_sort` body (lines 409-448) — the VC
succeeded only after implicit split_queries. Should add
`--split_queries always` to the push-options for stability.

## Checklist

Priority-ordered items for reaching a fully proven, high-quality
implementation:

- [x] Zero admits, zero assumes across all files
- [x] Rubric slots: Spec.fst, Lemmas.fst
- [x] Lemmas.fsti interface file created
- [x] Empty-list support for `bucket_sort`
- [x] Sorted output proven
- [x] Length preservation proven
- [x] Permutation proven (count-based)
- [x] Inter-bucket ordering proven (`bucket_index_monotone`, `bucket_index_strict`)
- [ ] **P1 (Stabilization)**: Warning 349 on `bucket_sort` — VC relies on
      implicit split_queries. Explicit `--split_queries always` breaks
      the inner `List.mem_count` proof (context lost). The warning is
      harmless; the proof is stable as-is.
- [ ] **P2 (Rubric)**: Create Pulse `Impl.fst`/`Impl.fsti` — convert
      list-based pure implementation to array-based Pulse implementation.
      This is a significant effort.
- [ ] **P3 (Rubric)**: Add `Complexity.fst`/`.fsti` for average-case
      O(n) analysis (requires probabilistic reasoning).
- [ ] **P4 (Spec)**: Connect `sorted`/`is_permutation` definitions to
      canonical `CLRS.Common.SortSpec` definitions (currently uses
      `list int` with custom definitions).
- [ ] **P5 (Spec)**: Add stability guarantee to bucket sort specification.
