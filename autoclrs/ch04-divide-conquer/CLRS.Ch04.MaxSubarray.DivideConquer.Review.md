# Divide-and-Conquer Maximum Subarray (CLRS §4.1)

## Top-Level Signature

This is a **pure** (non-imperative) implementation. The main function is in
`CLRS.Ch04.MaxSubarray.DivideConquer.Spec.fst`:

```fstar
let rec find_maximum_subarray_dc (s: Seq.seq int) (low high: nat) 
  : Pure (int * nat * nat)
  (requires low <= high /\ high <= Seq.length s)
  (ensures fun (sum, left, right) -> low <= left /\ left <= right /\ right <= high)
  (decreases high - low)
```

And the simplified wrapper:

```fstar
let find_maximum_subarray_sum (s: Seq.seq int) : Tot int =
  if Seq.length s = 0 then 0
  else (
    let (sum, _, _) = find_maximum_subarray_dc s 0 (Seq.length s) in
    sum
  )
```

### Parameters

* `s` is an immutable `Seq.seq int` — the input sequence.

* `low` and `high` are natural number bounds defining the sub-range `[low, high)`.

### Preconditions

* `low <= high /\ high <= Seq.length s`: The range is valid.

### Postcondition

The function returns a triple `(sum, left, right)` where:

* `low <= left /\ left <= right /\ right <= high` — The returned range
  `[left, right)` is within `[low, high)`.

Note: The `ensures` clause in the type signature is deliberately weak —
it only states bounds validity. The full correctness properties are proven
as separate lemmas.

## Auxiliary Definitions

### `find_max_crossing_subarray` (from `CLRS.Ch04.MaxSubarray.DivideConquer.Spec`)

```fstar
let find_max_crossing_subarray (s: Seq.seq int) (low mid high: nat) 
  : Pure (int * nat * nat)
  (requires low < mid /\ mid < high /\ high <= Seq.length s)
  (ensures fun (sum, left_idx, right_idx) -> 
    low <= left_idx /\ left_idx < mid /\ 
    mid < right_idx /\ right_idx <= high)
```

Finds the maximum subarray crossing the midpoint, by scanning left from
`mid - 1` and right from `mid`. This is the `FIND-MAX-CROSSING-SUBARRAY`
procedure from CLRS §4.1.

### `dc_ops_count` (from `CLRS.Ch04.MaxSubarray.DivideConquer.Complexity`)

```fstar
let rec dc_ops_count (n: nat) : Tot nat =
  if n <= 1 then 1
  else
    let half_ops = dc_ops_count (n / 2) in
    let double_half = half_ops + half_ops in
    double_half + n
```

The operation count recurrence: `T(n) = 2T(n/2) + n` for `n > 1`,
`T(1) = 1`. Matches the CLRS recurrence for the D&C max subarray.

### `log2_ceil` (from `CLRS.Ch04.MaxSubarray.DivideConquer.Complexity`)

```fstar
let rec log2_ceil (n: pos) : Tot nat (decreases n) =
  if n = 1 then 0
  else 1 + log2_ceil ((n + 1) / 2)
```

Ceiling of log base 2. Used in the closed-form complexity bound.

### `sum_range` (from `CLRS.Ch04.MaxSubarray.Spec`)

```fstar
let rec sum_range (s: Seq.seq int) (i j: nat) : Pure int
  (requires i <= j /\ j <= Seq.length s)
  (ensures fun _ -> True)
  (decreases j - i)
  =
  if i >= j then 0
  else Seq.index s i + sum_range s (i + 1) j
```

Sum of elements in `[i, j)`. Used in the correctness lemmas.

### `max_subarray_spec` (from `CLRS.Ch04.MaxSubarray.Spec`)

```fstar
let max_subarray_spec (s: Seq.seq int) : Tot int =
  if Seq.length s = 0 then 0
  else kadane_spec s 0 0 (Seq.index s 0)
```

The canonical max subarray specification (Kadane-based). The D&C algorithm
is proven equivalent to this.

## What Is Proven

Unlike the imperative algorithms, correctness here is proven via separate
lemmas rather than in the type signature:

1. **`lemma_dc_sum_correct`**: The returned sum equals `sum_range s left right`
   (the actual subarray sum for the returned range).

2. **`lemma_dc_nonempty`**: For non-empty input (`low < high`), the returned
   range is non-empty (`left < right`).

3. **`lemma_dc_optimal`**: For any subarray `[qi, qj)` within `[low, high)`,
   the D&C result is ≥ `sum_range s qi qj`. The result is the maximum.

4. **`dc_kadane_equivalence`**: `find_maximum_subarray_sum s == max_subarray_spec s`.
   The D&C and Kadane algorithms produce identical results.
   **No `elements_bounded` precondition.**

5. **`lemma_dc_complexity_bound`**:
   `dc_ops_count n <= 4 * n * (log2_ceil n + 1)`, i.e., O(n log n).

Together, these establish that the D&C algorithm computes the true maximum
non-empty subarray sum in O(n log n) time.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Weak type-level postcondition.** The `ensures` clause of
   `find_maximum_subarray_dc` only states `low <= left /\ left <= right /\ right <= high`.
   It does not state correctness or optimality. These are proven as separate
   lemmas, which means a caller must invoke them explicitly. A stronger design
   would encode correctness in the return type.

2. ~~**Equivalence with Kadane requires `elements_bounded`.**~~ **RESOLVED.**
   The `dc_kadane_equivalence` theorem now holds unconditionally (requires
   only `Seq.length s > 0`). The `initial_min` sentinel has been replaced
   with `Seq.index s 0` in the Kadane specification, eliminating the
   `elements_bounded` precondition.

3. **Not imperative.** This is a pure functional implementation, not a Pulse
   (imperative) one. There is no ghost counter linked to the implementation.
   The complexity analysis (`dc_ops_count`) is a separate pure function that
   models the recurrence — it is not linked to actual execution.

4. **Empty-range case returns 0.** When `low >= high`,
   `find_maximum_subarray_dc` returns `(0, low, low)`. This means the
   "maximum subarray sum" of an empty range is 0, which is the sum of the
   empty subarray. For all-negative arrays, the non-empty result is negative,
   but the empty-range edge case is only reachable internally.

5. **Complexity bound constant is loose.** The bound
   `4n(log₂ n + 1)` uses a constant of 4 for proof simplicity. The actual
   D&C max subarray uses ≈ `n log₂ n` operations.

6. **Only considers non-empty subarrays (when input is non-empty).** Matches
   CLRS but differs from formulations allowing the empty subarray.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Operations | O(n log n) = 4n(⌈log₂ n⌉ + 1) | ❌ Separate recurrence | Upper bound only |

The complexity is **not linked** to the implementation — `dc_ops_count` is a
separate pure function modeling the recurrence. The proof that
`dc_ops_count n ≤ 4n(log₂ n + 1)` is via induction on `n` using the Master
Theorem (case 2).

## Proof Structure

The correctness proof has three layers:

1. **Crossing subarrays**: `lemma_crossing_left_sum` and
   `lemma_crossing_right_sum` prove that the left/right scans compute actual
   `sum_range` values. `lemma_crossing_sum_correct` combines them.

2. **Recursive correctness**: `lemma_dc_sum_correct` proves by induction that
   the returned sum matches `sum_range` for the returned range.

3. **Optimality**: `lemma_dc_optimal` proves by induction that the D&C result
   is ≥ every subarray sum. The key insight: any subarray either lies entirely
   in the left half, entirely in the right half, or crosses the midpoint.

4. **Equivalence**: `dc_kadane_equivalence` uses the optimality of both
   algorithms — D&C is ≥ every sum_range, Kadane's `max_sub_sum` is ≥ every
   sum_range, and both achieve their bounds — to conclude they are equal.

## Files

| File | Role |
|------|------|
| `CLRS.Ch04.MaxSubarray.DivideConquer.fst` | Original monolith (to be cleaned up — see checklist) |
| `CLRS.Ch04.MaxSubarray.DivideConquer.Spec.fst` | Pure specification (same functions, extracted) |
| `CLRS.Ch04.MaxSubarray.DivideConquer.Complexity.fsti` | Complexity interface (`dc_ops_count`, bound) |
| `CLRS.Ch04.MaxSubarray.DivideConquer.Complexity.fst` | Complexity proofs (O(n log n) via Master Theorem) |
| `CLRS.Ch04.MaxSubarray.DivideConquer.Lemmas.fsti` | Lemma signatures (correctness, optimality, equivalence) |
| `CLRS.Ch04.MaxSubarray.DivideConquer.Lemmas.fst` | Lemma proofs |
| `CLRS.Ch04.MaxSubarray.Spec.fst` | Shared spec: `kadane_spec`, `sum_range`, `max_sub_sum`, etc. |
| `CLRS.Ch04.MaxSubarray.Lemmas.fst` | Kadane correctness lemmas (used in equivalence) |

## Checklist

Priority-ordered items to reach a fully proven, high-quality implementation:

- [x] Split monolith into Spec/Lemmas/Complexity per RUBRIC.md
- [x] Create `.fsti` interfaces for Lemmas and Complexity
- [x] Zero admits, zero assumes
- [x] Equivalence with Kadane holds unconditionally
- [x] O(n log n) complexity bound proven
- [x] **P1: Clean up monolith `DivideConquer.fst`.** Reduced to re-export
  the split modules. Removed dead code: `min_int` and
  `lemma_dc_equals_kadane`.
- [x] **P2: Remove dead code from shared Spec.fst.** `initial_min` and
  `elements_bounded` removed from `CLRS.Ch04.MaxSubarray.Spec.fst`.
