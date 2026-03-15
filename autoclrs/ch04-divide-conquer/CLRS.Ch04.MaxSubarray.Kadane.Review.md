# Kadane's Algorithm — Maximum Subarray (CLRS §4.1)

## Top-Level Signature

Here is the top-level signature proven about Kadane's algorithm in
`CLRS.Ch04.MaxSubarray.Kadane.fsti`:

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

### Parameters

* `a` is a read-only array of `int`, accessed with fractional permission
  `#p`. The ghost variable `s0` captures the contents (returned unchanged
  in the postcondition).

* `len` is the number of elements, of type `SZ.t`.

* `ctr` is a **ghost counter** for counting operations. Initial value `c0`.

### Preconditions

* `SZ.v len == Seq.length s0`: Length parameter matches logical sequence.

* `Seq.length s0 <= A.length a`: Logical sequence fits within the physical
  array.

* `SZ.v len > 0`: The array must be non-empty.

### Postcondition

The function returns an `int` value `result` such that:

* `result == max_subarray_spec s0` — The result exactly equals the
  specification function.

* `complexity_bounded_linear cf (reveal c0) (SZ.v len)` — Exactly `n`
  operations were performed.

## Auxiliary Definitions

### `max_subarray_spec` (from `CLRS.Ch04.MaxSubarray.Spec`)

```fstar
let max_subarray_spec (s: Seq.seq int) : Tot int =
  if Seq.length s = 0 then 0
  else kadane_spec s 0 0 (Seq.index s 0)
```

The top-level specification. For non-empty sequences, delegates to
`kadane_spec` starting at position 0 with `current_sum = 0` and
`best_sum = Seq.index s 0` (the first element).

### `kadane_spec` (from `CLRS.Ch04.MaxSubarray.Spec`)

```fstar
let rec kadane_spec (s: Seq.seq int) (i: nat) 
  (current_sum: int) (best_sum: int) : Pure int
  (requires i <= Seq.length s)
  (ensures fun _ -> True)
  (decreases (if i <= Seq.length s then Seq.length s - i else 0))
  =
  if i >= Seq.length s then best_sum
  else (
    let elem = Seq.index s i in
    let new_current = max_int elem (current_sum + elem) in
    let new_best = max_int best_sum new_current in
    kadane_spec s (i + 1) new_current new_best
  )
```

Pure recursive encoding of Kadane's algorithm. At each position `i`, it
decides whether to extend the current subarray or start fresh, and tracks the
best sum seen so far.

### `initial_min` (from `CLRS.Ch04.MaxSubarray.Spec`)

```fstar
let initial_min : int = -1000000000
```

A legacy sentinel value. No longer used by `max_subarray_spec`, which now
uses `Seq.index s 0` as the initial `best_sum`.

### `max_int` (from `CLRS.Ch04.MaxSubarray.Spec`)

```fstar
let max_int (a b: int) : Tot int = if a >= b then a else b
```

Standard integer maximum.

### `complexity_bounded_linear` (from `CLRS.Ch04.MaxSubarray.Kadane`)

```fstar
let complexity_bounded_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n
```

The operation count is **exactly** `n` — not just an upper bound. One tick
per array element.

### `sum_range` (from `CLRS.Ch04.MaxSubarray.Spec`)

```fstar
let rec sum_range (s: Seq.seq int) (i j: nat) : Pure int
  (requires i <= j /\ j <= Seq.length s)
  (ensures fun _ -> True)
  (decreases Prims.op_Subtraction j i)
  =
  if i >= j then 0
  else Seq.index s i + sum_range s (i + 1) j
```

Sum of elements in the half-open range `[i, j)`. Used in the optimality
theorems.

### `max_suffix_sum` (from `CLRS.Ch04.MaxSubarray.Spec`)

```fstar
let rec max_suffix_sum (s: Seq.seq int) (i: nat) : Pure int
  (requires i < Seq.length s) (ensures fun _ -> True) (decreases i) =
  if i = 0 then Seq.index s 0
  else max_int (Seq.index s i) (max_suffix_sum s (i - 1) + Seq.index s i)
```

Maximum sum of any non-empty contiguous subarray ending at position `i`.

### `max_sub_sum` (from `CLRS.Ch04.MaxSubarray.Spec`)

```fstar
let rec max_sub_sum (s: Seq.seq int) (i: nat) : Pure int
  (requires i < Seq.length s) (ensures fun _ -> True) (decreases i) =
  if i = 0 then Seq.index s 0
  else max_int (max_sub_sum s (i - 1)) (max_suffix_sum s i)
```

Maximum sum of any non-empty contiguous subarray in `s[0..i+1)`.

### ~~`elements_bounded`~~ (removed)

The `elements_bounded` predicate is no longer needed. By using
`Seq.index s 0` instead of `initial_min` as the initial `best_sum`,
all optimality theorems hold unconditionally for any integer sequence.

## What Is Proven

The postcondition `result == max_subarray_spec s0` proves that the imperative
Pulse implementation computes the exact same value as the pure specification.

The optimality theorems in `CLRS.Ch04.MaxSubarray.Lemmas` strengthen this:

* **`theorem_kadane_optimal`**: For any subarray `[i, j)`,
  `max_subarray_spec s >= sum_range s i j`. The result is at least as large
  as every contiguous subarray sum. **No `elements_bounded` precondition.**

* **`theorem_kadane_witness`**: There exist indices `i < j` such that
  `max_subarray_spec s == sum_range s i j`. The result is achieved by some
  contiguous subarray. **No `elements_bounded` precondition.**

Together, these prove that `max_subarray_spec` computes the **unique maximum
non-empty subarray sum** — the same quantity that CLRS §4.1 targets — for
**any** integer sequence.

The complexity bound `cf - c0 == n` is **exact** (not just an upper bound).

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. ~~**`initial_min` sentinel is not −∞.**~~ **RESOLVED.** The specification
   now uses `Seq.index s 0` (the first element) as the initial `best_sum`.
   The optimality theorems hold unconditionally for any integer sequence.

2. ~~**`elements_bounded` precondition not in the interface.**~~ **RESOLVED.**
   The `elements_bounded` precondition has been eliminated entirely. The
   full chain (imperative result = spec = true optimum) now works
   unconditionally.

3. **Only non-empty subarrays.** The specification considers non-empty
   subarrays only (`max_suffix_sum` and `max_sub_sum` are defined for
   `i < Seq.length s`). The empty subarray (sum = 0) is never considered. For
   arrays of all-negative values, the result is the least-negative element,
   not 0. This matches CLRS's definition but differs from some formulations
   that allow the empty subarray.

4. **`len > 0` precondition.** Kadane's algorithm on an empty array should
   return 0 (or handle trivially), but the implementation requires `len > 0`.

5. ~~**Array is not modified, but full permission is required.**~~ **RESOLVED.**
   The interface now takes `A.pts_to a #p s0` with a fractional permission
   `#p`, allowing concurrent reads.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Operations | O(n) = exactly n | ✅ Ghost counter | ✅ Exact (cf − c0 == n) |

The complexity is **fully linked** and **exact**: the ghost counter `ctr` is
incremented once per loop iteration via `tick ctr`, and the postcondition
asserts `cf - c0 == n` (equality, not inequality).

## Proof Structure

The proof uses a single while loop with invariant:

* `kadane_spec s (SZ.v vi) vcur vbest == kadane_spec s 0 0 initial_min` —
  The remaining computation from position `vi` with accumulators `vcur` and
  `vbest` equals the full computation from the start.
* `vc == reveal c0 + SZ.v vi` — Exactly `i` ticks have been counted.

At loop exit, `vi == len`, so `kadane_spec s len vcur vbest == best_sum`,
and `vbest == max_subarray_spec s`.

The key lemmas in `CLRS.Ch04.MaxSubarray.Lemmas`:

* `lemma_kadane_correct`: Links `kadane_spec` to `max_sub_sum` — proves that
  running Kadane from position `i` with the correct accumulators produces
  `max_sub_sum s (n-1)`.
* `theorem_kadane_optimal`: `max_subarray_spec s >= sum_range s i j` for all
  valid `i, j`.
* `theorem_kadane_witness`: There exist `i, j` achieving the optimum.

## Files

| File | Role |
|------|------|
| `CLRS.Ch04.MaxSubarray.Kadane.fsti` | Public interface (this signature) |
| `CLRS.Ch04.MaxSubarray.Kadane.fst` | Pulse implementation + `complexity_bounded_linear` |
| `CLRS.Ch04.MaxSubarray.Spec.fst` | `kadane_spec`, `max_subarray_spec`, `sum_range`, `max_suffix_sum`, `max_sub_sum` |
| `CLRS.Ch04.MaxSubarray.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch04.MaxSubarray.Lemmas.fst` | Correctness and optimality proofs |
