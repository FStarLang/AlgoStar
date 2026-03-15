# Binary Search (CLRS §2.3, Exercise 2.3-5 / §4 D&C)

## Top-Level Signature

Here is the top-level signature proven about Binary Search in
`CLRS.Ch04.BinarySearch.Impl.fsti`:

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

### Parameters

* `a` is a read-only array of `int`, accessed with fractional permission
  `#p`. The ghost variable `s0` captures the contents of the array (which
  are not modified — the postcondition returns `A.pts_to a #p s0` unchanged).

* `len` is the number of elements to search, of type `SZ.t`.

* `key` is the integer value to search for.

* `ctr` is a **ghost counter** for counting comparisons. Initial value `c0`.

### Preconditions

* `SZ.v len == Seq.length s0`: Length parameter matches logical sequence.

* `Seq.length s0 <= A.length a`: Logical sequence fits within the physical array.

* `is_sorted s0`: The input array must be sorted.

### Postcondition

The function returns a `SZ.t` value `result` such that:

* `SZ.v result <= SZ.v len` — The result is in-bounds or equals `len`
  (sentinel for "not found").

* `SZ.v result < SZ.v len ==> Seq.index s0 (SZ.v result) == key` — If the
  result is a valid index, the element at that index equals the key (found).

* `SZ.v result == SZ.v len ==> forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= key`
  — If the result is `len`, the key is not in the array (not found).

* `complexity_bounded_log cf (reveal c0) (SZ.v len)` — At most
  `⌊log₂ n⌋ + 1` comparisons.

## Auxiliary Definitions

### `is_sorted` (from `CLRS.Ch04.BinarySearch.Spec`)

```fstar
let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j
```

Standard sorted predicate using strict `i < j` (equivalent to `i ≤ j` used in
`CLRS.Common.SortSpec.sorted`). This is a local definition rather than
reusing the common one.

### `log2f` (from `CLRS.Ch04.BinarySearch.Spec`)

```fstar
let rec log2f (n: int) : Tot nat (decreases (if n > 0 then n else 0)) =
  if Prims.op_LessThanOrEqual n 1 then 0
  else Prims.op_Addition 1 (log2f (Prims.op_Division n 2))
```

Floor of log base 2. `log2f(1) = 0`, `log2f(2) = 1`, `log2f(3) = 1`,
`log2f(4) = 2`, etc. Used to express the O(log n) comparison bound.

### `complexity_bounded_log` (from `CLRS.Ch04.BinarySearch.Spec`)

```fstar
let complexity_bounded_log (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= log2f n + 1
```

The total number of comparisons (`cf - c0`) is at most `⌊log₂ n⌋ + 1`. This
is the tight worst-case bound for binary search.

## What Is Proven

The postcondition provides a **complete correctness specification** for binary
search:

* **If found**: returns a valid index where the key resides.
* **If not found**: returns the sentinel value `len`, and proves the key does
  not appear anywhere in the array.

This is a **total correctness** proof — it covers both the found and not-found
cases exhaustively.

The complexity bound `⌊log₂ n⌋ + 1` is the **tight worst-case** for binary
search: each iteration halves the search range, and the `+1` accounts for the
initial comparison.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. ~~**`len > 0` precondition.**~~ **RESOLVED.** The implementation now
   accepts `len >= 0`. Searching an empty array trivially returns
   `len` (not found) with 0 comparisons.

2. **No guarantee of returning the *first* occurrence.** If the key appears
   multiple times, the specification only guarantees *some* valid index is
   returned. CLRS does not require this either, but applications needing the
   leftmost match would need a stronger postcondition.

3. ~~**Array is not modified, but the interface does not use fractional permissions
   on `a`.**~~ **RESOLVED.** The interface now accepts a fractional permission
   `#p`, allowing concurrent reads. The postcondition returns
   `A.pts_to a #p s0`.

4. **Local `is_sorted` definition.** The spec defines its own `is_sorted`
   rather than reusing `CLRS.Common.SortSpec.sorted`. The two are logically
   equivalent (`i < j` vs. `i <= j` — the reflexive case is trivial), but
   having two definitions can create friction when composing with other
   sorting algorithms.

5. **The `+1` in the bound may be loose for some inputs.** For `n = 1`, the
   bound is `log2f(1) + 1 = 0 + 1 = 1`, which is tight. For power-of-2
   sizes, the bound is exact. For other sizes, the floor may introduce slight
   looseness.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Comparisons | O(log n) = ⌊log₂ n⌋ + 1 | ✅ Ghost counter | Upper bound (tight worst-case) |

The complexity is **fully linked** to the imperative implementation: the ghost
counter `ctr` is incremented via `tick ctr` on each comparison in the loop,
and the postcondition directly constrains `cf - c0`.

## Proof Structure

The proof uses a while loop with invariants tracking:

1. **Search range**: `lo ≤ hi`, with the key (if present) guaranteed to lie in
   `[lo, hi)`.
2. **Exclusion**: all indices outside `[lo, hi)` are proven to not contain the
   key.
3. **Complexity budget**: `(vc - c0) + log2f(hi - lo) ≤ log2f(len)` — the
   comparisons spent so far plus the remaining budget does not exceed the
   total budget.

Two key lemmas in `CLRS.Ch04.BinarySearch.Lemmas`:

* `lemma_log2f_mono`: log2f is monotone — `a ≤ b ==> log2f a ≤ log2f b`.
* `lemma_log2f_step`: Halving reduces the log by at least 1:
  `new_range ≤ old_range/2 ==> log2f(new_range) + 1 ≤ log2f(old_range)`.

## Files

| File | Role |
|------|------|
| `CLRS.Ch04.BinarySearch.Impl.fsti` | Public interface (this signature) |
| `CLRS.Ch04.BinarySearch.Impl.fst` | Pulse implementation |
| `CLRS.Ch04.BinarySearch.Spec.fst` | `is_sorted`, `log2f`, `complexity_bounded_log` |
| `CLRS.Ch04.BinarySearch.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch04.BinarySearch.Lemmas.fst` | Lemma proofs (log2f monotonicity and halving) |
