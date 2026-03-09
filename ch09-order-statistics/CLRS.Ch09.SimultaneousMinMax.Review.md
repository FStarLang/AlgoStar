# Simultaneous Min and Max (CLRS §9.1)

## Top-Level Signatures

Here are the top-level signatures proven about `find_minmax` and
`find_minmax_pairs` in `CLRS.Ch09.SimultaneousMinMax.Impl.fsti`:

### `find_minmax` (simple scan)

```fstar
fn find_minmax
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len >= 1 /\
      SZ.v len == A.length a
    )
  returns result: minmax_result
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
      complexity_bounded_minmax cf (reveal c0) (SZ.v len)
    )
```

### `find_minmax_pairs` (pair-processing, CLRS optimal)

```fstar
fn find_minmax_pairs
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len >= 1 /\
      SZ.v len == A.length a
    )
  returns result: minmax_result
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
      complexity_bounded_minmax_pairs cf (reveal c0) (SZ.v len)
    )
```

### Parameters

* `a` is an array of `int` borrowed read-only via fractional permission `#p`.

* `len` is the number of elements, of type `SZ.t`.

* `ctr` is a ghost counter for comparison counting.

* The return type is `minmax_result`, a record with `min_val` and `max_val`
  fields.

### Preconditions

* `SZ.v len == Seq.length s0`: Length matches.
* `SZ.v len >= 1`: Non-empty array.
* `SZ.v len == A.length a`: Logical and physical lengths agree.

### Postconditions (identical for both functions except complexity)

* `exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val` —
  The minimum exists in the array.

* `forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k` —
  The minimum is ≤ every element.

* `exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val` —
  The maximum exists in the array.

* `forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k` —
  The maximum is ≥ every element.

* Complexity bound (differs between the two algorithms — see below).

## Auxiliary Definitions

### `minmax_result` (from `CLRS.Ch09.SimultaneousMinMax.Spec`)

```fstar
noeq
type minmax_result = {
  min_val: int;
  max_val: int;
}
```

### `complexity_bounded_minmax` (from `CLRS.Ch09.SimultaneousMinMax.Spec`)

```fstar
/// Simple scan: exactly 2(n-1) comparisons
let complexity_bounded_minmax (cf c0 n: nat) : prop =
  n >= 1 /\
  cf >= c0 /\
  cf - c0 == op_Multiply 2 (n - 1)
```

The simple scan compares each element against both the current min and max:
exactly 2(n−1) comparisons. This is an **exact** count (equality).

### `complexity_bounded_minmax_pairs` (from `CLRS.Ch09.SimultaneousMinMax.Spec`)

```fstar
/// Pair-processing: at most ⌊3n/2⌋ comparisons (expressed without division)
let complexity_bounded_minmax_pairs (cf c0 n: nat) : prop =
  n >= 1 /\
  cf >= c0 /\
  op_Multiply 2 (cf - c0) <= op_Multiply 3 n
```

The pair-processing algorithm from CLRS §9.1 processes elements in pairs: first
compare the pair against each other (1 comparison), then compare the smaller
against the current min and the larger against the current max (2 comparisons) —
3 comparisons per pair, giving ⌊3n/2⌋ total. The bound is expressed as
`2 * (cf - c0) <= 3 * n` to avoid integer division. This is an **upper bound**.

## What Is Proven

Both functions prove the **strongest possible correctness specification**: the
returned min and max values exist in the array and are globally optimal.

The key contribution is proving two **different complexity bounds** for the
same correctness property:

1. `find_minmax`: 2(n−1) comparisons — the naïve approach.
2. `find_minmax_pairs`: ⌊3n/2⌋ comparisons — the CLRS-optimal algorithm.

For large n, ⌊3n/2⌋ < 2(n−1), so `find_minmax_pairs` is strictly better.

**Zero admits, zero assumes.** All proof obligations are mechanically discharged
by F\* and Z3.

## Specification Gaps and Limitations

1. **`len >= 1` precondition.** Same as MinMax — no handling of empty arrays.

2. **`len == A.length a` strictness.** Cannot operate on array prefixes.

3. **Pair-processing bound is an upper bound, not exact.** The simple scan
   proves an exact count (`==`), but the pair-processing algorithm proves only
   `2 * (cf - c0) <= 3 * n`. The exact count is ⌊3(n−1)/2⌋ for odd n and
   3(n−2)/2 + 1 for even n; the specification slightly overapproximates by
   using `3n` instead of `3(n-1)`.

4. **No index returned.** The functions return values but not the indices at
   which the min and max occur.

## Complexity

| Algorithm | Bound | Linked? | Exact? |
|-----------|-------|---------|--------|
| `find_minmax` | 2(n−1) | ✅ Ghost counter | ✅ Exact |
| `find_minmax_pairs` | ⌊3n/2⌋ | ✅ Ghost counter | Upper bound only |

Both complexities are **fully linked** to the imperative implementations via
ghost counters.

## Proof Structure

Correctness is proved directly in the implementation postconditions via loop
invariants. The `CLRS.Ch09.SimultaneousMinMax.Lemmas` module is intentionally
empty — the algorithms are simple enough that no separate lemmas are needed.

## Files

| File | Role |
|------|------|
| `CLRS.Ch09.SimultaneousMinMax.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch09.SimultaneousMinMax.Impl.fst` | Pulse implementation |
| `CLRS.Ch09.SimultaneousMinMax.Spec.fst` | `minmax_result`, complexity predicates |
| `CLRS.Ch09.SimultaneousMinMax.Complexity.fst` | Complexity module (intentionally minimal) |
| `CLRS.Ch09.SimultaneousMinMax.Lemmas.fsti` | Lemma signatures (empty) |
| `CLRS.Ch09.SimultaneousMinMax.Lemmas.fst` | Lemma proofs (empty) |
