# Minimum and Maximum (CLRS §9.1)

## Top-Level Signatures

Here are the top-level signatures proven about `find_minimum` and `find_maximum`
in `CLRS.Ch09.MinMax.Impl.fsti`:

### `find_minimum`

```fstar
fn find_minimum
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len > 0 /\
      SZ.v len == A.length a
    )
  returns min_val: int
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> min_val <= Seq.index s0 k) /\
      complexity_bounded_min cf (reveal c0) (SZ.v len)
    )
```

### `find_maximum`

```fstar
fn find_maximum
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len > 0 /\
      SZ.v len == A.length a
    )
  returns max_val: int
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> max_val >= Seq.index s0 k) /\
      complexity_bounded_max cf (reveal c0) (SZ.v len)
    )
```

### Parameters

* `a` is an array of `int` (mathematical, unbounded integers in F\*). The ghost
  variable `s0` captures the initial contents of the array.

* `#p: perm` — a fractional permission. The array is borrowed read-only; it is
  returned unchanged in the postcondition (`A.pts_to a #p s0`).

* `len` is the number of elements, of type `SZ.t` (machine-sized).

* `ctr` is a **ghost counter** — a ghost reference to a natural number used to
  count comparisons. The initial value is `c0`.

### Preconditions

* `SZ.v len == Seq.length s0`: The length parameter matches the logical sequence
  length.

* `SZ.v len > 0`: The array must be non-empty.

* `SZ.v len == A.length a`: The length parameter matches the physical array
  length.

### Postconditions

For `find_minimum`:

* `exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == min_val` — The
  returned value exists in the array.

* `forall (k:nat). k < Seq.length s0 ==> min_val <= Seq.index s0 k` — The
  returned value is ≤ every element (it is the minimum).

* `complexity_bounded_min cf (reveal c0) (SZ.v len)` — Exactly n−1 comparisons.

For `find_maximum`: symmetric, with `max_val >= Seq.index s0 k`.

## Auxiliary Definitions

### `complexity_bounded_min` / `complexity_bounded_max` (from `CLRS.Ch09.MinMax.Spec`)

```fstar
let complexity_bounded_min (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1

let complexity_bounded_max (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1
```

Both predicates state the **exact** number of comparisons: `cf - c0 == n - 1`.
This is not merely an upper bound — it is a tight equality. Any algorithm that
examines each element once must make exactly n−1 comparisons, which is the
information-theoretic lower bound for finding a minimum or maximum.

## What Is Proven

The postcondition is the **strongest possible functional correctness
specification** for minimum/maximum finding:

1. **Existence**: The returned value actually appears in the array.
2. **Optimality**: The returned value is ≤ (or ≥) every element in the array.
3. **Exact complexity**: Exactly n−1 comparisons — matching the CLRS §9.1
   lower bound.

The array is returned unchanged (read-only access via fractional permission `#p`).

**Zero admits, zero assumes.** All proof obligations are mechanically discharged
by F\* and Z3.

## Specification Gaps and Limitations

1. **`len > 0` precondition.** The implementation requires a non-empty array.
   The minimum/maximum of an empty array is undefined, so this is a natural
   precondition, but some designs return an `option` type instead.

2. **`len == A.length a` strictness.** Both functions require `len` to equal the
   physical array length. A more general version could operate on a prefix
   (`len <= A.length a`), as the insertion sort specification does.

3. **No index returned.** The functions return the min/max *value* but not the
   *index* at which it occurs. For some applications (e.g., selection sort), the
   index is needed.

4. **Identical complexity predicates.** `complexity_bounded_min` and
   `complexity_bounded_max` have identical definitions. They could be unified
   into a single predicate.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Comparisons | Θ(n) = n−1 | ✅ Ghost counter | ✅ Exact (equality, not just upper bound) |

The complexity is **fully linked** to the imperative implementation: the ghost
counter `ctr` is incremented inside the comparison loop. The postcondition
constrains `cf - c0 == n - 1` — an exact count, not merely an upper bound.

## Proof Structure

The algorithms are simple linear scans. Correctness is proved directly in the
implementation postconditions via loop invariants — no separate lemma modules are
needed. The `CLRS.Ch09.MinMax.Lemmas` module is intentionally empty.

## Files

| File | Role |
|------|------|
| `CLRS.Ch09.MinMax.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch09.MinMax.Impl.fst` | Pulse implementation |
| `CLRS.Ch09.MinMax.Spec.fst` | `complexity_bounded_min`, `complexity_bounded_max` |
| `CLRS.Ch09.MinMax.Complexity.fst` | Complexity module (intentionally minimal) |
| `CLRS.Ch09.MinMax.Lemmas.fsti` | Lemma signatures (empty — correctness proved inline) |
| `CLRS.Ch09.MinMax.Lemmas.fst` | Lemma proofs (empty) |
