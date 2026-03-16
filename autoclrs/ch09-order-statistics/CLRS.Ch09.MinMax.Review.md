# Minimum and Maximum (CLRS §9.1) — Review

**Last reviewed:** 2026-03-16
**Build status:** ✅ All files verified (zero admits, zero assumes)
**Verification time:** <10s total

## Checklist

- [x] Rubric compliance: 7/7 required files present (Spec, Lemmas.fsti,
  Lemmas.fst, Complexity.fsti, Complexity.fst, Impl.fsti, Impl.fst)
- [x] Zero admits / zero assumes
- [x] Impl.fsti shows clear API with correctness + complexity postconditions
- [x] Complexity bound is exact (n−1 comparisons, equality not just upper bound)
- [x] Correctness: existence + universality for both min and max
- [x] Array is read-only (fractional permission `#p`)
- [x] Build: Impl files included in Makefile and verified
- [x] Impl.fsti has correct `open` statements for Pulse compatibility
- [ ] *(Nice-to-have)* Consider returning index alongside value
- [ ] *(Nice-to-have)* Consider `len <= A.length a` for subrange operation

## Top-Level Signatures (`Impl.fsti`)

### `find_minimum`

```fstar
fn find_minimum (#p: perm) (a: array int) (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
  pure (SZ.v len == Seq.length s0 /\ SZ.v len > 0 /\ SZ.v len == A.length a)
returns min_val: int
ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
  pure (
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == min_val) /\
    (forall (k:nat). k < Seq.length s0 ==> min_val <= Seq.index s0 k) /\
    complexity_bounded_min cf (reveal c0) (SZ.v len))
```

### `find_maximum`

Symmetric: replaces `<=` with `>=`, uses `complexity_bounded_max`.

## What Is Proven

1. **Existence**: The returned value appears in the array.
2. **Optimality**: The returned value is ≤ (or ≥) every element.
3. **Exact complexity**: `cf - c0 == n - 1` (tight equality, not just upper bound).

## Proof Stability

| File | Time | z3rlimit | Notes |
|------|------|----------|-------|
| MinMax.Spec.fst | <1s | default | Trivial predicates |
| MinMax.Impl.fsti | <1s | default | — |
| MinMax.Impl.fst | ~5s | 200 | Simple linear scans |
| MinMax.Lemmas.* | <1s | — | Intentionally empty |
| MinMax.Complexity.* | <1s | — | Intentionally minimal |

## Limitations

1. **`len > 0` precondition** — natural for min/max (undefined on empty arrays).
2. **No index returned** — `find_min_index_from` in PartialSelectionSort provides this.
3. **`len == A.length a`** — cannot operate on a subrange.
