# Quickselect (CLRS §9.2) — Review

**Last reviewed:** 2026-03-16
**Build status:** ✅ All files verified (zero admits, zero assumes)
**Verification time:** ~34s for Impl.fst (the slowest file)

## Checklist

- [x] Rubric compliance: 7/7 required files present
- [x] Zero admits / zero assumes
- [x] Impl.fsti shows clear API with correctness + complexity postconditions
- [x] `partition_in_range`: exact hi−lo−1 comparisons
- [x] `quickselect`: O(n²) worst-case via `qs_cost(n) ≤ n(n+1)/2`
- [x] Correctness: `result == select_spec s0 k` (strongest possible)
- [x] Partition property: left ≤ pivot ≤ right
- [x] Permutation preservation
- [x] Build: Impl files included in Makefile and verified
- [x] No duplicate top-level definitions between .fsti and .fst
- [ ] *(Nice-to-have)* Expected O(n) analysis for randomized pivot
- [ ] *(Nice-to-have)* Randomized pivot selection

## Top-Level Signatures (`Impl.fsti`)

### `partition_in_range`

```fstar
fn partition_in_range (a: A.array int) (#s0: Ghost.erased (Seq.seq int))
  (lo: SZ.t) (hi: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
  ...
returns pivot_pos: SZ.t
ensures exists* s1 (cf: nat). A.pts_to a s1 ** GR.pts_to ctr cf **
  pure (
    permutation s0 s1 /\ partition_ordered s1 lo pivot_pos hi /\
    unchanged_outside s0 s1 lo hi /\
    cf - reveal c0 == hi - lo - 1)
```

### `quickselect`

```fstar
fn quickselect (a: A.array int) (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t) (k: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
  ...
returns result: int
ensures exists* s_final (cf: nat). A.pts_to a s_final ** GR.pts_to ctr cf **
  pure (
    permutation s0 s_final /\
    result == Seq.index s_final k /\
    (forall i < k. s_final[i] <= result) /\
    (forall i > k. result <= s_final[i]) /\
    result == select_spec s0 k /\
    complexity_bounded_quickselect cf c0 n)
```

## What Is Proven

1. **Partition correctness** with exact comparison count.
2. **Selection correctness**: `result == select_spec s0 k`.
3. **Partition property**: array partitioned at position k.
4. **Worst-case complexity**: O(n²) via `qs_cost(n) = n(n+1)/2`.

## Proof Stability

| File | Time | z3rlimit | Notes |
|------|------|----------|-------|
| Quickselect.Spec.fst | <2s | default | |
| Quickselect.Impl.fsti | <2s | default | |
| Quickselect.Impl.fst | ~34s | 120/200 | partition_in_range=120, quickselect=200 |
| Quickselect.Lemmas.fst | ~7s | 20-80 | Several focused push-options blocks |
| Quickselect.Complexity.fst | <2s | default | Simple inductive proofs |

## Limitations

1. **Only worst-case O(n²)** — expected O(n) for randomized pivot not mechanized.
2. **Deterministic pivot** — always picks last element; adversarial inputs hit worst case.
3. **k is 0-indexed** — CLRS uses 1-indexed ranks.
