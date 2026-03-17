# Simultaneous Min and Max (CLRS §9.1) — Review

**Last reviewed:** 2026-03-17
**Build status:** ✅ All files verified (zero admits, zero assumes)
**Verification time:** ~18s for Impl.fst (the slowest file)

## Checklist

- [x] Rubric compliance: 7/7 required files present
- [x] Zero admits / zero assumes
- [x] Impl.fsti shows clear API with correctness + complexity postconditions
- [x] `find_minmax`: exact 2(n−1) comparisons (equality)
- [x] `find_minmax_pairs`: tight ⌊3(n−1)/2⌋ bound (CLRS Theorem 9.1)
- [x] Correctness: existence + universality for both min and max
- [x] Array is read-only (fractional permission `#p`)
- [x] Build: Impl files included in Makefile and verified
- [x] **Spec validation**: ImplTest.fst verified — postcondition is precise
  enough to determine exact output for concrete inputs (no admits/assumes)
- [ ] *(Stability)* `find_minmax_pairs` uses `--z3rlimit 500 --ifuel 3 --fuel 3` — consider
  reducing via proof restructuring
- [ ] *(Nice-to-have)* Consider returning indices alongside values

## Top-Level Signatures (`Impl.fsti`)

### `find_minmax` (simple scan — 2(n−1) comparisons)

```fstar
fn find_minmax (#p: perm) (a: array int) (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
  ...
returns result: minmax_result
ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
  pure (
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
    complexity_bounded_minmax cf (reveal c0) (SZ.v len))
```

### `find_minmax_pairs` (CLRS pair-processing — ⌊3(n−1)/2⌋ comparisons)

Same correctness postcondition, with `complexity_bounded_minmax_pairs` instead.

## What Is Proven

1. **Min correctness**: existence + universality.
2. **Max correctness**: existence + universality.
3. **Complexity**: `find_minmax` = exact 2(n−1); `find_minmax_pairs` ≤ ⌊3(n−1)/2⌋.

## Proof Stability

| File | Time | z3rlimit | Notes |
|------|------|----------|-------|
| SimultaneousMinMax.Spec.fst | <1s | default | |
| SimultaneousMinMax.Impl.fsti | <1s | default | |
| SimultaneousMinMax.Impl.fst | ~18s | 500 | `find_minmax_pairs` uses high fuel/ifuel |
| SimultaneousMinMax.Lemmas.* | <1s | — | Intentionally empty |
| SimultaneousMinMax.Complexity.* | <1s | — | Intentionally minimal |

**`find_minmax_pairs`** requires `--z3rlimit 500 --ifuel 3 --fuel 3`. This is
high but the proof is stable. The pair-processing loop has complex invariants
tracking tick counts across even/odd cases.

## Limitations

1. **No indices returned** — values only.
2. **`len >= 1`** — no empty array handling.
3. **`len == A.length a`** — cannot operate on subrange.

## Spec Validation (ImplTest)

The `ImplTest.fst` tests both `find_minmax` and `find_minmax_pairs` on
`[5, 2, 8]` and proves `min_val == 2` and `max_val == 8` from the
postcondition alone.

**Result:** ✅ PASS — No spec weaknesses found. Postcondition uniquely
determines both min and max for any concrete input.
