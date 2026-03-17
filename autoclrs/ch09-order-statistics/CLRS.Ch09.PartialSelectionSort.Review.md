# Partial Selection Sort — Review

**Last reviewed:** 2026-03-17
**Build status:** ✅ All files verified (zero admits, zero assumes)
**Verification time:** ~29s for Spec.fst (optimized from 317s)

## Checklist

- [x] Rubric compliance: 7/7 required files present (plus 2 supplementary)
- [x] Zero admits / zero assumes
- [x] Impl.fsti shows clear API with correctness + complexity postconditions
- [x] `find_min_index_from`: exact (len − start − 1) comparisons
- [x] `select`: O(nk) = k × (n−1) comparisons
- [x] Correctness: permutation + sorted_prefix + prefix_leq_suffix
- [x] Build: Impl files included in Makefile and verified
- [x] No duplicate top-level definitions between .fsti and .fst
- [x] Complexity module proves both simple and tight closed forms
- [x] Spec.fst verification optimized: 317s → 29s (set --fuel 4 on bottleneck lemmas)
- [x] **Spec validation**: ImplTest.fst verified — postcondition is precise
  enough to determine exact output, though requires `reveal_opaque` for the
  opaque `permutation` and a completeness lemma (no admits/assumes)
- [ ] *(Nice-to-have)* Unify `permutation` definition with Quickselect.Spec

## Top-Level Signatures (`Impl.fsti`)

### `find_min_index_from`

```fstar
fn find_min_index_from (#p: perm) (a: array int) (#s: Ghost.erased (Seq.seq int))
  (start: SZ.t) (len: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
  ...
returns min_idx: SZ.t
ensures exists* (cf: nat). A.pts_to a #p s ** GR.pts_to ctr cf **
  pure (
    is_min_in_range s min_idx start len /\
    cf - reveal c0 == len - start - 1)
```

### `select`

```fstar
fn select (a: array int) (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t) (k: SZ.t) (ctr: GR.ref nat) (#c0: erased nat)
  requires ... pure (n > 0 /\ k > 0 /\ k <= n)
returns result: int
ensures exists* s_final (cf: nat). A.pts_to a s_final ** GR.pts_to ctr cf **
  pure (
    permutation s0 s_final /\
    sorted_prefix s_final k /\
    prefix_leq_suffix s_final k /\
    result == Seq.index s_final (k - 1) /\
    complexity_bounded_select cf c0 n k)
```

## What Is Proven

1. **Functional correctness**: first k elements are the k smallest, sorted.
2. **Partition property**: prefix ≤ suffix.
3. **Complexity**: at most k × (n−1) comparisons.
4. **Tight model**: `2 * tight(n,k) == k * (2*n - k - 1)`, strictly better when k > 1.

## Proof Stability

| File | Time | z3rlimit | Notes |
|------|------|----------|-------|
| PartialSelectionSort.Spec.fst | ~29s | 20-100 | Optimized from 317s by setting --fuel 4 on remove_element_count_le/lt |
| PartialSelectionSort.Lemmas.fst | ~21s | 10-60 | Multiple #restart-solver sections |
| PartialSelectionSort.Impl.fst | ~11s | 20-50 | |
| PartialSelectionSort.Complexity.fst | <2s | 20 | |
| PartialSelectionSort.Complexity.Enhanced.fst | <2s | default | |
| PartialSelectionSort.Complexity.Test.fst | <2s | default | |

### Performance Notes

**`PartialSelectionSort.Spec.fst` at 317s is the critical bottleneck** for the
entire ch09 build. This file contains:
- `pure_sort` (insertion sort on sequences) + its properties
- `count_occ`, `count_lt`, `count_le` + many permutation invariance lemmas
- `select_spec` + partition property proofs

The Makefile disables `optimize_let_vc` and `fly_deps` for the entire chapter
because they break quantifier instantiation in `insert_sorted` within this file.
This affects ALL files in the chapter.

Potential optimizations:
1. Add targeted `#push-options` with higher z3rlimit to specific slow lemmas
2. Split the file into smaller modules (e.g., separate `PureSort`, `Counting`)
3. Use `#restart-solver` between independent proof sections
4. Make some definitions `opaque_to_smt` where not needed

## Limitations

1. **Not a CLRS algorithm** — custom selection-sort variant.
2. **O(nk) worst-case** — worse than quickselect for large k.
3. **k is 1-indexed** — unlike quickselect's 0-indexed k.
4. **Own permutation definition** — separate from Quickselect.Spec.permutation.

## Spec Validation (ImplTest)

The `ImplTest.fst` tests `select` on `[5, 2, 8]` with k=1, proving
`result == 2`. Because `permutation` is `[@@"opaque_to_smt"]`, the test
uses `reveal_opaque` and a `completeness_select_k1` lemma with count-based
reasoning to establish the result.

**Result:** ✅ PASS — The postcondition is precise but requires extra proof
effort due to the opaque permutation. Unlike Quickselect's postcondition
(which includes `result == select_spec s0 k`), PartialSelectionSort's
postcondition relies on the combination of `sorted_prefix +
prefix_leq_suffix + permutation` which is equivalent but harder to use
directly.
