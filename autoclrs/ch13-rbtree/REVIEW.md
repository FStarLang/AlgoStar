# Chapter 13: Red-Black Trees — Review

**Last reviewed:** 2026-03-16
**Reviewed by:** Automated audit
**Build status:** ✅ All 12 modules verified (clean build, zero errors)
**Admits:** 0 across all files

---

## Executive Summary

This is a **high-quality, fully verified** implementation of CLRS Chapter 13
Red-Black Trees, covering §13.1–13.4 with two independent Pulse implementations
(Okasaki-style and CLRS-faithful), sharing a common pure specification.

**Strengths:**
- Zero admits, zero assumes across ~6,510 lines of F*/Pulse
- Three-tier API: low-level, validated (bundles invariants), complexity-aware
- Complete coverage: search, insert, delete, minimum, free
- CLRS Theorem 13.1 fully proven (height ≤ 2·lg(n+1))
- O(log n) complexity proven via ghost tick counters
- `valid_rbtree` slprop bundles BST + RB invariants for clean user API

**All prior review complaints have been addressed:**
- ✅ Deletion now fully implemented with zero-admit proofs
- ✅ Complexity bounds now in Pulse postconditions (not vacuous)
- ✅ `valid_rbtree` bundles invariants (no manual lemma tracking)

---

## Checklist

### P0 — Critical (all done)
- [x] RB-INSERT implemented and proven (Okasaki + CLRS)
- [x] RB-DELETE implemented and proven (Kahrs + CLRS)
- [x] `delete_is_rbtree` fully proven (zero admits)
- [x] `valid_rbtree` bundles BST + RB invariants in slprop
- [x] Theorem 13.1 (height bound) fully proven
- [x] O(log n) complexity bounds proven
- [x] Complexity-aware API with tick bounds in postconditions
- [x] `free_rbtree` / `free_valid_rbtree` for memory management

### P1 — Proof Optimization/Stabilization
- [x] Max fuel reduced: 12 → 5 (concrete examples now use fuel 1)
- [x] Max rlimit reduced: 100 → 30 (was 100 in CLRSSpec `clrs_del_mem`)
- [x] Concrete examples (`log2_floor_16`, `log2_floor_1024`) use fuel 1, rlimit 20
- [ ] Consider adding `--split_queries always` to remaining fuel-5 proofs for stability
- [ ] Profile verification times per-module to identify bottlenecks

### P2 — Documentation & Structure
- [x] Rubric compliance: all required files present (Spec, Lemmas, Complexity, Impl, .fsti)
- [x] README.md comprehensive and accurate
- [x] Review files updated to reflect current state
- [ ] Audit report (AUDIT_CH13.md) updated to remove stale admitted-lemma claim
- [ ] CLRS.Ch13.RBTree.Review.md and CLRSImpl.Review.md reference consolidated here

### P3 — Enhancements (deferred)
- [ ] Amortized rotation count analysis (CLRS: insert ≤ 2, delete ≤ 3 rotations)
- [ ] Generic key type (currently integer-only)
- [ ] Iterator / in-order traversal
- [ ] Separate `minimum_ticks` exposure for Okasaki impl

---

## File Inventory

| File | Lines | Role | Admits |
|------|------:|------|:------:|
| `CLRS.Ch13.RBTree.Spec.fst` | 308 | Pure spec: types, invariants, insert (Okasaki), delete (Kahrs) | 0 |
| `CLRS.Ch13.RBTree.Lemmas.fsti` | 220 | Lemma signatures | 0 |
| `CLRS.Ch13.RBTree.Lemmas.fst` | 1164 | Correctness proofs (Thm 13.1, preservation) | 0 |
| `CLRS.Ch13.RBTree.Complexity.fsti` | 98 | Tick counter signatures | 0 |
| `CLRS.Ch13.RBTree.Complexity.fst` | 293 | Complexity proofs | 0 |
| `CLRS.Ch13.RBTree.Impl.fsti` | 125 | Okasaki Pulse public API | 0 |
| `CLRS.Ch13.RBTree.Impl.fst` | 1322 | Okasaki Pulse implementation | 0 |
| `CLRS.Ch13.RBTree.CLRSSpec.fst` | 1206 | CLRS-style spec + proofs | 0 |
| `CLRS.Ch13.RBTree.CLRSComplexity.fsti` | 91 | CLRS tick counter signatures | 0 |
| `CLRS.Ch13.RBTree.CLRSComplexity.fst` | 198 | CLRS complexity proofs | 0 |
| `CLRS.Ch13.RBTree.CLRSImpl.fsti` | 136 | CLRS Pulse public API | 0 |
| `CLRS.Ch13.RBTree.CLRSImpl.fst` | 1349 | CLRS Pulse implementation | 0 |
| **Total** | **6510** | | **0** |

## Proof Resource Usage (after optimization)

| Metric | Max Value | Where |
|--------|-----------|-------|
| fuel | 5 | Lemmas.fst: balL/balR/fuse/del RB-invariant proofs |
| ifuel | 3 | Lemmas.fst: same proofs (3-level tree induction) |
| z3rlimit | 30 | Lemmas.fst, CLRSSpec.fst: delete proofs |

Previous maxima: fuel 12, rlimit 100. Reduced by adding explicit lemma calls
and using `assert_norm` for concrete normalization.

## Rubric Compliance

| Rubric Requirement | Status |
|--------------------|:------:|
| `Spec.fst` — Pure specification | ✅ |
| `Lemmas.fst` — Correctness proofs | ✅ |
| `Lemmas.fsti` — Lemma signatures | ✅ |
| `Complexity.fst` — Complexity proofs | ✅ |
| `Complexity.fsti` — Complexity interface | ✅ |
| `Impl.fst` — Pulse implementation | ✅ |
| `Impl.fsti` — Public Pulse interface | ✅ |
| Zero admits/assumes | ✅ |
| Functional correctness (Impl ↔ Spec linkage) | ✅ |
| Complexity bounds in Pulse postconditions | ✅ |

**Overall Grade: A** — Fully verified, rubric-compliant, proof-optimized

---

## Spec Validation (2026-03-17)

### Methodology

Following the spec-validation approach from [arXiv:2406.09757](https://arxiv.org/abs/2406.09757),
we wrote `CLRS.Ch13.RBTree.ImplTest.fst` to validate the `Impl.fsti` API on a
small concrete instance (insert keys 3, 1, 2 into empty tree; search; delete).

### Results

| Test | Status |
|------|:------:|
| Pure spec normalization (tree shapes, search, mem, delete) | ✅ zero admits |
| Pulse API test (new → insert → search → delete → free) | ✅ zero admits |
| Preconditions satisfiable | ✅ all verified |
| Postconditions precise (concrete outputs match expected) | ✅ all verified |

### Spec Strengthening

The initial review identified a gap: the `Impl.fsti` postconditions lacked
a direct connection between `search` and `mem`. The test relied on ad-hoc
`assert_norm` helpers for every search assertion. Strengthening addressed this:

1. **New lemmas** in `Lemmas.fsti`/`Lemmas.fst`:
   - `search_mem`: `is_bst t ∧ mem k t ⟹ search t k == Some k`
   - `search_not_mem`: `¬(mem k t) ⟹ search t k == None`
   - `search_correct`: Combined form requiring only `is_bst t`

2. **Stronger postconditions** in `Impl.fsti`:
   - `rb_search_v`: Adds `(mem k 'ft ==> result == Some k) ∧ (¬(mem k 'ft) ==> result == None)`
   - `rb_insert_v`: Adds `search (insert 'ft k) k == Some k`
   - `rb_delete_v`: Adds `search (delete 'ft k) k == None`
   - Same strengthening applied to complexity-aware API

3. **Improved test**: Same-key insert/search and delete/search patterns now
   require **zero helper lemmas** — the postconditions are self-sufficient.

### Spec Quality Assessment

- **Spec gap found and fixed**: Missing `search`↔`mem` connection in Lemmas.
  Postconditions now directly expose this relationship.
- **No remaining spec incompleteness**: All preconditions satisfiable,
  all postconditions uniquely determine outputs.
- **Duplicate insert**: `S.insert t k` when `mem k t` is an identity (proven
  by `insert_duplicate` lemma in Lemmas.fst); the test verifies this on concrete input.
- **Delete non-existing key**: `S.delete t 99` preserves all keys; verified on concrete input.

### Files Added/Modified

| File | Purpose |
|------|---------|
| `CLRS.Ch13.RBTree.Lemmas.fsti` | Added `search_mem`, `search_not_mem`, `search_correct` |
| `CLRS.Ch13.RBTree.Lemmas.fst` | Proofs for search correctness lemmas |
| `CLRS.Ch13.RBTree.Impl.fsti` | Strengthened postconditions for search/insert/delete |
| `CLRS.Ch13.RBTree.Impl.fst` | Updated proofs to call `search_correct` |
| `CLRS.Ch13.RBTree.ImplTest.fst` | Updated test leveraging stronger postconditions |
| `CLRS.Ch13.RBTree.ImplTest.md` | Updated documentation |

### Notable Finding

Both Okasaki and CLRS insert implementations produce valid RB trees but with
different colorings for the same input sequence (3, 1, 2). Okasaki's balance
produces Black children at the balanced node, while CLRS's rotation-based fixup
produces Red children. Both are correct; the difference is in how each algorithm
distributes colors during rebalancing.
