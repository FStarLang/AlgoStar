# Chapter 12: Binary Search Trees -- Rubric Compliance

**Generated:** 2025-07-18  
**Updated:** 2025-07-19  
**Source files:** 20 `.fst`/`.fsti` files, ~6 000 LOC total  
**Layers:** BST.\* (pointer-based Pulse + pure spec) · BSTArray.\* (array-based Pulse)

---

## Current File Inventory

| # | File | LOC | Layer | Role |
|---|------|-----|-------|------|
| 1 | `CLRS.Ch12.BST.Spec.fst` | 949 | Pure spec | Full inductive BST: type, validity, search, insert, delete, inorder, correctness lemmas |
| 2 | `CLRS.Ch12.BST.Complexity.fst` | ~190 | Pure spec | Lemma proofs: O(h) tick-counting bounds |
| 2i | `CLRS.Ch12.BST.Complexity.fsti` | ~115 | Pure spec | Transparent definitions (max, bst_height, tick functions) + lemma signatures |
| 3 | `CLRS.Ch12.BST.KeySet.fst` | 33 | Pure spec | Shared `list_to_set` / `key_set` helpers |
| 4 | `CLRS.Ch12.BST.Insert.Spec.fst` | 78 | Pure spec | `key_set(insert(t,k)) = key_set(t) ∪ {k}` theorem |
| 5 | `CLRS.Ch12.BST.Delete.Spec.fst` | 329 | Pure spec | `key_set(delete(t,k)) = key_set(t) \ {k}` theorem |
| 5a | `CLRS.Ch12.BST.Lemmas.fst` | ~80 | Pure spec | Unified re-export of correctness lemmas |
| 5b | `CLRS.Ch12.BST.Lemmas.fsti` | ~60 | Pure spec | Interface: key-set algebra, search correctness, validity, inorder |
| 6 | `CLRS.Ch12.BST.Impl.fst` | ~560 | Pointer Pulse | Pulse implementations with ghost tick counters linked to BST.Complexity |
| 6i | `CLRS.Ch12.BST.Impl.fsti` | ~105 | Pointer Pulse | Types, bst_subtree, fn signatures with `GR.ref nat` ticks |
| 7 | `CLRS.Ch12.BSTArray.Impl.fst` | ~680 | Array Pulse | Imperative search + insert + inorder with ghost tick counters linked to BSTArray.Complexity |
| 7i | `CLRS.Ch12.BSTArray.Impl.fsti` | ~210 | Array Pulse | Types, predicates, fn signatures with `GR.ref nat` ticks |
| 8 | `CLRS.Ch12.BSTArray.Delete.fst` | 805 | Array Pulse | min/max/successor/predecessor/delete |
| 9 | `CLRS.Ch12.BSTArray.Predicates.fst` | 571 | Array shared | `subtree_in_range`, `well_formed_bst`, preservation lemmas |
| 10 | `CLRS.Ch12.BSTArray.Spec.fst` | 344 | Array shared | Pure search over arrays + soundness/completeness |
| 11 | `CLRS.Ch12.BSTArray.Refinement.fst` | 249 | Array shared | `array_to_bst` abstraction + refinement proofs |
| 12 | `CLRS.Ch12.BSTArray.Complexity.fst` | ~100 | Array shared | Lemma proofs: structural bounds |
| 12i | `CLRS.Ch12.BSTArray.Complexity.fsti` | ~77 | Array shared | Transparent definitions (log2_floor, tree_height, node_depth) + bound signatures |
| 13 | `CLRS.Ch12.BSTArray.Lemmas.fst` | ~100 | Array shared | Unified re-export from Predicates + Refinement |
| 13i | `CLRS.Ch12.BSTArray.Lemmas.fsti` | ~50 | Array shared | Interface: validity/search/inorder refinement signatures |

---

## Complexity Linking

Each Pulse operation carries a `GhostReference.ref nat` tick counter whose postcondition
links directly to the complexity functions, establishing O(h) bounds.

### BST (Pointer-Based) -- Tick Postconditions

| Operation | Tick Function | Postcondition |
|-----------|---------------|---------------|
| `tree_search` | `bst_search_ticks` | `ticks == n + bst_search_ticks ft k` |
| `tree_minimum` | `bst_minimum_ticks` | `ticks == n + bst_minimum_ticks ft` |
| `tree_maximum` | `bst_maximum_ticks` | `ticks == n + bst_maximum_ticks ft` |
| `tree_insert` | `bst_insert_ticks` | `ticks == n + bst_insert_ticks ft k` |
| `tree_delete` | `bst_delete_ticks` | `ticks == n + bst_delete_ticks ft k` |

Combined with `search_ticks_bounded`, `insert_ticks_bounded`, `delete_ticks_bounded`
from `BST.Complexity`, these give **machine-checked O(h) bounds**.

### BSTArray (Array-Based) -- Tick Postconditions

| Operation | Bound | Postcondition |
|-----------|-------|---------------|
| `tree_search` | `tree_height(cap)` | `ticks - n <= tree_height(cap)` |
| `tree_insert` | `tree_height(cap)` | `ticks - n <= tree_height(cap)` |

Combined with `search_complexity_bound` from `BSTArray.Complexity`,
these give **machine-checked O(log cap) bounds** since `tree_height(cap) = log2_floor(cap)`.

---

## Rubric Compliance Matrix

### BST (Pointer-Based) -- `CLRS.Ch12.BST.*`

| Rubric Artefact | Required File | Status | Notes |
|-----------------|---------------|--------|-------|
| **Spec.fst** | `CLRS.Ch12.BST.Spec.fst` | ✅ | Renamed from `BST.Spec.Complete.fst` |
| **Lemmas.fst** | `CLRS.Ch12.BST.Lemmas.fst` | ✅ | Unified re-export |
| **Lemmas.fsti** | `CLRS.Ch12.BST.Lemmas.fsti` | ✅ | Interface |
| **Complexity.fst** | `CLRS.Ch12.BST.Complexity.fst` | ✅ | Lemma proofs; linked to Impl via ticks |
| **Complexity.fsti** | `CLRS.Ch12.BST.Complexity.fsti` | ✅ | Transparent defs + signatures |
| **Impl.fst** | `CLRS.Ch12.BST.Impl.fst` | ✅ | Ghost tick counters in all ops |
| **Impl.fsti** | `CLRS.Ch12.BST.Impl.fsti` | ✅ | Pulse interface with tick params |

### BSTArray (Array-Based) -- `CLRS.Ch12.BSTArray.*`

| Rubric Artefact | Required File | Status | Notes |
|-----------------|---------------|--------|-------|
| **Spec.fst** | `CLRS.Ch12.BSTArray.Spec.fst` | ✅ | Pure search over arrays |
| **Lemmas.fst** | `CLRS.Ch12.BSTArray.Lemmas.fst` | ✅ | Unified re-export |
| **Lemmas.fsti** | `CLRS.Ch12.BSTArray.Lemmas.fsti` | ✅ | Interface |
| **Complexity.fst** | `CLRS.Ch12.BSTArray.Complexity.fst` | ✅ | Lemma proofs; linked to Impl via ticks |
| **Complexity.fsti** | `CLRS.Ch12.BSTArray.Complexity.fsti` | ✅ | Transparent defs + signatures |
| **Impl.fst** | `CLRS.Ch12.BSTArray.Impl.fst` | ✅ | Ghost tick counters in search + insert |
| **Impl.fsti** | `CLRS.Ch12.BSTArray.Impl.fsti` | ✅ | Pulse interface with tick params |

### Cross-Cutting Concerns

| Aspect | Status | Details |
|--------|--------|---------|
| **Zero admits** | ✅ | No `admit()` calls in any file |
| **Zero assumes** | ✅ | No `assume` calls in any file |
| **Complexity linked** | ✅ | Ghost tick counters in Impl postconditions reference Complexity functions |
| **Refinement proof** | ✅ | `BSTArray.Refinement.fst` connects array repr to pure inductive spec |
| **CLRS cross-references** | ✅ | Theorems 12.2 and 12.3 cited; §12.1-12.3 referenced |
| **All 20 files verified** | ✅ | `make -j1` succeeds with zero errors |

---

## Proof Stability (updated 2026-03-16)

All solver settings reduced and verified on clean rebuild:
- **Max rlimit across all of ch12: 80** (was 300 in Predicates, 100 in FiniteSet proofs)
- **Max fuel: 2** everywhere (was fuel 3 in Predicates)
- No `restart_solver`, `retry`, or `quake` directives
- All 20 modules verify with zero errors

---

## Completeness Gaps (P2)

| # | Action | Details |
|---|--------|---------|
| 1 | Complete BSTArray `tree_delete` for 1-child and 2-child cases | Currently marks invalid, orphaning children |
| 2 | Add ghost ticks to BSTArray `tree_minimum`/`tree_maximum`/`tree_delete` in Delete.fst | Only search + insert have ticks currently |
| 3 | Consider tighter delete bound | Pure spec proves `4h+1`; could be `3h+1` |
