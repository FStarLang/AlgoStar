# Chapter 12: Binary Search Trees -- Rubric Compliance

**Generated:** 2025-07-18  
**Updated:** 2025-07-19  
**Source files:** 20 `.fst`/`.fsti` files, ~5 800 LOC total  
**Layers:** BST.\* (pointer-based Pulse + pure spec) · BSTArray.\* (array-based Pulse)

---

## Current File Inventory

| # | File | LOC | Layer | Role |
|---|------|-----|-------|------|
| 1 | `CLRS.Ch12.BST.Spec.fst` | 949 | Pure spec | Full inductive BST: type, validity, search, insert, delete, inorder, correctness lemmas *(renamed from Spec.Complete)* |
| 2 | `CLRS.Ch12.BST.Complexity.fst` | ~190 | Pure spec | Lemma proofs: O(h) tick-counting bounds *(definitions moved to .fsti)* |
| 2i | `CLRS.Ch12.BST.Complexity.fsti` | ~105 | Pure spec | Transparent definitions (max, bst_height, tick functions) + lemma signatures |
| 3 | `CLRS.Ch12.BST.KeySet.fst` | 33 | Pure spec | Shared `list_to_set` / `key_set` helpers |
| 4 | `CLRS.Ch12.BST.Insert.Spec.fst` | 78 | Pure spec | `key_set(insert(t,k)) = key_set(t) ∪ {k}` theorem |
| 5 | `CLRS.Ch12.BST.Delete.Spec.fst` | 329 | Pure spec | `key_set(delete(t,k)) = key_set(t) \ {k}` theorem |
| 5a | `CLRS.Ch12.BST.Lemmas.fst` | ~80 | Pure spec | Unified re-export of correctness lemmas |
| 5b | `CLRS.Ch12.BST.Lemmas.fsti` | ~60 | Pure spec | Interface: key-set algebra, search correctness, validity, inorder |
| 6 | `CLRS.Ch12.BST.Impl.fst` | ~540 | Pointer Pulse | Pulse implementations *(renamed from BST.fst; types moved to .fsti)* |
| 6i | `CLRS.Ch12.BST.Impl.fsti` | ~97 | Pointer Pulse | Types (bst_node/bst_ptr), bst_subtree predicate, fn signatures |
| 7 | `CLRS.Ch12.BSTArray.Impl.fst` | ~660 | Array Pulse | Imperative search + insert + inorder *(renamed from BSTArray.fst; types moved to .fsti)* |
| 7i | `CLRS.Ch12.BSTArray.Impl.fsti` | ~100 | Array Pulse | Types (bst), predicates, fn signatures |
| 8 | `CLRS.Ch12.BSTArray.Delete.fst` | 805 | Array Pulse | min/max/successor/predecessor/delete |
| 9 | `CLRS.Ch12.BSTArray.Predicates.fst` | 571 | Array shared | `subtree_in_range`, `well_formed_bst`, preservation lemmas |
| 10 | `CLRS.Ch12.BSTArray.Spec.fst` | 344 | Array shared | Pure search over arrays + soundness/completeness |
| 11 | `CLRS.Ch12.BSTArray.Refinement.fst` | 249 | Array shared | `array_to_bst` abstraction + refinement proofs |
| 12 | `CLRS.Ch12.BSTArray.Complexity.fst` | ~100 | Array shared | Lemma proofs: structural bounds *(definitions moved to .fsti)* |
| 12i | `CLRS.Ch12.BSTArray.Complexity.fsti` | ~75 | Array shared | Transparent definitions (log2_floor, tree_height, node_depth) + bound signatures |
| 13 | `CLRS.Ch12.BSTArray.Lemmas.fst` | ~100 | Array shared | Unified re-export from Predicates + Refinement |
| 13i | `CLRS.Ch12.BSTArray.Lemmas.fsti` | ~50 | Array shared | Interface: validity/search/inorder refinement signatures |

---

## Rubric Compliance Matrix

The canonical rubric requires seven artefacts per algorithm. This chapter has **two implementation layers** (pointer-based BST.\* and array-based BSTArray.\*), so compliance is assessed for each.

### BST (Pointer-Based) -- `CLRS.Ch12.BST.*`

| Rubric Artefact | Required File | Status | Notes |
|-----------------|---------------|--------|-------|
| **Spec.fst** | `CLRS.Ch12.BST.Spec.fst` | ✅ | Renamed from `BST.Spec.Complete.fst` |
| **Lemmas.fst** | `CLRS.Ch12.BST.Lemmas.fst` | ✅ | Unified re-export |
| **Lemmas.fsti** | `CLRS.Ch12.BST.Lemmas.fsti` | ✅ | Interface |
| **Complexity.fst** | `CLRS.Ch12.BST.Complexity.fst` | ✅ | Lemma proofs (defs in .fsti) |
| **Complexity.fsti** | `CLRS.Ch12.BST.Complexity.fsti` | ✅ | Transparent defs + signatures |
| **Impl.fst** | `CLRS.Ch12.BST.Impl.fst` | ✅ | Renamed from `BST.fst`; types in .fsti |
| **Impl.fsti** | `CLRS.Ch12.BST.Impl.fsti` | ✅ | Pulse interface with types + fn sigs |

### BSTArray (Array-Based) -- `CLRS.Ch12.BSTArray.*`

| Rubric Artefact | Required File | Status | Notes |
|-----------------|---------------|--------|-------|
| **Spec.fst** | `CLRS.Ch12.BSTArray.Spec.fst` | ✅ | Pure search over arrays |
| **Lemmas.fst** | `CLRS.Ch12.BSTArray.Lemmas.fst` | ✅ | Unified re-export |
| **Lemmas.fsti** | `CLRS.Ch12.BSTArray.Lemmas.fsti` | ✅ | Interface |
| **Complexity.fst** | `CLRS.Ch12.BSTArray.Complexity.fst` | ✅ | Lemma proofs (defs in .fsti) |
| **Complexity.fsti** | `CLRS.Ch12.BSTArray.Complexity.fsti` | ✅ | Transparent defs + signatures |
| **Impl.fst** | `CLRS.Ch12.BSTArray.Impl.fst` | ✅ | Renamed from `BSTArray.fst`; types in .fsti |
| **Impl.fsti** | `CLRS.Ch12.BSTArray.Impl.fsti` | ✅ | Pulse interface with types + fn sigs |

### Cross-Cutting Concerns

| Aspect | Status | Details |
|--------|--------|---------|
| **Zero admits** | ✅ | No `admit()` calls in any file |
| **Zero assumes** | ✅ | No `assume` calls in any file |
| **Refinement proof** | ✅ | `BSTArray.Refinement.fst` connects array repr to pure inductive spec |
| **CLRS cross-references** | ✅ | Theorems 12.2 and 12.3 cited; §12.1-12.3 referenced |
| **All 20 files verified** | ✅ | `make -j1` succeeds with zero errors |

---

## Completeness Gaps (P2)

| # | Action | Details |
|---|--------|---------|
| 1 | Complete BSTArray `tree_delete` for 1-child and 2-child cases | Currently marks invalid, orphaning children |
| 2 | Add ghost ticks to BSTArray `tree_insert` | Only `tree_search` has ghost O(h) ticks |
| 3 | Add ghost ticks to BSTArray `tree_minimum`/`tree_maximum` | Straightforward |
| 4 | Connect BSTArray.Complexity to operation costs | Structural proof only |
| 5 | Consider tighter delete bound | Pure spec proves `4h+1`; could be `3h+1` |
