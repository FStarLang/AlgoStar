# Audit Report: Chapter 12 — Binary Search Trees

**Scope:** `ch12-bst/` (8 files, 3 403 LOC total)  
**Date:** 2025-07-18  

---

## Executive Summary

Chapter 12 implements BST operations across two parallel representations:

1. **Array-based (Pulse):** `BST.fst`, `BST.Delete.fst`, `BST.Complexity.fst` — imperative, heap-manipulating code using `keys`/`valid` arrays with implicit `2*i+1`/`2*i+2` child indexing.
2. **Inductive (pure F\*):** `Spec.Complete.fst`, `Spec.fst`, `Spec.Complexity.fst`, `Insert.Spec.fst`, `Delete.Spec.fst` — algebraic `Leaf | Node left key right` data type with full functional specifications and proofs.

The **pure spec layer** is mature and well-proven: search soundness/completeness, insert validity preservation + key-set equality, delete validity preservation + key-set equality, inorder sorted, and O(h) complexity — all **without any `admit` or `assume`**.

The **array-based Pulse layer** is partially complete: search and insert are verified, but **delete is semantically broken** (marks node invalid, orphaning children). No `admit`/`assume` calls appear anywhere in the codebase.

---

## 1. CLRS Fidelity

### 1.1 Operations Implemented

| CLRS Operation | Pure Spec (Spec.Complete) | Array Pulse (BST.fst / Delete.fst) | Notes |
|---|---|---|---|
| TREE-SEARCH (§12.2) | ✅ `bst_search` (recursive) | ✅ `tree_search` (iterative while loop) | Both faithful to CLRS |
| TREE-MINIMUM (§12.2) | ✅ `bst_minimum` (recursive) | ✅ `tree_minimum` (iterative) | Faithful |
| TREE-MAXIMUM (§12.2) | ✅ `bst_maximum` (recursive) | ✅ `tree_maximum` (iterative) | Faithful |
| TREE-INSERT (§12.3) | ✅ `bst_insert` (recursive) | ✅ `tree_insert` (iterative) | CLRS uses trailing pointer; code uses find-empty-slot. Equivalent semantics. |
| TREE-DELETE (§12.3) | ✅ `bst_delete` (all 3 cases) | ⚠️ `tree_delete` (**broken**) | Pure spec is correct; Pulse version simply marks invalid in ALL cases |
| TREE-SUCCESSOR (§12.2) | ❌ Not implemented | ❌ Not implemented | CLRS defines this; requires parent pointers |
| TREE-PREDECESSOR (§12.2) | ❌ Not implemented | ❌ Not implemented | Symmetric to SUCCESSOR |
| TRANSPLANT (§12.3) | N/A (not needed for inductive) | ❌ Not implemented | CLRS helper for pointer-based delete |
| INORDER-TREE-WALK (§12.1) | ✅ `bst_inorder` | ❌ Not implemented | Only in pure spec |

### 1.2 Representation: Pointer-Based vs Array-Based

CLRS uses a **pointer-based** representation with explicit `left`, `right`, `p` (parent) fields. The implementation uses:

- **Pure spec:** Inductive `Node left key right` — no parent pointers. This is a standard functional encoding. TREE-SUCCESSOR is omitted because it requires parent pointers (lines 3–7 of CLRS walk up via `x.p`).
- **Array Pulse:** Implicit heap layout (`2*i+1`, `2*i+2`). This is closer to a complete binary tree array than CLRS's pointer structure. Parent is computable as `(i-1)/2` but unused. **This design choice makes TRANSPLANT impossible** since you cannot rewire subtrees — child positions are fixed by index arithmetic.

**Key issue:** The array layout is fundamentally incompatible with CLRS's pointer-based TREE-DELETE, which relies on TRANSPLANT to rewire parent–child links. The pure spec correctly uses the "find successor, copy key, recursively delete successor" approach from CLRS, but the Pulse code cannot implement the structural rearrangement.

### 1.3 Delete Case Analysis

**CLRS defines 4 cases (Figure 12.4):**
1. No left child → replace with right child
2. No right child → replace with left child
3. Two children, successor is right child → replace directly
4. Two children, successor is deeper → transplant successor, then replace

**Pure spec (`Spec.Complete.fst` lines 132–152):** ✅ Handles all 3 logical cases correctly:
- `Leaf, Leaf` → `Leaf` (case 1 when right is also NIL)
- `Leaf, _` → `right` (case 1)
- `_, Leaf` → `left` (case 2)
- `_, _` → find min of right, swap, recursively delete (cases 3+4 combined)

**Pulse (`BST.Delete.fst` lines 319–389):** ❌ **All 4 branches do the same thing:** `t.valid.(del_idx) <- false`. Cases 2–4 (which should move children up or swap with successor) are stubbed with comments saying "Simplified: just mark invalid." This **orphans children** — they remain in the array but become unreachable to future searches starting from root 0.

---

## 2. Specification Strength

### 2.1 BST Invariant

| Aspect | Rating | Details |
|---|---|---|
| **Pure BST validity** (`bst_valid`) | **Strong** | `Spec.Complete.fst:64–72`: Checks `all_less key (bst_inorder left)` ∧ `all_greater key (bst_inorder right)` recursively. This is the **global** BST property (not just local parent–child), which is stronger than the local version at `BST.fst:43–49`. |
| **Array BST property** (`bst_property_at`) | **Weak** | `BST.fst:43–49`: Only checks immediate children (local). `subtree_in_range` (lines 53–69) is the strong global version and is used in search but **not** in insert's postcondition. |
| **Inorder sorted** | **Strong** | `bst_inorder_sorted` (`Spec.Complete.fst:939–949`): Fully proven, no admits. |

### 2.2 Search Specifications

| Property | Rating | Location | Details |
|---|---|---|---|
| **Soundness** (found ⟹ key matches) | **Strong** | `Spec.fst:155–182` (pure), `BST.fst:329–333` (Pulse) | Both proven without admits. Pulse postcondition: `Some? result ⟹ keys[idx] == key`. |
| **Completeness** (not found ⟹ key absent) | **Strong** | `Spec.fst:190–299` (pure), `BST.fst:333` (Pulse) | Pure: `None? ⟹ ~(key_in_subtree ...)`. Pulse: same via `~(key_in_subtree ...)`. Requires `subtree_in_range` precondition. |
| **Search ↔ membership** | **Strong** | `Spec.Complete.fst:233–262` | `bst_search t k ⟺ mem k (bst_inorder t)` — the gold standard for search correctness. |

### 2.3 Insert Specifications

| Property | Rating | Location | Details |
|---|---|---|---|
| **BST preserved** | **Strong** | `Spec.Complete.fst:342–364` | `bst_valid t ⟹ bst_valid (bst_insert t k)`. Fully proven. |
| **Key added** | **Strong** | `Insert.Spec.fst:46–51` | `key_set(insert(t,k)) = key_set(t) ∪ {k}`. Proven via `FiniteSet` algebra. |
| **Search succeeds after insert** | **Strong** | `Spec.Complete.fst:396–406` | `bst_search (bst_insert t k) k = true`. |
| **Old keys preserved** (pure) | **Strong** | `Spec.fst:373–434` | `key_in_subtree old_keys ⟹ key_in_subtree new_keys` (for array representation). |
| **Pulse insert postcondition** | **Medium** | `BST.fst:467–480` | Proves `∃ idx. keys'[idx] == key ∧ valid'[idx] == true`, but does **not** prove BST property preserved on the array. No `subtree_in_range` in postcondition. |

### 2.4 Delete Specifications

| Property | Rating | Location | Details |
|---|---|---|---|
| **BST preserved** (pure) | **Strong** | `Spec.Complete.fst:788–842` | `bst_valid t ⟹ bst_valid (bst_delete t k)`. Fully proven. |
| **Key removed** (pure) | **Strong** | `Delete.Spec.fst:90–95` | `key_set(delete(t,k)) = key_set(t) \ {k}`. Proven via `FiniteSet`. |
| **Pulse delete postcondition** | **Weak** | `BST.Delete.fst:306–317` | Only proves `valid'[del_idx] == false` and `keys' == keys`. Does **not** prove BST property preserved (and indeed it isn't — orphaned children break it). |

### 2.5 Summary Ratings

| Operation | Pure Spec | Pulse Implementation |
|---|---|---|
| Search | **Strong** | **Strong** |
| Insert | **Strong** | **Medium** (no BST invariant in post) |
| Delete | **Strong** | **Weak** (semantically incorrect) |
| Minimum/Maximum | **Strong** | **Strong** (verified, no admits) |

---

## 3. Complexity Analysis

### 3.1 Pure Inductive Complexity (`Spec.Complexity.fst`)

| Operation | Tick Function | Bound Proven | Rating |
|---|---|---|---|
| Search | `bst_search_ticks` | `≤ bst_height t` ✅ | **Strong** |
| Minimum | `bst_minimum_ticks` | `≤ bst_height t` ✅ | **Strong** |
| Maximum | `bst_maximum_ticks` | `≤ bst_height t` ✅ | **Strong** |
| Insert | `bst_insert_ticks` | `≤ bst_height t` ✅ | **Strong** |
| Delete | `bst_delete_ticks` | `≤ 4h + 1` ✅ | **Strong** |
| Delete minimum | `delete_minimum_bounded` | `≤ 2h` (requires `bst_valid`) ✅ | **Strong** |

All bounds are proven without `admit`/`assume`. The delete bound of `4h + 1` is conservative but correct. The comment on line 254 mentions "admit this lemma" but this refers to an **earlier version** — the actual code at lines 258–279 is a fully proven recursive lemma with `requires bst_valid t`.

### 3.2 Array Complexity (`BST.Complexity.fst`)

Proves structural properties:
- `tree_height cap = log2_floor cap` (line 46–47)
- `node_depth i ≤ tree_height cap` for all `i < cap` (line 81–84)
- `search_complexity_bound`: all nodes within height `h = ⌊log₂(cap)⌋` (line 101–110)

**Limitation:** This only proves that the **array structure** has depth ≤ log₂(cap). It does **not** connect this to actual operation costs (no ghost ticks in the Pulse search/insert/delete loops). The Pulse `tree_search` loop has no tick counter; complexity is structural only.

### 3.3 Ghost Tick Usage

**No ghost ticks are used anywhere in the Pulse code.** The complexity proofs are entirely on the pure inductive side. This is an acceptable design choice — the pure spec serves as the reference for algorithmic complexity, and the Pulse code is linked to the spec conceptually but not mechanically.

---

## 4. Code Quality

### 4.1 Duplication

| Duplicated Definition | Files Where It Appears | Lines |
|---|---|---|
| `child_indices_fit` | `BST.fst:15–24`, `Spec.fst:12–25`, `Delete.fst:47–56` | 3× |
| `bst` type (array) | `BST.fst:35–39`, `Delete.fst:59–64` | 2× |
| `subtree_in_range` | `BST.fst:53–69`, `Spec.fst:28–43` | 2× |
| `key_in_subtree` | `BST.fst:72–83`, `Spec.fst:46–57` | 2× |
| `lemma_key_in_bounded_subtree` | `BST.fst:86–109`, `Spec.fst:60–78` | 2× |
| `lemma_key_not_in_right_if_less` | `BST.fst:112–141`, `Spec.fst:81–104` | 2× |
| `lemma_key_not_in_left_if_greater` | `BST.fst:144–170`, `Spec.fst:107–130` | 2× |
| `list_to_set` | `Insert.Spec.fst:18–19`, `Delete.Spec.fst:16–17` | 2× |
| `key_set` | `Insert.Spec.fst:21–22`, `Delete.Spec.fst:19–20` | 2× |
| `lemma_list_to_set_mem` | `Insert.Spec.fst:24–27`, `Delete.Spec.fst:22–25` | 2× |
| `lemma_list_to_set_append` | `Insert.Spec.fst:29–33`, `Delete.Spec.fst:27–31` | 2× |
| `lemma_list_to_set_singleton` | `Insert.Spec.fst:35–37`, `Delete.Spec.fst:33–35` | 2× |

**~250 lines of duplicated code.** The `Spec.fst` file copies definitions from `BST.fst` because F\* modules with `#lang-pulse` can't be easily opened from pure modules. The `Insert.Spec.fst` and `Delete.Spec.fst` duplicate `list_to_set` / `key_set` / helpers because they were developed independently.

**Recommendation:** Extract shared definitions into a common module (e.g., `CLRS.Ch12.BST.Common.fst`) that both Pulse and pure modules can import.

### 4.2 Dead / Unused Code

- `BST.fst:43–49`: `bst_property_at` — the **local** BST property predicate is defined but never used anywhere; `subtree_in_range` superseded it.
- `BST.fst:173–180`: Comment block referencing removed admits — cleanup artifact, harmless.
- `Delete.fst:395–514`: `tree_delete_key` duplicates the search logic already in `BST.fst:tree_search` instead of calling it. This is ~120 lines of redundant search code.

### 4.3 Module Organization

The 8 files could be consolidated:

| Current | Proposed |
|---|---|
| `BST.fst` + `BST.Delete.fst` | `BST.fst` (all Pulse implementations) |
| `Spec.fst` + `Spec.Complete.fst` | `Spec.fst` (all pure spec + proofs) |
| `Insert.Spec.fst` + `Delete.Spec.fst` | `Spec.KeySet.fst` (key-set theorems) |
| `Spec.Complexity.fst` + `BST.Complexity.fst` | `Complexity.fst` (both pure + array) |

This would reduce from 8 files to 4 and eliminate most duplication.

---

## 5. Proof Quality — Admits and Assumes

### 5.1 `admit` Usage

**There are ZERO `admit()` calls in the entire ch12-bst codebase.**

The word "admit" appears only in **comments**:
- `BST.fst:173` — documents that earlier admitted lemmas were removed
- `BST.Delete.fst:32,35,36,277,284` — documents design decisions in comments
- `Spec.Complexity.fst:254` — **misleading comment** says "we admit this lemma" but the actual code at lines 258–279 is a fully proven `let rec` with `requires bst_valid t`
- `Insert.Spec.fst:9`, `Delete.Spec.fst:9` — documents "zero admits"

### 5.2 `assume` Usage

**There are ZERO `assume` calls in the entire ch12-bst codebase.**

### 5.3 `assert False` Usage

- `Delete.Spec.fst:106` — In the `Leaf` branch of `delete_key_set_lemma`: the precondition requires `bst_search t k = true` but `bst_search Leaf k = false`, so `assert False` is **logically valid** (contradiction discharge). ✅
- `Delete.Spec.fst:346` — In the `None` branch of `bst_minimum right` when right is a `Node`: contradiction since `bst_minimum_exists` proves `Some?`. ✅

Both uses are sound — they discharge impossible branches.

### 5.4 Z3 Resource Limits

- `Delete.Spec.fst:87`: `--z3rlimit 100 --fuel 1 --ifuel 1` for `delete_key_set_lemma`
- `Insert.Spec.fst:43`: `--z3rlimit 100 --fuel 1 --ifuel 1` for `insert_key_set_lemma`
- `Spec.Complete.fst:903`: `--z3rlimit 20` for `lemma_sorted_concat`

These are reasonable; rlimit 100 is moderate for FiniteSet-heavy proofs.

---

## 6. Documentation & Comments

### 6.1 Accuracy

| Claim | Location | Accurate? |
|---|---|---|
| "Main lemma verified with zero admits" | `Insert.Spec.fst:9` | ✅ Correct |
| "Main lemma verified with zero admits" | `Delete.Spec.fst:9` | ✅ Correct |
| "TREE-MINIMUM and TREE-MAXIMUM: Fully verified (no admits)" | `Delete.fst:35` | ✅ Correct |
| "TREE-DELETE: Uses admits for complex structural proofs" | `Delete.fst:36` | ❌ **Misleading** — there are no admits, but delete is semantically broken (just marks invalid) |
| "we admit this lemma" | `Spec.Complexity.fst:254` | ❌ **Stale comment** — the actual code below is fully proven |
| "Several lemmas with admits were removed" | `BST.fst:173` | ✅ Accurate historical note |
| "Simplified: just mark invalid" | `Delete.fst:351,359,380` | ⚠️ Accurate description but understates severity — should say "INCOMPLETE: orphans children, violates BST" |

### 6.2 CLRS Cross-References

Good: Most functions reference the correct CLRS section number (§12.1, §12.2, §12.3).  
Good: `Delete.fst` includes CLRS pseudocode in comments for TREE-MINIMUM and TREE-MAXIMUM.  
Missing: No cross-reference to CLRS Theorem 12.2 (O(h) for queries) or Theorem 12.3 (O(h) for insert/delete).

### 6.3 Snippet Markers

36 `SNIPPET_START`/`SNIPPET_END` pairs across 6 files — suggests integration with documentation tooling. All markers appear well-placed around key definitions and theorems.

---

## 7. Task List

### P0 — Critical (Correctness)

- [ ] **Fix Pulse `tree_delete` two-children case** (`Delete.fst:364–389`): Currently marks node invalid, orphaning both children. Must implement successor-swap approach: (1) call `tree_minimum` on right subtree, (2) copy successor key to `del_idx`, (3) recursively delete successor position. This is the most critical gap in Ch12.
- [ ] **Fix Pulse `tree_delete` one-child cases** (`Delete.fst:348–363`): Cases 2 and 3 mark the node invalid but do not promote the child. For the array representation, the child subtree remains at its position — consider either moving the subtree up or switching to a different in-place approach.
- [ ] **Fix stale comment** (`Spec.Complexity.fst:254`): Says "we admit this lemma" but code is fully proven. Change to "This lemma is proven by induction with bst_valid."

### P1 — High (Specification Gaps)

- [ ] **Add BST invariant to Pulse `tree_insert` postcondition** (`BST.fst:467–480`): Currently only proves key exists at some index. Should additionally prove `subtree_in_range keys' valid' cap 0 lo' hi'` is maintained.
- [ ] **Connect pure spec to Pulse via refinement** : Prove that the Pulse `tree_search` / `tree_insert` operations refine the pure `bst_search` / `bst_insert` on the abstract inductive tree extracted from the array. This would close the gap between the strong pure proofs and the Pulse implementations.
- [ ] **Add Pulse `tree_delete` postcondition for BST preservation**: Once delete is fixed, the postcondition should guarantee the BST invariant, not just `valid'[del_idx] == false`.

### P2 — Medium (Code Quality)

- [ ] **Eliminate duplication of `child_indices_fit`** : Extract to a shared module used by `BST.fst`, `Spec.fst`, and `Delete.fst`.
- [ ] **Eliminate duplication of `list_to_set` / `key_set` / helpers** : Create `CLRS.Ch12.BST.KeySet.fst` shared by `Insert.Spec.fst` and `Delete.Spec.fst` (~30 lines duplicated).
- [ ] **Eliminate duplication of array BST predicates** : `subtree_in_range`, `key_in_subtree`, and 3 associated lemmas are duplicated between `BST.fst` and `Spec.fst`. Extract to common module.
- [ ] **Remove dead code `bst_property_at`** (`BST.fst:43–49`): Unused local BST predicate superseded by `subtree_in_range`.
- [ ] **Deduplicate search logic in `tree_delete_key`** (`Delete.fst:440–514`): Reuse `tree_search` from `BST.fst` instead of reimplementing the search loop.
- [ ] **Remove duplicate `bst` type definition** (`Delete.fst:59–64`): Import from `BST.fst` instead.

### P3 — Low (Completeness / Polish)

- [ ] **Implement TREE-SUCCESSOR** : CLRS §12.2 defines this; it requires parent pointers (or the array parent formula `(i-1)/2`). Consider implementing for the array representation.
- [ ] **Implement TREE-PREDECESSOR** : Symmetric to SUCCESSOR.
- [ ] **Implement INORDER-TREE-WALK for Pulse** : The array representation has no imperative inorder walk.
- [ ] **Add ghost ticks to Pulse loops** : Currently complexity is only proven on the pure side. Adding a ghost tick counter to `tree_search`'s while loop would mechanically connect the O(h) bound to the imperative code.
- [ ] **Fix misleading comment in `Delete.fst:36`** : "TREE-DELETE: Uses admits for complex structural proofs" — there are no admits; the issue is semantic incorrectness, not proof gaps.
- [ ] **Add CLRS theorem cross-references** : Cite Theorem 12.2 and 12.3 in the complexity modules.
- [ ] **Consider tighter delete bound** : The `4h + 1` bound in `Spec.Complexity.fst:304` could potentially be tightened to `3h + 1` by observing that finding the successor and deleting it share the same right-subtree path.

---

## Appendix: File Summary

| File | LOC | Role | Admits | Key Theorems |
|---|---|---|---|---|
| `CLRS.Ch12.BST.fst` | 552 | Pulse search + insert | 0 | `tree_search` sound+complete, `tree_insert` |
| `CLRS.Ch12.BST.Spec.fst` | 468 | Pure search spec + proofs | 0 | `pure_search_sound`, `pure_search_complete`, `pure_insert_sound`, `pure_insert_complete` |
| `CLRS.Ch12.BST.Spec.Complete.fst` | 949 | Full pure BST spec | 0 | `bst_search_correct`, `bst_insert_valid`, `bst_delete_valid`, `bst_inorder_sorted` |
| `CLRS.Ch12.BST.Spec.Complexity.fst` | 348 | Pure O(h) bounds | 0 | `search_ticks_bounded`, `insert_ticks_bounded`, `delete_ticks_bounded` |
| `CLRS.Ch12.BST.Insert.Spec.fst` | 98 | Insert key-set theorem | 0 | `insert_key_set_lemma`, `theorem_insert_preserves_bst` |
| `CLRS.Ch12.BST.Delete.fst` | 514 | Pulse min/max/delete | 0 | `tree_minimum`, `tree_maximum` (verified); `tree_delete` (**broken**) |
| `CLRS.Ch12.BST.Delete.Spec.fst` | 349 | Delete key-set theorem | 0 | `delete_key_set_lemma` |
| `CLRS.Ch12.BST.Complexity.fst` | 125 | Array structural bounds | 0 | `search_complexity_bound`, `node_depth_bounded` |
| **Total** | **3 403** | | **0** | |
