# Chapter 12: Binary Search Trees — Rubric Compliance

**Generated:** 2025-07-18  
**Source files:** 12 `.fst` files, ~5 146 LOC total  
**Layers:** BST.\* (pointer-based Pulse + pure spec) · BSTArray.\* (array-based Pulse)

---

## Current File Inventory

| # | File | LOC | Layer | Role |
|---|------|-----|-------|------|
| 1 | `CLRS.Ch12.BST.Spec.Complete.fst` | 949 | Pure spec | Full inductive BST: type, validity, search, insert, delete, inorder, correctness lemmas |
| 2 | `CLRS.Ch12.BST.Spec.Complexity.fst` | 352 | Pure spec | O(h) tick-counting bounds for search, min, max, insert, delete |
| 3 | `CLRS.Ch12.BST.KeySet.fst` | 33 | Pure spec | Shared `list_to_set` / `key_set` helpers (used by Insert.Spec + Delete.Spec) |
| 4 | `CLRS.Ch12.BST.Insert.Spec.fst` | 78 | Pure spec | `key_set(insert(t,k)) = key_set(t) ∪ {k}` theorem |
| 5 | `CLRS.Ch12.BST.Delete.Spec.fst` | 329 | Pure spec | `key_set(delete(t,k)) = key_set(t) \ {k}` theorem |
| 6 | `CLRS.Ch12.BST.fst` | 580 | Pointer-based Pulse | `bst_node` with parent pointer, sep-logic `bst_subtree`, search/insert/delete/free linked to pure spec |
| 7 | `CLRS.Ch12.BSTArray.fst` | 721 | Array Pulse | Imperative search + insert + inorder walk with ghost O(h) ticks |
| 8 | `CLRS.Ch12.BSTArray.Delete.fst` | 805 | Array Pulse | min/max/successor/predecessor/delete (leaf case proven; 1-/2-child cases incomplete) |
| 9 | `CLRS.Ch12.BSTArray.Predicates.fst` | 571 | Array shared | `subtree_in_range`, `well_formed_bst`, frame/insert/delete preservation lemmas |
| 10 | `CLRS.Ch12.BSTArray.Spec.fst` | 344 | Array shared | Pure search over arrays + soundness/completeness proofs |
| 11 | `CLRS.Ch12.BSTArray.Refinement.fst` | 249 | Array shared | `array_to_bst` abstraction, inorder/validity/search refinement proofs |
| 12 | `CLRS.Ch12.BSTArray.Complexity.fst` | 135 | Array shared | `log2_floor`, `tree_height`, `node_depth ≤ tree_height` structural bounds |

---

## Algorithms Covered

### Pure Functional Spec (`BST.Spec.Complete`)

Inductive `bst = Leaf | Node left key right` — standard functional encoding.

| CLRS Operation | Function | Proven Properties |
|----------------|----------|-------------------|
| TREE-SEARCH §12.2 | `bst_search` | Soundness, completeness, `⟺ mem (bst_inorder)` |
| TREE-MINIMUM §12.2 | `bst_minimum` | Correctness, existence when non-Leaf |
| TREE-MAXIMUM §12.2 | `bst_maximum` | Symmetric to minimum |
| TREE-INSERT §12.3 | `bst_insert` | Validity preserved, `key_set` union, search succeeds after insert |
| TREE-DELETE §12.3 | `bst_delete` | Validity preserved, `key_set` difference, all 3 cases |
| INORDER-WALK §12.1 | `bst_inorder` | Sorted output proven |

### Pointer-Based Pulse (`BST.fst`)

`bst_node = { key; left; right; p }` with sep-logic predicate `bst_subtree` linking to pure spec.

| CLRS Operation | Function | Status |
|----------------|----------|--------|
| TREE-SEARCH §12.2 | `tree_search` | ✅ Recursive, linked to pure spec |
| TREE-INSERT §12.3 | `tree_insert` | ✅ Recursive, parent-pointer maintained |
| TREE-DELETE §12.3 | `tree_delete` | ✅ Recursive, linked to pure spec |
| TREE-FREE | `tree_free` | ✅ Recursive deallocation |

### Array-Based Pulse (`BSTArray.fst` + `BSTArray.Delete.fst`)

`bst = { keys: array int; valid: array bool; cap: SZ.t }` — implicit `2*i+1`/`2*i+2` layout.

| CLRS Operation | Function | Status |
|----------------|----------|--------|
| TREE-SEARCH §12.2 | `tree_search` | ✅ Iterative while loop + ghost O(h) ticks |
| TREE-INSERT §12.3 | `tree_insert` | ✅ Iterative, `well_formed_bst` pre/post |
| TREE-MINIMUM §12.2 | `tree_minimum` | ✅ Iterative, fully verified |
| TREE-MAXIMUM §12.2 | `tree_maximum` | ✅ Iterative, fully verified |
| TREE-SUCCESSOR §12.2 | `tree_successor` | ✅ Parent formula `(i-1)/2` + parity |
| TREE-PREDECESSOR §12.2 | `tree_predecessor` | ✅ Symmetric |
| TREE-DELETE §12.3 | `tree_delete` | 🔶 Leaf proven; 1-/2-child cases incomplete |
| INORDER-WALK §12.1 | `inorder_walk` | ✅ Recursive Pulse, proven ≡ pure spec via Refinement |
| TRANSPLANT §12.3 | — | ❌ Impossible in array layout (positions fixed by index arithmetic) |

---

## Rubric Compliance Matrix

The canonical rubric requires seven artefacts per algorithm. This chapter has **two implementation layers** (pointer-based BST.\* and array-based BSTArray.\*), so compliance is assessed for each.

### Legend

- ✅ Present and complete
- 🔶 Partially present or needs work
- ❌ Missing

### BST (Pointer-Based) — `CLRS.Ch12.BST.*`

| Rubric Artefact | Required File | Status | Actual File(s) | Notes |
|-----------------|---------------|--------|-----------------|-------|
| **Spec.fst** | `CLRS.Ch12.BST.Spec.fst` | ✅ | `BST.Spec.Complete.fst` | Pure spec with all operations; naming uses `.Spec.Complete` instead of `.Spec` |
| **Lemmas.fst** | `CLRS.Ch12.BST.Lemmas.fst` | 🔶 | `Insert.Spec.fst`, `Delete.Spec.fst`, `KeySet.fst` | Key-set theorems exist as separate files; no unified `Lemmas.fst` |
| **Lemmas.fsti** | `CLRS.Ch12.BST.Lemmas.fsti` | ❌ | — | No interface files exist anywhere in chapter |
| **Complexity.fst** | `CLRS.Ch12.BST.Complexity.fst` | ✅ | `BST.Spec.Complexity.fst` | O(h) bounds for all operations; naming uses `.Spec.Complexity` |
| **Complexity.fsti** | `CLRS.Ch12.BST.Complexity.fsti` | ❌ | — | No interface file |
| **Impl.fst** | `CLRS.Ch12.BST.Impl.fst` | ✅ | `BST.fst` | Pulse pointer-based impl with `bst_subtree` sep-logic; naming is `.BST` not `.Impl` |
| **Impl.fsti** | `CLRS.Ch12.BST.Impl.fsti` | ❌ | — | No interface file |

### BSTArray (Array-Based) — `CLRS.Ch12.BSTArray.*`

| Rubric Artefact | Required File | Status | Actual File(s) | Notes |
|-----------------|---------------|--------|-----------------|-------|
| **Spec.fst** | `CLRS.Ch12.BSTArray.Spec.fst` | ✅ | `BSTArray.Spec.fst` | Pure search over arrays + soundness/completeness |
| **Lemmas.fst** | `CLRS.Ch12.BSTArray.Lemmas.fst` | 🔶 | `Predicates.fst`, `Refinement.fst` | Lemmas split across Predicates (frame, preservation) and Refinement (abstraction proofs) |
| **Lemmas.fsti** | `CLRS.Ch12.BSTArray.Lemmas.fsti` | ❌ | — | No interface file |
| **Complexity.fst** | `CLRS.Ch12.BSTArray.Complexity.fst` | 🔶 | `BSTArray.Complexity.fst` | Structural bounds only (`node_depth ≤ log₂ cap`); does not connect to operation costs |
| **Complexity.fsti** | `CLRS.Ch12.BSTArray.Complexity.fsti` | ❌ | — | No interface file |
| **Impl.fst** | `CLRS.Ch12.BSTArray.Impl.fst` | ✅ | `BSTArray.fst` + `BSTArray.Delete.fst` | Split across two files; naming uses `.BSTArray` not `.Impl` |
| **Impl.fsti** | `CLRS.Ch12.BSTArray.Impl.fsti` | ❌ | — | No interface file |

### Cross-Cutting Concerns

| Aspect | Status | Details |
|--------|--------|---------|
| **Zero admits** | ✅ | No `admit()` calls in any file. All occurrences of "admit" are in comments only. |
| **Zero assumes** | ✅ | No `assume` calls in any file. |
| **Refinement proof** | ✅ | `BSTArray.Refinement.fst` connects array repr to pure inductive spec (`array_to_bst`) |
| **CLRS cross-references** | ✅ | Theorems 12.2 and 12.3 cited; §12.1–12.3 referenced throughout |
| **Snippet markers** | ✅ | 36+ `SNIPPET_START`/`SNIPPET_END` pairs across 6 files |
| **Ghost complexity ticks** | 🔶 | Only `tree_search` (BSTArray) has ghost ticks; insert/delete/min/max lack them |

---

## Detailed Action Items

### P0 — Naming Compliance

| # | Action | Current | Target | Effort |
|---|--------|---------|--------|--------|
| 1 | Rename or alias `BST.Spec.Complete` → `BST.Spec` | `CLRS.Ch12.BST.Spec.Complete.fst` | `CLRS.Ch12.BST.Spec.fst` | Low — rename + update imports |
| 2 | Rename or alias `BST.Spec.Complexity` → `BST.Complexity` | `CLRS.Ch12.BST.Spec.Complexity.fst` | `CLRS.Ch12.BST.Complexity.fst` | Low |

> **Note:** Item 1 conflicts with the existing `CLRS.Ch12.BSTArray.Spec.fst`. The two layers use different naming prefixes (`BST` vs `BSTArray`), so the rename is safe within each prefix.

### P1 — Missing Interface Files (.fsti)

| # | Action | File to Create |
|---|--------|----------------|
| 3 | Create BST Lemmas interface | `CLRS.Ch12.BST.Lemmas.fsti` — expose `insert_key_set_lemma`, `delete_key_set_lemma`, correctness lemma signatures |
| 4 | Create BST Complexity interface | `CLRS.Ch12.BST.Complexity.fsti` — expose tick bound signatures (`bst_search_ticks ≤ bst_height`, etc.) |
| 5 | Create BST Impl interface | `CLRS.Ch12.BST.Impl.fsti` — public signatures for `tree_search`, `tree_insert`, `tree_delete`, `tree_free` |
| 6 | Create BSTArray Lemmas interface | `CLRS.Ch12.BSTArray.Lemmas.fsti` — expose `well_formed_bst`, `lemma_insert_wfb`, refinement lemma signatures |
| 7 | Create BSTArray Complexity interface | `CLRS.Ch12.BSTArray.Complexity.fsti` — expose `tree_height`, `node_depth_bounded` |
| 8 | Create BSTArray Impl interface | `CLRS.Ch12.BSTArray.Impl.fsti` — public signatures for Pulse operations |

### P1 — Consolidate Lemma Files

| # | Action | Details |
|---|--------|---------|
| 9 | Create unified `CLRS.Ch12.BST.Lemmas.fst` | Consolidate or re-export from `Insert.Spec.fst`, `Delete.Spec.fst`, `KeySet.fst` |
| 10 | Create unified `CLRS.Ch12.BSTArray.Lemmas.fst` | Consolidate or re-export from `Predicates.fst` and `Refinement.fst` |

### P2 — Completeness Gaps

| # | Action | Details |
|---|--------|---------|
| 11 | Complete BSTArray `tree_delete` for 1-child and 2-child cases | Currently marks invalid, orphaning children. Requires `copy_subtree` for array layout. |
| 12 | Add ghost ticks to BSTArray `tree_insert` | Only `tree_search` has ghost O(h) tick counter |
| 13 | Add ghost ticks to BSTArray `tree_minimum`/`tree_maximum` | Straightforward — loop already follows root-to-leaf path |
| 14 | Connect BSTArray.Complexity to operation costs | Current proof is structural only (`node_depth ≤ log₂ cap`); does not link to actual loop iterations |
| 15 | Deduplicate search logic in `BSTArray.Delete:tree_delete_key` | ~120 lines duplicate `tree_search`; blocked on API change (needs `subtree_in_range` precondition) |
| 16 | Consider tighter delete bound | Pure spec proves `4h+1`; could be `3h+1` since successor-find and delete share the same right-subtree path |

### DEFER

| # | Action | Reason |
|---|--------|--------|
| 17 | Implement `bst_successor`/`bst_predecessor` in pure spec | Requires parent pointers; not natural for inductive type |
| 18 | Implement TRANSPLANT for BSTArray | Impossible in array layout — child positions fixed by index arithmetic |

---

## Quality Checks

| Check | Result | Evidence |
|-------|--------|----------|
| **No `admit()` calls** | ✅ PASS | `grep -c admit *.fst` returns 0 actual calls; all hits are in comments |
| **No `assume` calls** | ✅ PASS | `grep -c assume *.fst` returns 0 actual calls |
| **No `assert False` misuse** | ✅ PASS | Two uses in `Delete.Spec.fst` (lines 106, 346) are valid contradiction discharges |
| **Z3 rlimits reasonable** | ✅ PASS | Max rlimit is 100 (for FiniteSet proofs); most files use defaults |
| **Fuel/ifuel bounded** | ✅ PASS | Explicit `--fuel 1 --ifuel 1` on heavy lemmas; `--fuel 2` in Refinement |
| **CLRS sections cited** | ✅ PASS | §12.1, §12.2, §12.3 referenced; Theorems 12.2, 12.3 cited |
| **Pure spec ↔ Impl linked** | ✅ PASS | Pointer BST: `bst_subtree` links to `Spec.Complete`. Array BST: `Refinement.fst` provides `array_to_bst`. |
| **Inorder sorted proven** | ✅ PASS | `bst_inorder_sorted` in `Spec.Complete.fst` — fully proven |
| **Key-set algebra proven** | ✅ PASS | Insert: `∪ {k}`, Delete: `\ {k}` — both via FiniteSet, no admits |
| **Two layers consistent** | ✅ PASS | `Refinement.fst` proves `well_formed_bst ⟹ bst_valid`, `key_in_subtree ⟺ bst_search`, inorder equivalence |
| **Dead code minimal** | 🔶 WARN | `BSTArray.fst` retains local copies of `subtree_in_range`/`key_in_subtree` (Pulse import limitation) |
| **Comment accuracy** | ✅ PASS | Stale "admit" comment in `Spec.Complexity.fst` was fixed; `Delete.fst` comments now say "INCOMPLETE" |
