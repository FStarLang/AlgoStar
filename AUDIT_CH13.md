# Audit Report — Chapter 13: Red-Black Trees

**Module:** `ch13-rbtree/`  
**Date:** 2025-07-18  
**Files audited:**

| File | Lines | Description |
|------|-------|-------------|
| `CLRS.Ch13.RBTree.Spec.fst` | 524 | Pure functional spec: data types, invariants, insert, balance, Theorem 13.1, correctness proofs |
| `CLRS.Ch13.RBTree.fst` | 712 | Pulse (separation-logic) implementation: heap-allocated nodes, pointer-level balance/insert/search |
| `CLRS.Ch13.RBTree.Complexity.fst` | 196 | Ghost tick counters proving O(log n) for search and insert |

---

## 1. CLRS Fidelity

### 1.1 Design Choice: Okasaki vs. CLRS Imperative Style

The implementation uses **Okasaki-style functional balancing** rather than the imperative parent-pointer approach from CLRS §13.3–13.4. This is a deliberate and well-documented design decision (file header, line 4: "Okasaki-style balance"). The two approaches are semantically equivalent for insertion but structurally different:

| CLRS Imperative | This Implementation |
|-----------------|---------------------|
| `RB-INSERT` iterative walk + `RB-INSERT-FIXUP` while-loop | Recursive `rb_ins` + bottom-up `balance` during unwinding |
| `LEFT-ROTATE` / `RIGHT-ROTATE` standalone procedures | Rotations embedded in 4-case `balance` function |
| Parent pointers required | No parent pointers needed |
| `RB-DELETE` + `RB-DELETE-FIXUP` | **Not implemented** |

**Assessment:** The Okasaki encoding is a standard, well-known alternative to CLRS's imperative rotations. It implements the same logical transformations (LL, LR, RL, RR rotations) but packages them into a single `balance` function applied bottom-up during recursive insertion. This is a valid and faithful representation of the CLRS balancing logic.

### 1.2 Operations Covered

| CLRS Operation | Status | Notes |
|----------------|--------|-------|
| BST Search (§12.2) | ✅ `rb_search` (Pulse) + `search` (Spec) | Recursive, O(h) |
| RB-INSERT (§13.3) | ✅ `rb_insert` = `rb_ins` + `make_black` | Okasaki-style |
| RB-INSERT-FIXUP (§13.3) | ✅ Encoded in `balance` | 4 rotation cases |
| LEFT-ROTATE (§13.2) | ⚠️ Implicit in `balance_ll`, `balance_lr`, `balance_rl`, `balance_rr` | Not standalone |
| RIGHT-ROTATE (§13.2) | ⚠️ Implicit in `balance_ll`, `balance_lr`, `balance_rl`, `balance_rr` | Not standalone |
| RB-DELETE (§13.4) | ❌ Not implemented | |
| RB-DELETE-FIXUP (§13.4) | ❌ Not implemented | |
| RB-TRANSPLANT (§13.4) | ❌ Not implemented | |
| TREE-MINIMUM (§12.2) | ❌ Not implemented | Needed for delete |

### 1.3 Rotation Fidelity

The four balance cases in the Spec (lines 118–132) map directly to CLRS's rotation patterns:

- **BC_LL** (Spec line 120–121): Left-left case → right rotation of grandparent. Matches CLRS Case 3 (§13.3) when uncle is black and z is left child.
- **BC_LR** (Spec lines 123–124): Left-right case → left rotation of parent then right rotation of grandparent. Matches CLRS Cases 2→3.
- **BC_RL** (Spec lines 126–127): Mirror of LR.
- **BC_RR** (Spec lines 129–130): Mirror of LL.

All four Pulse implementations (`balance_ll`, `balance_lr`, `balance_rl`, `balance_rr`) are verified against the pure spec via `classify_balance_lemma`, which itself is proven by normalization (Spec line 187: `= ()`).

### 1.4 Theorem 13.1 (Lemma 13.1 in CLRS)

CLRS Lemma 13.1 states: *"A red-black tree with n internal nodes has height at most 2·lg(n+1)."*

This is proven in the Spec as `height_bound_theorem` (line 273), which assembles:
1. `min_nodes_for_bh`: node_count ≥ 2^bh − 1 (line 193)
2. `bh_height_bound`: height ≤ 2·bh + color_bonus (line 219)
3. `log2_floor_ge`: n ≥ 2^k ⟹ log2_floor(n) ≥ k (line 257)

**Assessment:** ✅ Faithfully proven. The proof structure mirrors the CLRS proof (induction on height for the key lemma).

---

## 2. Specification Strength

### 2.1 Five RB Properties

CLRS defines five red-black properties:

| # | CLRS Property | Spec Predicate | Status |
|---|--------------|----------------|--------|
| 1 | Every node is red or black | Enforced by `type color = Red \| Black` | ✅ By construction |
| 2 | Root is black | `is_root_black` (line 51) | ✅ |
| 3 | Every leaf (NIL) is black | `Leaf` constructor (implicit: leaves have no color) | ✅ Implicit in representation |
| 4 | Red node has two black children | `no_red_red` (line 57) | ✅ |
| 5 | Equal black-height on all paths | `same_bh` (line 68) | ✅ |

Combined invariant at Spec line 73:
```fstar
let is_rbtree (t: rbtree) : bool =
  is_root_black t && no_red_red t && same_bh t
```

**Assessment:** ✅ All five properties are correctly encoded. Property 3 is elegant — since `Leaf` has no color attribute, it is implicitly treated as black by `bh` (which returns 0 for Leaf, not incrementing the black count).

### 2.2 BST Invariant

The BST ordering invariant is specified separately:
- `all_lt` / `all_gt` bound predicates (lines 84–93)
- `is_bst` recursive check (line 96)
- `ins_preserves_bst` proven (line 409)
- `insert_preserves_bst` proven (line 428)

**Assessment:** ✅ Complete BST correctness. The choice to use `all_lt`/`all_gt` (global bounds) rather than local parent comparisons is the standard approach for functional BST verification.

### 2.3 Insert Preservation Proofs

The following are all proven (zero admits):

| Property | Lemma | Line |
|----------|-------|------|
| Membership correctness | `insert_mem` | 315 |
| BST preservation | `insert_preserves_bst` | 428 |
| RB invariant preservation | `insert_is_rbtree` | 520 |
| Black-height preservation | via `ins_properties` | 489 |
| No-red-red (modulo root) | `ins_properties` ensures `almost_no_red_red` | 489 |

`ins_properties` (line 489) is the key lemma, proving four properties simultaneously by structural induction — a clean proof strategy.

### 2.4 Pulse ↔ Spec Linkage

The separation-logic predicate `is_rbtree` (Pulse file, line 54) is a recursive predicate tying the pointer structure to the pure functional `rbtree`:

```pulse
let rec is_rbtree (ct: rb_ptr) (ft: S.rbtree) : Tot slprop (decreases ft) = ...
```

Every Pulse operation's postcondition is stated in terms of the spec function:
- `rb_search`: returns `S.search 'ft k` (line 594)
- `rb_ins`: returns tree representing `S.ins 'ft k` (line 631)
- `rb_insert`: returns tree representing `S.insert 'ft k` (line 707)

**Assessment:** ✅ Strong functional correctness linking. The Pulse code is a verified refinement of the pure spec.

### 2.5 Gaps in Specification

- **No `delete` specification or implementation** — CLRS §13.4 is entirely missing.
- **No `minimum`/`maximum` operation** — needed as helper for delete.
- **No `predecessor`/`successor` operation.**
- **Memory safety of deallocation**: `rb_ins` calls `Box.free vl` (line 654) when a node is rebalanced. This is safe because the node's ownership is consumed, but there is no explicit `free_rbtree` operation to deallocate an entire tree.
- **No set-theoretic specification**: e.g., no proof that `insert` into a tree of size n yields size n or n+1.

---

## 3. Complexity Analysis

### 3.1 Ghost Tick Counters

The Complexity module defines tick functions that mirror the recursive structure:

| Operation | Tick Function | Bound |
|-----------|--------------|-------|
| `search` | `search_ticks` | ≤ height + 1 |
| `ins` | `ins_ticks` | ≤ height + 1 |
| `insert` | `insert_ticks` = `ins_ticks + 1` | ≤ height + 2 |

### 3.2 Logarithmic Bounds

Both `search_complexity` (line 77) and `insert_complexity` (line 85) prove:

```
search_ticks t k ≤ 2 · log2_floor(n+1) + 1
insert_ticks t k ≤ 2 · log2_floor(n+1) + 2
```

These follow from `height_bound_theorem` (Theorem 13.1). The constant factors are tight.

### 3.3 Balance is O(1)

The Complexity module correctly observes (comment at line 141) that balance operations are O(1) — they examine a constant number of nodes and perform at most 2 rotations. This is reflected in the tick counter by not counting recursive calls inside `balance`.

### 3.4 Concrete Examples

Two concrete examples are verified:
- 15-node tree: height ≤ 8, search ≤ 9, insert ≤ 10 (line 154)
- 1023-node tree: height ≤ 20, search ≤ 21, insert ≤ 22 (line 174)

### 3.5 Complexity Gaps

- **No delete complexity analysis** (delete not implemented).
- **No amortized analysis** — CLRS notes that delete-fixup does at most 3 rotations but O(lg n) recolorings. This distinction is not captured.
- **Tick counters are pure ghost functions**, not embedded into the Pulse implementation. The Pulse code does not carry cost annotations. This means the O(log n) bound is proven for the spec but not directly for the compiled code.

**Assessment:** ✅ The complexity analysis for search and insert is correct and well-structured. The approach of separate ghost tick functions proved against the spec height bound is clean and sufficient.

---

## 4. Code Quality

### 4.1 Structure and Organization

| Aspect | Rating | Notes |
|--------|--------|-------|
| Module separation (Spec/Impl/Complexity) | ⭐⭐⭐⭐⭐ | Textbook-clean three-layer design |
| Naming conventions | ⭐⭐⭐⭐⭐ | Consistent: `rb_` prefix, snake_case, matches CLRS terminology |
| Comments | ⭐⭐⭐⭐ | Good module-level docs; inline comments explain proof steps |
| Code duplication | ⭐⭐⭐ | `check_right_balance` (80 lines) has repeated nested match patterns; `classify_runtime` is 100 lines of nested case analysis. Inherent to pointer-level work. |
| Line count efficiency | ⭐⭐⭐⭐ | 1432 total lines for a verified RB-tree is reasonable |

### 4.2 Pulse Implementation Quality

The Pulse code demonstrates several good patterns:
- **Node reuse via mutation** (`llp :=`, `lp :=`, etc.) to minimize allocation in balance cases.
- **Ghost fold/unfold helpers** (`intro_is_rbtree_node`, `elim_is_rbtree_leaf`, etc.) are cleanly factored out.
- **`is_rbtree_cases`** (line 98) avoids recursive unfolding for case analysis — good performance practice.
- **`preserves` keyword** used for read-only operations (`rb_search`, `classify_runtime`).

### 4.3 Potential Issues

1. **`classify_runtime` verbosity** (lines 280–377): The runtime balance classifier is ~100 lines of nested pointer chasing. This is a consequence of needing to match the pure pattern-matching classifier against a pointer tree. Not a bug, but a maintenance concern. Consider extracting per-case helpers.

2. **`Box.free` in `rb_ins`** (lines 654, 660): The old node is freed when rebalancing. This is correct because the node's ownership (via `is_rbtree_case_some`) is consumed and the subtree pointers are extracted. However, it means **the original tree is destroyed** during insert. This is expected for a mutable data structure but worth documenting at the API level.

3. **No `rb_ptr` alias for readability**: `option (box rb_node)` is used throughout. The type alias `rb_ptr` (line 48) helps, but the mutual recursion with `rb_node` is slightly unusual.

---

## 5. Proof Quality

### 5.1 Admits and Assumes

**Zero admits. Zero assumes.** Confirmed by grep across all three files. The only hits are in documentation comments:
- `CLRS.Ch13.RBTree.fst` line 21: `"NO admits. NO assumes."` (comment)
- `CLRS.Ch13.RBTree.Spec.fst` line 13: `"Zero admits."` (comment)
- `CLRS.Ch13.RBTree.Complexity.fst` line 15: `"NO admits. NO assumes."` (comment)

**Assessment:** ✅ Fully verified. This is the gold standard.

### 5.2 Proof Strategies

| Strategy | Used In | Assessment |
|----------|---------|------------|
| Structural induction | `ins_properties`, `ins_preserves_bst`, `min_nodes_for_bh`, `bh_height_bound` | ✅ Standard |
| Normalization (`= ()`) | `classify_balance_lemma`, `balance_mem`, `balance_same_bh`, `balance_bh`, `balance_all_lt/gt` | ✅ Elegant — Z3 handles these by reduction |
| Ghost rewriting | All Pulse functions (extensive `rewrite` usage) | ✅ Necessary for sep-logic |
| Fuel/ifuel/rlimit tuning | Multiple `#push-options` blocks | ⚠️ See below |

### 5.3 Z3 Resource Limits

| Proof | Fuel | iFuel | Z3 rlimit | Risk |
|-------|------|-------|-----------|------|
| `min_nodes_for_bh` | 2 | 0 | 20 | Low |
| `bh_height_bound` | 2 | 1 | 30 | Low |
| `balance_mem` | 3 | 1 | 20 | Low |
| `ins_preserves_bst` + `balance_is_bst` | 4 | 2 | 200 | ⚠️ Moderate — high fuel+rlimit |
| `balance_restores_no_red_red_*` + `balance_red_almost` | 8 | 4 | 200 | ⚠️ Moderate — high fuel+rlimit |
| `ins_properties` | 3 | 1 | 30 | Low |
| `log2_floor_16` | — | — | 30 (fuel 6) | Low |
| `log2_floor_1024` | — | — | 30 (fuel 12) | Low |

The `--fuel 8 --ifuel 4 --z3rlimit 200` block (Spec line 465) and `--fuel 4 --ifuel 2 --z3rlimit 200` block (Spec line 390) are the most resource-intensive proofs. While they verify, they could be fragile under Z3 version changes. Consider adding intermediate lemmas to reduce fuel requirements.

### 5.4 Pulse-Specific Proof Patterns

The Pulse proofs make heavy use of:
- `intro_is_rbtree_node` / `elim_is_rbtree_leaf` — ghost fold/unfold (~30 call sites)
- `rewrite each X as Y` — pointer equality rewrites
- `with t. rewrite (is_rbtree y t) as (is_rbtree y (S.f ...))` — linking computed tree to spec

These are clean and idiomatic. The ghost helpers are well-factored and reusable.

---

## 6. Documentation Accuracy

### 6.1 Module Headers

| File | Header Claims | Accurate? |
|------|--------------|-----------|
| Spec | "Defines: rbtree type, BST ordering, RB invariants, search, insert, Theorem 13.1, correctness" | ✅ All present |
| Spec | "Zero admits" | ✅ Confirmed |
| Impl | "Okasaki-style balance", "NO admits. NO assumes." | ✅ Confirmed |
| Impl | "Operations: rb_search O(h), rb_ins O(h), rb_insert, rb_balance" | ✅ All present |
| Complexity | "O(log n) search and insert", "NO admits. NO assumes." | ✅ Confirmed |

### 6.2 Inline Documentation

- SNIPPET markers (`//SNIPPET_START`/`//SNIPPET_END`) are used for key definitions — suggests integration with a document generation system. ✅ Good practice.
- Proof steps in balance cases have inline comments explaining the restructuring. ✅
- The `classify_balance_lemma` comment block (Spec lines 151–168) clearly maps cases to CLRS patterns. ✅

### 6.3 Misleading or Missing Documentation

- **Title says "CLRS Chapter 13"** but only §13.1–13.3 are covered. §13.4 (Deletion) is entirely absent. The module header should note this limitation.
- **No mention of Okasaki citation** in the Spec file. The Impl file mentions "Okasaki-style balance" but does not cite the original paper (Okasaki, "Red-Black Trees in a Functional Setting", JFP 1999).
- **No API documentation** for the Pulse functions (e.g., documenting that `rb_insert` destroys the input tree).

---

## 7. Task List

### Priority: Critical (P0)

| # | Task | Rationale |
|---|------|-----------|
| 2 | **Add `delete` to Spec** with Okasaki-style functional delete | Must precede Pulse implementation. Consider Kahrs/Germane-Might style functional delete. |
| 3 | **Prove `delete` preserves RB + BST invariants** | Core correctness obligation |
| 1 | **Implement RB-DELETE** (§13.4) | CLRS Ch13 is incomplete without deletion. This is the most complex operation and the main gap. Requires `RB-TRANSPLANT`, `TREE-MINIMUM`, `RB-DELETE-FIXUP`. |
| 4 | **Implement `delete` in Pulse** | Pointer-level verified implementation |
| 5 | **Add delete complexity analysis** | O(log n) delete ticks |
| 6 | **Add `minimum` / `maximum` operations** | Useful standalone + needed for delete |
| 7 | **Reduce Z3 resource usage** for `balance_restores_no_red_red_*` (fuel 8, rlimit 200) and `balance_is_bst` (fuel 4, rlimit 200) | Proof stability under Z3 version changes |
| 8 | **Add `free_rbtree` operation** in Pulse to deallocate an entire tree | Memory management completeness |
| 9 | **Prove `insert` preserves node count** (size increases by 0 or 1) | Set-theoretic completeness |
| 10 | **Update module header** to note that §13.4 (delete) is not yet covered | Documentation accuracy |
| 11 | **Add Okasaki citation** to Spec file header | Academic completeness |
| 15 | **Embed tick counters into Pulse operations** | Tie complexity proof directly to compiled code |
| 12 | **Refactor `classify_runtime`** — extract per-case helpers to reduce nesting | Maintainability |
| 14 | **Add successor / predecessor** | CLRS §12.2 completeness |

### DEFER

| # | Task | Rationale |
|---|------|-----------|
| 13 | **Add iterator / in-order traversal** | Practical utility |

---

## Summary

| Dimension | Grade | Notes |
|-----------|-------|-------|
| CLRS Fidelity | **B+** | Insert and search are faithful (via Okasaki). Delete (§13.4) is entirely absent — a significant gap for Ch13 completeness. |
| Specification Strength | **A** | All 5 RB properties, BST invariant, membership correctness, full preservation proofs for insert. |
| Complexity | **A** | O(log n) for search/insert proven with clean ghost tick approach. Theorem 13.1 fully verified. |
| Code Quality | **A−** | Excellent module separation. Minor verbosity in `classify_runtime`. |
| Proof Quality | **A+** | Zero admits/assumes. Fully machine-checked. Some high-fuel proofs but all verify. |
| Documentation | **B+** | Good inline docs. Missing: deletion gap disclosure, Okasaki citation, API-level docs for Pulse functions. |

**Overall: A−** — A high-quality verified implementation of RB-tree insertion with strong proofs, limited by the absence of deletion.
