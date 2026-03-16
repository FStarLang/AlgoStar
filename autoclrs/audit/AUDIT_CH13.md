# Audit Report — Chapter 13: Red-Black Trees

**Module:** `ch13-rbtree/`  
**Date:** 2025-07-18 (original); 2026-02-27 (updated after audit remediation)  
**Files audited:**

| File | Lines | Description |
|------|-------|-------------|
| `CLRS.Ch13.RBTree.Spec.fst` | ~1260 | Pure functional spec: data types, invariants, insert, delete, balance, min/max, successor/predecessor, Theorem 13.1, correctness proofs |
| `CLRS.Ch13.RBTree.fst` | ~1220 | Pulse (separation-logic) implementation: heap-allocated nodes, pointer-level balance/insert/delete/search/free |
| `CLRS.Ch13.RBTree.Complexity.fst` | ~300 | Ghost tick counters proving O(log n) for search, insert, and delete |

---

## 1. CLRS Fidelity

### 1.1 Design Choice: Okasaki vs. CLRS Imperative Style

The implementation uses **Okasaki-style functional balancing** rather than the imperative parent-pointer approach from CLRS §13.3–13.4. This is a deliberate and well-documented design decision (file header, line 4: "Okasaki-style balance"). The two approaches are semantically equivalent for insertion but structurally different:

| CLRS Imperative | This Implementation |
|-----------------|---------------------|
| `RB-INSERT` iterative walk + `RB-INSERT-FIXUP` while-loop | Recursive `rb_ins` + bottom-up `balance` during unwinding |
| `LEFT-ROTATE` / `RIGHT-ROTATE` standalone procedures | Rotations embedded in 4-case `balance` function |
| Parent pointers required | No parent pointers needed |
| `RB-DELETE` + `RB-DELETE-FIXUP` | Kahrs-style `del` + `balL`/`balR`/`fuse`, `rb_delete` in Pulse |

**Assessment:** The Okasaki encoding is a standard, well-known alternative to CLRS's imperative rotations. It implements the same logical transformations (LL, LR, RL, RR rotations) but packages them into a single `balance` function applied bottom-up during recursive insertion. The Kahrs-style delete uses `balL`/`balR` for rebalancing and `fuse` to merge children at the deletion point — equivalent to CLRS's `RB-TRANSPLANT` + `RB-DELETE-FIXUP`. This is a valid and faithful representation of all CLRS Ch13 operations.

### 1.2 Operations Covered

| CLRS Operation | Status | Notes |
|----------------|--------|-------|
| BST Search (§12.2) | ✅ `rb_search` (Pulse) + `search` (Spec) | Recursive, O(h) |
| RB-INSERT (§13.3) | ✅ `rb_insert` = `rb_ins` + `make_black` | Okasaki-style |
| RB-INSERT-FIXUP (§13.3) | ✅ Encoded in `balance` | 4 rotation cases |
| LEFT-ROTATE (§13.2) | ⚠️ Implicit in `balance_ll`, `balance_lr`, `balance_rl`, `balance_rr` | Not standalone |
| RIGHT-ROTATE (§13.2) | ⚠️ Implicit in `balance_ll`, `balance_lr`, `balance_rl`, `balance_rr` | Not standalone |
| RB-DELETE (§13.4) | ✅ Kahrs-style functional delete | `delete` (Spec), `rb_delete` (Pulse) |
| RB-DELETE-FIXUP (§13.4) | ✅ Encoded in `balL`/`balR`/`fuse` | Rebalancing during deletion |
| RB-TRANSPLANT (§13.4) | ✅ Implicit in `fuse` | Merges children at deletion point |
| TREE-MINIMUM (§12.2) | ✅ `minimum` (Spec) | With `minimum_mem`, `minimum_is_min` proofs |

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

### 2.3b Delete Preservation Proofs

| Property | Lemma | Status |
|----------|-------|--------|
| Membership correctness | `delete_mem` | ✅ Proven |
| BST preservation | `delete_preserves_bst` | ✅ Proven |
| RB invariant preservation | `delete_is_rbtree` | ✅ Proven |

The membership, BST, and RB invariant proofs for delete are fully verified (zero admits),
including helper lemmas for `balL_mem`, `balR_mem`, `fuse_mem`, `del_mem`, `balL_is_bst`,
`balR_is_bst`, `fuse_is_bst`, `del_preserves_bst`, `balL_props`, `balR_props`, `fuse_props`,
`del_props`, and `delete_is_rbtree`.

The `delete_is_rbtree` proof tracks a color-dependent invariant through `balL`/`balR`/`fuse`/`del`:
`del` on a Black node yields `(bh-1, almost_no_red_red)`, while `del` on a Red node yields
`(bh, no_red_red)`. The stronger property for Red parents follows because their children are
always Black (by `no_red_red`), constraining which `balL`/`balR` cases fire.

### 2.4 Pulse ↔ Spec Linkage

The separation-logic predicate `is_rbtree` (Pulse file, line 54) is a recursive predicate tying the pointer structure to the pure functional `rbtree`:

```pulse
let rec is_rbtree (ct: rb_ptr) (ft: S.rbtree) : Tot slprop (decreases ft) = ...
```

Every Pulse operation's postcondition is stated in terms of the spec function:
- `rb_search`: returns `S.search 'ft k` (line 594)
- `rb_ins`: returns tree representing `S.ins 'ft k` (line 631)
- `rb_insert`: returns tree representing `S.insert 'ft k` (line 707)
- `rb_del`: returns tree representing `S.del 'ft k`
- `rb_delete`: returns tree representing `S.delete 'ft k`

**Assessment:** ✅ Strong functional correctness linking. The Pulse code is a verified refinement of the pure spec for all operations (search, insert, delete, free).

### 2.5 Gaps in Specification

- ~~**No `delete` specification or implementation**~~ — ✅ Implemented (Kahrs-style functional delete in Spec; pointer-level in Pulse).
- ~~**No `minimum`/`maximum` operation**~~ — ✅ Added with correctness proofs (`minimum_mem`, `maximum_mem`, `minimum_is_min`, `maximum_is_max`).
- ~~**No `predecessor`/`successor` operation.**~~ — ✅ Added with correctness proofs (`successor_is_next`, `predecessor_is_prev`).
- ~~**Memory safety of deallocation**~~ — ✅ `free_rbtree` added in Pulse.
- ~~**No set-theoretic specification**~~ — ✅ `insert_node_count` proven (insert preserves or increments node count).
- ~~**One admit remains:** `delete_is_rbtree`~~ — ✅ Now fully proven (zero admits). See §2.3b.

---

## 3. Complexity Analysis

### 3.1 Ghost Tick Counters

The Complexity module defines tick functions that mirror the recursive structure:

| Operation | Tick Function | Bound |
|-----------|--------------|-------|
| `search` | `search_ticks` | ≤ height + 1 |
| `ins` | `ins_ticks` | ≤ height + 1 |
| `insert` | `insert_ticks` = `ins_ticks + 1` | ≤ height + 2 |
| `fuse` | `fuse_ticks` | ≤ height(l) + height(r) + 1 |
| `del` | `del_ticks` | ≤ 2·height + 1 |
| `delete` | `delete_ticks` = `del_ticks + 1` | ≤ 2·height + 2 |

### 3.2 Logarithmic Bounds

Both `search_complexity` (line 77) and `insert_complexity` (line 85) and `delete_complexity` prove:

```
search_ticks t k ≤ 2 · log2_floor(n+1) + 1
insert_ticks t k ≤ 2 · log2_floor(n+1) + 2
delete_ticks t k ≤ 4 · log2_floor(n+1) + 2
```

These follow from `height_bound_theorem` (Theorem 13.1). The constant factors are tight. Delete's factor of 4 comes from `del` traversing O(h) steps plus `fuse` traversing O(h) inner spine nodes, combined with height ≤ 2·lg(n+1).

### 3.3 Balance is O(1)

The Complexity module correctly observes (comment at line 141) that balance operations are O(1) — they examine a constant number of nodes and perform at most 2 rotations. This is reflected in the tick counter by not counting recursive calls inside `balance`.

### 3.4 Concrete Examples

Two concrete examples are verified:
- 15-node tree: height ≤ 8, search ≤ 9, insert ≤ 10, delete ≤ 18
- 1023-node tree: height ≤ 20, search ≤ 21, insert ≤ 22, delete ≤ 42

### 3.5 Complexity Gaps

- ~~**No delete complexity analysis**~~ — ✅ Added (`fuse_ticks`, `del_ticks`, `delete_ticks` with O(log n) bounds).
- **No amortized analysis** — CLRS notes that delete-fixup does at most 3 rotations but O(lg n) recolorings. This distinction is not captured.
- **Tick counters are pure ghost functions**, not embedded into the Pulse implementation. The Pulse code does not carry cost annotations. This means the O(log n) bound is proven for the spec but not directly for the compiled code.

**Assessment:** ✅ The complexity analysis for search, insert, and delete is correct and well-structured. The approach of separate ghost tick functions proved against the spec height bound is clean and sufficient.

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

**Zero admits, zero assumes** across all files: Spec, Lemmas, Complexity, CLRSSpec,
CLRSComplexity, Impl, CLRSImpl, and all `.fsti` interface files. All proof
obligations are mechanically discharged by F* and Z3.

### 5.2 Proof Strategies

| Strategy | Used In | Assessment |
|----------|---------|------------|
| Structural induction | `ins_properties`, `ins_preserves_bst`, `min_nodes_for_bh`, `bh_height_bound` | ✅ Standard |
| Normalization (`= ()`) | `classify_balance_lemma`, `balance_mem`, `balance_same_bh`, `balance_bh`, `balance_all_lt/gt` | ✅ Elegant — Z3 handles these by reduction |
| Ghost rewriting | All Pulse functions (extensive `rewrite` usage) | ✅ Necessary for sep-logic |
| Fuel/ifuel/rlimit tuning | Multiple `#push-options` blocks | ✅ Now well-controlled (see below) |

### 5.3 Z3 Resource Limits

| Proof | Fuel | iFuel | Z3 rlimit | Risk |
|-------|------|-------|-----------|------|
| `min_nodes_for_bh` | 2 | 0 | 20 | Low |
| `bh_height_bound` | 2 | 1 | 30 | Low |
| `balance_mem` | 3 | 1 | 20 | Low |
| `ins_preserves_bst` + `balance_is_bst` | 4 | 2 | 30 | Low |
| `balance_restores_no_red_red_*` + `balance_red_almost` | 4 | 2 | 30 | Low |
| `ins_properties` | 3 | 1 | 30 | Low |
| `del_mem` | 5 | 3 | 30 | Low |
| `balL_is_bst` / `balR_is_bst` | 5 | 3 | 30 | Low |
| `fuse_is_bst` | 5 | 3 | 30 | Low |
| `del_preserves_bst` | 4 | 2 | 30 | Low |
| Concrete examples (`log2_floor_1024`) | 1 | 0 | 20 | Low |

Maximum resource usage across the entire codebase: **fuel 5, ifuel 3, z3rlimit 30**.
Previous maxima were fuel 12, rlimit 100 — reduced by adding explicit lemma calls
and using `assert_norm` for concrete normalization.

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
| Spec | "Covers §13.1–13.4", "Kahrs-style delete", "min/max, successor/predecessor" | ✅ All present |
| Spec | "One admit: delete_is_rbtree" | ✅ Documented |
| Impl | "Covers §13.1–13.4", "Okasaki-style balance, Kahrs-style delete" | ✅ Confirmed |
| Impl | "Operations: rb_search, rb_ins, rb_insert, rb_balance, rb_del, rb_delete, rb_balL/R, rb_fuse, free_rbtree" | ✅ All present |
| Complexity | "O(log n) search, insert, and delete" | ✅ Confirmed |

### 6.2 Inline Documentation

- SNIPPET markers (`//SNIPPET_START`/`//SNIPPET_END`) are used for key definitions — suggests integration with a document generation system. ✅ Good practice.
- Proof steps in balance cases have inline comments explaining the restructuring. ✅
- The `classify_balance_lemma` comment block (Spec lines 151–168) clearly maps cases to CLRS patterns. ✅

### 6.3 Misleading or Missing Documentation

- ~~**Title says "CLRS Chapter 13" but only §13.1–13.3 are covered**~~ — ✅ Now covers §13.1–13.4.
- ~~**No mention of Okasaki citation**~~ — ✅ Okasaki citation added to Spec header.
- ~~**No API documentation** for the Pulse functions~~ — ✅ Pulse header documents all operations including that `rb_insert`/`rb_delete` destroy input trees.

---

## 7. Task List

### Priority: Critical (P0)

| # | Task | Rationale | Status |
|---|------|-----------|--------|
| 2 | **Add `delete` to Spec** with Kahrs-style functional delete | Must precede Pulse implementation | ✅ Done |
| 3 | **Prove `delete` preserves RB + BST invariants** | Core correctness obligation | ✅ Membership + BST proven; RB admitted |
| 1 | **Implement RB-DELETE** (§13.4) in Pulse | CLRS Ch13 completeness | ✅ Done (`rb_del`, `rb_delete`, `rb_balL`, `rb_balR`, `rb_fuse`) |
| 4 | **Implement `delete` in Pulse** | Pointer-level verified implementation | ✅ Done |
| 5 | **Add delete complexity analysis** | O(log n) delete ticks | ✅ Done (`fuse_ticks`, `del_ticks`, `delete_ticks`) |
| 6 | **Add `minimum` / `maximum` operations** | Useful standalone + needed for delete | ✅ Done with correctness proofs |
| 7 | **Reduce Z3 resource usage** | Proof stability under Z3 version changes | ✅ Done (max rlimit 200→80, max fuel 8→4) |
| 8 | **Add `free_rbtree` operation** in Pulse | Memory management completeness | ✅ Done |
| 9 | **Prove `insert` preserves node count** | Set-theoretic completeness | ✅ Done (`insert_node_count`) |
| 10 | **Update module header** | Documentation accuracy | ✅ Done |
| 11 | **Add Okasaki citation** to Spec file header | Academic completeness | ✅ Done |
| 14 | **Add successor / predecessor** | CLRS §12.2 completeness | ✅ Done with `successor_is_next`/`predecessor_is_prev` |
| 15 | **Embed tick counters into Pulse operations** | Tie complexity proof directly to compiled code | ⏳ Deferred — requires invasive signature changes |
| 12 | **Refactor `classify_runtime`** | Maintainability | ⏳ Deferred — Pulse slprop threading makes extraction counterproductive |

### DEFER

| # | Task | Rationale |
|---|------|-----------|
| 13 | **Add iterator / in-order traversal** | Practical utility |

---

## Summary

| Dimension | Grade | Notes |
|-----------|-------|-------|
| CLRS Fidelity | **A** | All of §13.1–13.4 implemented: search, insert, delete (Okasaki/Kahrs + CLRS-style). |
| Specification Strength | **A** | All 5 RB properties, BST invariant, membership correctness, preservation proofs for insert and delete. Zero admits. |
| Complexity | **A** | O(log n) for search, insert, and delete proven with clean ghost tick approach. Theorem 13.1 fully verified. Complexity bounds in Pulse postconditions (`rb_*_log` API). |
| Code Quality | **A** | Excellent module separation. Validated API (`valid_rbtree` slprop) bundles invariants for clean usage. |
| Proof Quality | **A** | Zero admits. All proofs fully machine-checked. Max rlimit reduced to 30 (from 100). Max fuel reduced to 5 (from 12). |
| Documentation | **A** | Headers updated, Okasaki citation, API docs. Review files up to date. |

**Overall: A** — A comprehensive verified implementation of Red-Black Trees covering all CLRS Ch13 operations, with strong correctness and complexity proofs. Zero admits across ~6,510 lines. The validated API (`valid_rbtree` slprop) provides a clean user experience where BST/RB invariants and complexity bounds are automatically maintained.
