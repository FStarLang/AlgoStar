# CLRS.Ch13.RBTree.CLRSImplTest — Spec Validation Report

**File:** `CLRS.Ch13.RBTree.CLRSImplTest.fst`  
**Target API:** `CLRS.Ch13.RBTree.CLRSImpl.fsti` (CLRS-faithful Red-Black Tree)  
**Status:** ✅ Fully verified — zero admits, zero assumes  
**Build:** `make` produces `CLRS.Ch13.RBTree.CLRSImplTest.fst.checked` with no errors  

---

## What the Test Does

Validates the `CLRSImpl.fsti` API on a concrete 3-element instance: insert
keys 3, 1, 2 into an empty tree, then search and delete. Uses the CLRS-style
rotation-based insert/delete from `CLRSSpec.fst` (as opposed to the Okasaki-style
operations in `Spec.fst`).

### Pure Spec Validation (outside Pulse)

| Property | Assertion | Result |
|----------|-----------|--------|
| Tree shape after insert 3 | `Node Black Leaf 3 Leaf` | ✅ |
| Tree shape after insert 1 | `Node Black (Node Red Leaf 1 Leaf) 3 Leaf` | ✅ |
| Tree shape after insert 2 | `Node Black (Node Red Leaf 1 Leaf) 2 (Node Red Leaf 3 Leaf)` | ✅ |
| RB + BST invariants on all trees | `is_rbtree` and `is_bst` true | ✅ |
| Search existing keys | `search t3 1/2/3` returns `Some 1/2/3` | ✅ |
| Search missing keys | `search t3 0/4` returns `None` | ✅ |
| Delete correctness | After deleting 1: `mem 1 = false`, `mem 2/3 = true` | ✅ |
| Delete preserves RB/BST | `is_rbtree t4 = true`, `is_bst t4 = true` | ✅ |

### Key Observation: Okasaki vs CLRS Tree Shapes

Both implementations produce valid RB-BST trees, but with different colorings:

| After insert 3, 1, 2 | Okasaki | CLRS |
|---|---|---|
| Children of root | **Black** children | **Red** children |
| Root key | 2 | 2 |
| Shape | `Node Black (Node Black Leaf 1 Leaf) 2 (Node Black Leaf 3 Leaf)` | `Node Black (Node Red Leaf 1 Leaf) 2 (Node Red Leaf 3 Leaf)` |

Both are valid RB trees. The difference arises because Okasaki's balance function
performs unconditional black promotion, while CLRS's rotation-based fixup preserves
more red nodes when no uncle recoloring is needed.

### Pulse API Test (`test_clrs_rbtree_insert_search_delete`)

Same lifecycle as the Okasaki test but using CLRSImpl API functions, which take
an additional `parent` parameter (None for root operations):

1. `rb_new()` → empty tree
2. `rb_insert_v tree 3/1/2 None` → successive inserts
3. `rb_search_v tree 2/4` → verify search precision
4. `rb_delete_v tree 1 None` → delete key 1
5. `rb_search_v tree 1/3` → verify deletion effects
6. `free_valid_rbtree tree` → cleanup

---

## Spec Quality Assessment

### Preconditions
All preconditions are satisfiable in natural usage. The additional `parent`
parameter (needed for CLRS's parent-pointer representation) must be provided
as `None #CI.rb_node_ptr` for root operations. **No issues found.**

### Postconditions
- **`rb_insert_v`**: Uses `CS.clrs_insert` (rotation-based). Fully deterministic,
  output uniquely determined. **Fully precise.**
- **`rb_search_v`**: Returns `S.search 'ft k` (shared search spec). **Fully precise.**
- **`rb_delete_v`**: Uses `CS.clrs_delete` (rotation-based). Fully deterministic.
  **Fully precise.**

### Verdict

The `CLRSImpl.fsti` specification is **complete and precise**. No spec
incompleteness or imprecision issues found.
