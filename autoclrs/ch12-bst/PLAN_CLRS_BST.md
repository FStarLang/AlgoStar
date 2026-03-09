# PLAN: Pointer-Based BST (CLRS Ch12) — COMPLETED

## Summary

Renamed array-based BST files to `BSTArray` and implemented a pointer-based BST
(`CLRS.Ch12.BST.fst`) following CLRS Chapter 12 exactly.

## Stage 1: Rename — ✅ DONE

Six array-specific files renamed from `CLRS.Ch12.BST.*` to `CLRS.Ch12.BSTArray.*`.
Five representation-independent spec files kept as `BST.*`.
All 11 modules verify after rename.

## Stage 2: Pointer-Based BST — ✅ DONE

`CLRS.Ch12.BST.fst` (580 LOC, 0 admits):

| Operation | CLRS § | Status | Postcondition |
|-----------|--------|--------|---------------|
| `bst_node` type | §12.1 | ✅ | `{ key; left; right; p }` with parent pointers |
| `bst_subtree` slprop | §12.1 | ✅ | Recursive ownership tying pointers to ghost `bst` tree |
| TREE-SEARCH | §12.2 | ✅ | `result == bst_search t k` |
| TREE-MINIMUM | §12.2 | ✅ | `bst_minimum t == Some result` |
| TREE-MAXIMUM | §12.2 | ✅ | `bst_maximum t == Some result` |
| TREE-INSERT | §12.3 | ✅ | `bst_subtree y (bst_insert t k) parent` |
| TREE-DELETE | §12.3 | ✅ | `bst_subtree result (bst_delete t k) parent` |
| TREE-FREE | — | ✅ | Deallocates all nodes |
| TREE-SUCCESSOR | §12.2 | Deferred | Requires zipper for parent walk |
| TREE-PREDECESSOR | §12.2 | Deferred | Symmetric to SUCCESSOR |
