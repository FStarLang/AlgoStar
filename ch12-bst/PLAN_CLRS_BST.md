# PLAN: Pointer-Based BST (CLRS Ch12)

## Goal

CLRS Chapter 12 describes a pointer-based BST where each node has `left`, `right`,
and `p` (parent) fields. The existing `ch12-bst/` implements an **array-based** BST
using implicit heap indexing (`2*i+1`, `2*i+2`). We rename the array-based files to
`BSTArray` and create a new pointer-based implementation `CLRS.Ch12.BST.fst` that
follows CLRS exactly.

## Stage 1: Rename Array-Based Files → `BSTArray`

Six files are array-specific and get renamed:

| Old Name | New Name | Reason |
|---|---|---|
| `CLRS.Ch12.BST.fst` | `CLRS.Ch12.BSTArray.fst` | Pulse array-based search/insert/inorder |
| `CLRS.Ch12.BST.Delete.fst` | `CLRS.Ch12.BSTArray.Delete.fst` | Pulse array-based min/max/succ/pred/delete |
| `CLRS.Ch12.BST.ArrayPredicates.fst` | `CLRS.Ch12.BSTArray.Predicates.fst` | Array predicates (well_formed_bst, etc.) |
| `CLRS.Ch12.BST.Complexity.fst` | `CLRS.Ch12.BSTArray.Complexity.fst` | Array structural bounds (tree_height, node_depth) |
| `CLRS.Ch12.BST.Spec.fst` | `CLRS.Ch12.BSTArray.Spec.fst` | Pure spec for array-based search |
| `CLRS.Ch12.BST.Refinement.fst` | `CLRS.Ch12.BSTArray.Refinement.fst` | Array-to-inductive refinement |

Five files stay as `BST.*` (representation-independent pure specs):

| File | Reason to keep |
|---|---|
| `CLRS.Ch12.BST.Spec.Complete.fst` | Inductive BST type + operations — shared by both representations |
| `CLRS.Ch12.BST.Spec.Complexity.fst` | Pure O(h) bounds on inductive BST |
| `CLRS.Ch12.BST.Insert.Spec.fst` | Key-set insert theorem |
| `CLRS.Ch12.BST.Delete.Spec.fst` | Key-set delete theorem |
| `CLRS.Ch12.BST.KeySet.fst` | Shared list_to_set / key_set |

After rename: update all `module` declarations and `open`/`module` imports. Rebuild.

## Stage 2: Implement Pointer-Based BST (`CLRS.Ch12.BST.fst`)

### Node type (CLRS §12.1 + ch10 DLL patterns)

```fstar
noeq type bst_node = { key: int; left: dptr; right: dptr; p: dptr }
let dptr = option (box bst_node)
```

Following the ch10 DLL pattern: `box` for heap-allocated mutable nodes, `option`
for nullable pointers.

### Separation logic predicate

```fstar
// Subtree ownership: ptr points to a tree t, with parent pointer = parent
let rec bst_subtree (ptr: dptr) (t: bst) (parent: dptr)
  : Tot slprop (decreases t)
  = match t with
    | Leaf -> pure (ptr == None)
    | Node l k r ->
      exists* (bp: box bst_node) (v: bst_node).
        pure (ptr == Some bp) **
        pts_to bp v **
        pure (v.key == k /\ v.p == parent) **
        bst_subtree v.left l (Some bp) **
        bst_subtree v.right r (Some bp)
```

Reuses `bst` from `Spec.Complete` as the ghost tree.

### Operations (CLRS order)

| # | CLRS Operation | Approach |
|---|---|---|
| 1 | INORDER-TREE-WALK (§12.1) | `fn rec` following `bst_subtree` |
| 2 | TREE-SEARCH (§12.2) | Iterative while loop, returns `dptr` |
| 3 | TREE-MINIMUM (§12.2) | Follow `left` pointers to `None` |
| 4 | TREE-MAXIMUM (§12.2) | Follow `right` pointers to `None` |
| 5 | TREE-SUCCESSOR (§12.2) | Right min, or walk up via `p` |
| 6 | TREE-PREDECESSOR (§12.2) | Symmetric to successor |
| 7 | TREE-INSERT (§12.3) | Trailing pointer `y`, pointer surgery |
| 8 | TRANSPLANT (§12.3) | Replace subtree, update parent |
| 9 | TREE-DELETE (§12.3) | Full 4-case CLRS delete using TRANSPLANT |

### Key design decisions

- **Ghost tree**: Each operation gets the ghost `bst` tree as an erased parameter and
  must produce an updated ghost tree in the postcondition.
- **Factor/unfactor**: Ghost functions to decompose `bst_subtree (Node l k r)` into
  separate ownership of the root node + left/right subtrees (like DLL's `factor_dls`).
- **BST validity**: Proven via `bst_valid` from `Spec.Complete`.
- **Refinement**: Ghost tree IS the `bst` from `Spec.Complete`, so the refinement is
  immediate (no separate abstraction function needed).

### Challenges

- **TRANSPLANT** modifies parent pointers, requiring careful slprop rewriting.
- **DELETE case (d)** (successor not right child) involves splicing `y` out and replacing
  `z`, requiring multiple pointer updates with ghost tree transformations.
- **Walk-up via parent** (SUCCESSOR lines 3–7) needs a "path to root" ghost argument
  to prove termination and correctness.
