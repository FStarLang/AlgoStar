# CLRS Chapter 12: Binary Search Trees

## Verification Status

**ZERO ADMITS.** Every module in this chapter — including the pointer-based
BST, array-based BST, pure specification, complexity analysis, and all
key-set lemmas — is fully verified with no `admit()`, `assume()`, or `sorry`
calls.

## Overview

This directory contains two verified implementations of binary search trees
following CLRS §12.1–12.3:

1. **Pointer-based BST** (`BST.Impl.fst`): heap-allocated nodes with mutable
   fields and parent pointers, connected by a recursive separation-logic
   predicate `bst_subtree`. Full CLRS API: search, insert, delete, minimum,
   maximum, free.

2. **Array-based BST** (`BSTArray.Impl.fst`): flat array layout where node
   *i* has left child at `2i + 1` and right child at `2i + 2`. Search,
   insert, delete, inorder walk, minimum, maximum, successor, predecessor.

Both are backed by a shared **pure specification** (`BST.Spec.fst`) with
inductive `bst` type, validity predicate, and all CLRS operations defined
functionally, plus **key-set theorems** proved using `FStar.FiniteSet`.

## Algorithm Summary

| Operation | CLRS § | Pointer-based | Array-based | Complexity (proven) |
|---|---|---|---|---|
| TREE-SEARCH | §12.2 | `tree_search` | `tree_search` | O(h) |
| TREE-MINIMUM | §12.2 | `tree_minimum` | `tree_minimum` | O(h) |
| TREE-MAXIMUM | §12.2 | `tree_maximum` | — | O(h) |
| TREE-INSERT | §12.3 | `tree_insert` | `tree_insert` | O(h) |
| TREE-DELETE | §12.3 | `tree_delete` | `tree_delete` | O(h) |
| TREE-SUCCESSOR | §12.2 | — | `tree_successor` | O(h) |
| TREE-PREDECESSOR | §12.2 | — | `tree_predecessor` | O(h) |
| INORDER-WALK | §12.1 | — | `inorder_walk` | O(n) |
| Admits | — | **0** | **0** | — |

All complexities are O(h) where h is the tree height.

## Pure Specification (`CLRS.Ch12.BST.Spec`)

The inductive BST type:

```fstar
type bst =
  | Leaf : bst
  | Node : left:bst -> key:int -> right:bst -> bst
```

The validity predicate uses inorder traversal bounds:

```fstar
let rec bst_valid (t: bst) : bool =
  match t with
  | Leaf -> true
  | Node left key right ->
      bst_valid left && bst_valid right &&
      all_less key (bst_inorder left) &&
      all_greater key (bst_inorder right)
```

All pure operations (`bst_search`, `bst_insert`, `bst_delete`, `bst_minimum`,
`bst_maximum`) follow the CLRS algorithms directly. The delete operation uses
the in-order successor (minimum of right subtree) for the two-children case.

### Key-Set Theorems (strongest guarantees)

| Theorem | Statement |
|---|---|
| `insert_key_set_lemma` | `key_set(insert(t,k)) = key_set(t) ∪ {k}` |
| `delete_key_set_lemma` | `key_set(delete(t,k)) = key_set(t) \ {k}` |
| `bst_search_correct` | `bst_search t k ⟺ mem k (bst_inorder t)` |
| `bst_insert_valid` | `bst_valid t ⟹ bst_valid (bst_insert t k)` |
| `bst_delete_valid` | `bst_valid t ⟹ bst_valid (bst_delete t k)` |
| `bst_inorder_sorted` | `bst_valid t ⟹ sorted (bst_inorder t)` |

The key-set theorems use `FStar.FiniteSet.Base` and are the **strongest
functional correctness guarantees**: they exactly characterize the set of keys
before and after each operation, not just that "the key is present" or "the
key is absent."

## Pointer-Based BST (`CLRS.Ch12.BST.Impl`)

### Node Type and Separation Logic Predicate

```fstar
noeq type bst_node = {
  key: int; left: bst_ptr; right: bst_ptr; p: bst_ptr }
```

The recursive separation-logic predicate `bst_subtree ct ft parent` links the
concrete pointer structure to a pure `bst` ghost shape. A `Leaf` requires
`ct == None`; a `Node l k r` requires a heap-allocated node whose fields
recursively satisfy `bst_subtree`.

### Correctness Theorems (`CLRS.Ch12.BST.Impl.fsti`)

#### `tree_search`

```fstar
fn rec tree_search (tree: bst_ptr) (k: int) (ticks: GR.ref nat)
  preserves bst_subtree tree 'ft 'parent
  requires GR.pts_to ticks 'n
  returns result: bool
  ensures GR.pts_to ticks ('n + bst_search_ticks 'ft k) **
          pure (result == bst_search 'ft k)
```

- `result == bst_search 'ft k`: the result exactly matches the pure
  specification's search.
- `bst_subtree` preserved (read-only).
- Ticks incremented by the *exact* pure tick count.

#### `tree_insert`

```fstar
fn rec tree_insert (tree: bst_ptr) (k: int) (parent: bst_ptr) (ticks: GR.ref nat)
  requires bst_subtree tree 'ft parent ** GR.pts_to ticks 'n
  returns y: bst_ptr
  ensures bst_subtree y (bst_insert 'ft k) parent **
          GR.pts_to ticks ('n + bst_insert_ticks 'ft k)
```

- The output pointer represents exactly `bst_insert 'ft k` — the pure
  specification applied to the ghost tree.
- Parent pointers are correctly maintained.

#### `tree_delete`

```fstar
fn rec tree_delete (tree: bst_ptr) (k: int) (parent: bst_ptr) (ticks: GR.ref nat)
  requires bst_subtree tree 'ft parent ** GR.pts_to ticks 'n
  returns result: bst_ptr
  ensures bst_subtree result (bst_delete 'ft k) parent **
          GR.pts_to ticks ('n + bst_delete_ticks 'ft k)
```

- Handles all four CLRS cases (leaf, one child left, one child right, two children).
- The result tree matches `bst_delete 'ft k` exactly.
- Freed nodes are deallocated.

### Strongest Guarantees

Each operation's postcondition says the resulting pointer structure represents
*exactly* the pure specification applied to the ghost tree. Combined with the
key-set theorems from `BST.Lemmas`, this gives the complete CLRS correctness:

- After `tree_insert`, `k ∈ key_set(result)` and
  `key_set(result) = key_set(old) ∪ {k}`.
- After `tree_delete`, `k ∉ key_set(result)` and
  `key_set(result) = key_set(old) \ {k}`.

## Array-Based BST (`CLRS.Ch12.BSTArray.Impl`)

### Layout

Node `i` has:
- Left child at index `2*i + 1`
- Right child at index `2*i + 2`
- `keys[i]`: the key (if `valid[i]`)
- `valid[i]`: whether the node is present

### Key Postconditions

**Search:**
- Found: returns `Some idx` with `keys[idx] == key` and `valid[idx] == true`.
- Not found: returns `None` with `¬(key_in_subtree keys valid cap 0 key)`.

**Insert:**
- Preserves `well_formed_bst keys valid cap 0 lo hi`.
- On success, the key exists at some index in the resulting arrays.
- On failure (tree full), arrays unchanged.

### Refinement Bridge (`BSTArray.Refinement`)

The refinement module connects the array-based BST to the pure specification
via `valid_refinement` and `search_refinement`, proving that the array layout
correctly implements the abstract BST.

## Complexity

### Pointer-Based BST

All operations have **exact tick counting** via ghost references:

| Operation | Tick function | Bound |
|---|---|---|
| `tree_search` | `bst_search_ticks t k` | `≤ bst_height t` |
| `tree_minimum` | `bst_minimum_ticks t` | `≤ bst_height t` |
| `tree_maximum` | `bst_maximum_ticks t` | `≤ bst_height t` |
| `tree_insert` | `bst_insert_ticks t k` | `≤ bst_height t` |
| `tree_delete` | `bst_delete_ticks t k` | `≤ 4 * bst_height t + 1` |

Additional bounds:
- `insert_height_bound`: `height(insert(t,k)) ≤ height(t) + 1`
- `delete_height_bound`: `height(delete(t,k)) ≤ height(t)`
- `delete_minimum_bounded`: deleting minimum costs `≤ 2 * height`

### Array-Based BST

Height is `⌊log₂(cap)⌋`. All operations are bounded by `tree_height(cap)`.

| Theorem | Statement |
|---|---|
| `node_depth_bounded` | `node_depth(i) ≤ tree_height(cap)` for all `i < cap` |
| `search_complexity_bound` | Search visits at most `h + 1` nodes |
| `balanced_tree_height` | For balanced trees, `h = Θ(log n)` |

**Gap:** Complexity is O(h) where h is tree height. Since there is no balancing
guarantee, h could be O(n) in the worst case (degenerate/linear tree). See
Chapter 13 (red-black trees) for O(lg n) bounds.

## Limitations

- **No balancing.** Tree height can be O(n) in the worst case. The O(h) bounds
  are tight but h itself is not bounded.
- **Pointer-based BST delete tick bound.** Delete cost is `≤ 4h + 1` (not h)
  due to the two-children case requiring both finding the minimum of the right
  subtree and recursively deleting it.
- **Array-based BST capacity.** Fixed capacity `cap < 32768` (fits in 16 bits
  for child index arithmetic).
- **Array-based delete is simplified.** Marks the node invalid (orphaning
  children) rather than performing a full CLRS transplant. This is correct
  for the verified postcondition but does not reclaim the subtree structure.
- **No balancing ⟹ no O(lg n) guarantee.** Use Chapter 13 (red-black trees)
  for logarithmic worst-case bounds.

## File Inventory

| File | Role | Admits |
|---|---|---|
| `CLRS.Ch12.BST.Spec.fst` | Pure inductive BST type, all operations, correctness lemmas | 0 |
| `CLRS.Ch12.BST.KeySet.fst` | `list_to_set`, `key_set`, FiniteSet conversion lemmas | 0 |
| `CLRS.Ch12.BST.Insert.Spec.fst` | `insert_key_set_lemma`, `theorem_insert_preserves_bst` | 0 |
| `CLRS.Ch12.BST.Delete.Spec.fst` | `delete_key_set_lemma` | 0 |
| `CLRS.Ch12.BST.Lemmas.fsti` | Unified correctness interface | 0 |
| `CLRS.Ch12.BST.Lemmas.fst` | Unified correctness proofs | 0 |
| `CLRS.Ch12.BST.Complexity.fsti` | Tick functions and O(h) bounds interface | 0 |
| `CLRS.Ch12.BST.Complexity.fst` | Complexity proofs | 0 |
| `CLRS.Ch12.BST.Impl.fsti` | Pointer-based BST: types, slprop, signatures | 0 |
| `CLRS.Ch12.BST.Impl.fst` | Pointer-based BST: Pulse implementation | 0 |
| `CLRS.Ch12.BSTArray.Predicates.fst` | Array BST predicates (`well_formed_bst`, etc.) | 0 |
| `CLRS.Ch12.BSTArray.Spec.fst` | Array BST pure spec, search/insert sound/complete | 0 |
| `CLRS.Ch12.BSTArray.Impl.fsti` | Array BST: types, signatures | 0 |
| `CLRS.Ch12.BSTArray.Impl.fst` | Array BST: Pulse implementation | 0 |
| `CLRS.Ch12.BSTArray.Delete.fst` | Array BST: delete, minimum, successor, predecessor | 0 |
| `CLRS.Ch12.BSTArray.Lemmas.fsti` | Array BST refinement interface | 0 |
| `CLRS.Ch12.BSTArray.Lemmas.fst` | Array BST refinement proofs | 0 |
| `CLRS.Ch12.BSTArray.Refinement.fst` | Array ↔ pure BST correspondence | 0 |
| `CLRS.Ch12.BSTArray.Complexity.fsti` | Array BST complexity interface | 0 |
| `CLRS.Ch12.BSTArray.Complexity.fst` | Array BST complexity proofs | 0 |

## Building and Verification

```bash
cd ch12-bst
make          # Verify all modules
```

The Makefile includes `$(PULSE_ROOT)/mk/test.mk` for the standard Pulse build
infrastructure.

## References

- CLRS 3rd Edition, Chapter 12: Binary Search Trees, §12.1–12.3
- Theorem 12.2: Each operation on a BST of height h runs in O(h) time
