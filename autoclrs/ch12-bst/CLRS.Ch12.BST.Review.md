# Pointer-Based Binary Search Tree (CLRS §12.1–12.3)

## Top-Level Signatures

Here are the top-level signatures proven about the pointer-based BST in
`CLRS.Ch12.BST.Impl.fsti`:

### `tree_search`

```fstar
fn rec tree_search (tree: bst_ptr) (k: int) (ticks: GR.ref nat)
  preserves bst_subtree tree 'ft 'parent
  requires GR.pts_to ticks 'n
  returns result: bool
  ensures GR.pts_to ticks ('n + bst_search_ticks 'ft k) **
          pure (result == bst_search 'ft k)
```

### `tree_minimum`

```fstar
fn rec tree_minimum (tree: bst_ptr) (bp: bst_node_ptr) (ticks: GR.ref nat)
  preserves bst_subtree tree 'ft 'parent
  requires GR.pts_to ticks 'n ** pure (tree == Some bp)
  returns result: int
  ensures GR.pts_to ticks ('n + bst_minimum_ticks 'ft) **
          pure (bst_minimum 'ft == Some result)
```

### `tree_maximum`

```fstar
fn rec tree_maximum (tree: bst_ptr) (bp: bst_node_ptr) (ticks: GR.ref nat)
  preserves bst_subtree tree 'ft 'parent
  requires GR.pts_to ticks 'n ** pure (tree == Some bp)
  returns result: int
  ensures GR.pts_to ticks ('n + bst_maximum_ticks 'ft) **
          pure (bst_maximum 'ft == Some result)
```

### `tree_insert`

```fstar
fn rec tree_insert (tree: bst_ptr) (k: int) (parent: bst_ptr) (ticks: GR.ref nat)
  requires bst_subtree tree 'ft parent ** GR.pts_to ticks 'n
  returns y: bst_ptr
  ensures bst_subtree y (bst_insert 'ft k) parent **
          GR.pts_to ticks ('n + bst_insert_ticks 'ft k)
```

### `tree_delete`

```fstar
fn rec tree_delete (tree: bst_ptr) (k: int) (parent: bst_ptr) (ticks: GR.ref nat)
  requires bst_subtree tree 'ft parent ** GR.pts_to ticks 'n
  returns result: bst_ptr
  ensures bst_subtree result (bst_delete 'ft k) parent **
          GR.pts_to ticks ('n + bst_delete_ticks 'ft k)
```

### `free_bst`

```fstar
fn rec free_bst (tree: bst_ptr)
  requires bst_subtree tree 'ft 'parent
  ensures emp
```

### Parameters

* `tree` is a nullable pointer to a BST node (`bst_ptr = option bst_node_ptr`).
  The ghost variable `'ft` captures the pure tree shape of type `bst`.

* `k` is the key to search/insert/delete (unbounded `int`).

* `parent` is the expected parent pointer for the root of the subtree (for
  maintaining CLRS parent-pointer invariant).

* `ticks` is a **ghost counter** — a ghost reference to a natural number used to
  count operations. Ghost values are erased at runtime.

### Node Type

```fstar
noeq
type bst_node = {
  key:   int;
  left:  bst_ptr;
  right: bst_ptr;
  p:     bst_ptr;     // parent pointer (CLRS §12.1)
}
```

### Separation Logic Predicate

```fstar
let rec bst_subtree (ct: bst_ptr) (ft: bst) (parent: bst_ptr)
  : Tot slprop (decreases ft)
  = match ft with
    | Leaf -> pure (ct == None)
    | Node l k r ->
      exists* (bp: bst_node_ptr) (node: bst_node).
        pure (ct == Some bp) **
        (bp |-> node) **
        pure (node.key == k /\ node.p == parent) **
        bst_subtree node.left l (Some bp) **
        bst_subtree node.right r (Some bp)
```

This recursively asserts ownership of all nodes in the subtree, linking each
node's key and parent pointer to the pure ghost tree `ft`. The `preserves`
keyword on search/min/max means the slprop is returned unchanged.

### Postconditions

All five operations have **definitional postconditions**: the result and the
ghost tree in the postcondition are defined by applying the corresponding pure
specification function to the ghost tree in the precondition.

* **Search**: `result == bst_search 'ft k` — returns true iff key is in tree.
* **Minimum**: `bst_minimum 'ft == Some result` — returns the minimum key.
* **Maximum**: `bst_maximum 'ft == Some result` — returns the maximum key.
* **Insert**: Resulting tree is `bst_insert 'ft k` — the pure insertion.
* **Delete**: Resulting tree is `bst_delete 'ft k` — the pure deletion.

Complexity is stated by exact tick counts:
`ticks_after == ticks_before + f('ft, k)` where `f` is the corresponding tick
function from `CLRS.Ch12.BST.Complexity`.

## Auxiliary Definitions

### `bst` (from `CLRS.Ch12.BST.Spec`)

```fstar
type bst =
  | Leaf : bst
  | Node : left:bst -> key:int -> right:bst -> bst
```

### `bst_valid` (from `CLRS.Ch12.BST.Spec`)

```fstar
let rec bst_valid (t: bst) : bool =
  match t with
  | Leaf -> true
  | Node left key right ->
      bst_valid left &&
      bst_valid right &&
      all_less key (bst_inorder left) &&
      all_greater key (bst_inorder right)
```

Standard BST property via inorder-traversal bounds: all keys in the left subtree
are strictly less than the node's key, and all keys in the right subtree are
strictly greater. Uses auxiliary list predicates `all_less` and `all_greater`.

### `bst_search` (from `CLRS.Ch12.BST.Spec`)

```fstar
let rec bst_search (t: bst) (k: int) : bool =
  match t with
  | Leaf -> false
  | Node left key right ->
      if k = key then true
      else if k < key then bst_search left k
      else bst_search right k
```

### `bst_insert` (from `CLRS.Ch12.BST.Spec`)

```fstar
let rec bst_insert (t: bst) (k: int) : bst =
  match t with
  | Leaf -> Node Leaf k Leaf
  | Node left key right ->
      if k < key then Node (bst_insert left k) key right
      else if k > key then Node left key (bst_insert right k)
      else t
```

### `bst_delete` (from `CLRS.Ch12.BST.Spec`)

```fstar
let rec bst_delete (t: bst) (k: int) : bst =
  match t with
  | Leaf -> Leaf
  | Node left key right ->
      if k < key then
        Node (bst_delete left k) key right
      else if k > key then
        Node left key (bst_delete right k)
      else
        match left, right with
        | Leaf, Leaf -> Leaf
        | Leaf, _ -> right
        | _, Leaf -> left
        | _, _ ->
            match bst_minimum right with
            | Some successor_key ->
                Node left successor_key (bst_delete right successor_key)
            | None -> t
```

CLRS three-case deletion: no children → remove; one child → splice out;
two children → replace with in-order successor (minimum of right subtree).

### `key_set` (from `CLRS.Ch12.BST.KeySet`)

```fstar
let key_set (t: bst) : FS.set int =
  list_to_set (bst_inorder t)
```

Converts the inorder traversal to a finite set, enabling set-algebraic reasoning.

## What Is Proven

### Functional Correctness (in `CLRS.Ch12.BST.Lemmas`)

* **Search correctness**: `bst_search t k ⟺ mem k (bst_inorder t)` — search
  is equivalent to membership in the inorder traversal.

* **Insert key-set algebra**: `key_set(insert(t,k)) = key_set(t) ∪ {k}` — the
  strongest possible set-level insert specification.

* **Delete key-set algebra**: `key_set(delete(t,k)) = key_set(t) \ {k}` — the
  strongest possible set-level delete specification.

* **Insert preserves BST validity**: `bst_valid t ⟹ bst_valid (bst_insert t k)`.

* **Delete preserves BST validity**: `bst_valid t ⟹ bst_valid (bst_delete t k)`.

* **Inorder traversal is sorted**: `bst_valid t ⟹ sorted (bst_inorder t)`.

### Complexity (in `CLRS.Ch12.BST.Complexity`)

All operations are **exactly counted** via tick functions and bounded by tree
height:

* `bst_search_ticks t k ≤ bst_height t`
* `bst_minimum_ticks t ≤ bst_height t`
* `bst_maximum_ticks t ≤ bst_height t`
* `bst_insert_ticks t k ≤ bst_height t`
* `bst_delete_ticks t k ≤ 4 * bst_height t + 1`
* `bst_height (bst_insert t k) ≤ bst_height t + 1`
* `bst_height (bst_delete t k) ≤ bst_height t`

The delete bound is `O(h)` with constant factor 4 because two-children deletion
requires finding the successor (`bst_minimum_ticks`) plus deleting it
(`bst_delete_ticks` on the right subtree).

**Zero admits, zero assumes.** All proof obligations are mechanically discharged
by F\* and Z3.

## Specification Gaps and Limitations

1. **~~BST validity not in postconditions.~~** *(Addressed.)* The Pulse
   postconditions for `tree_insert` and `tree_delete` now include
   `pure (bst_valid 'ft ==> bst_valid (bst_insert 'ft k))` (resp. delete).
   Callers get BST validity preservation directly from the postcondition
   without importing the Lemmas module.

2. **No O(log n) bound for balanced trees.** The complexity bounds are all in
   terms of height `h`. For an unbalanced BST, `h` can be `n`. The
   specification does not assert balanced-tree properties (that requires
   Chapter 13's red-black trees).

3. **Delete complexity constant factor.** The delete ticks bound is
   `4 * bst_height t + 1`, which is O(h) but with a constant of 4. CLRS states
   O(h) without specifying the constant. The slack comes from bounding the
   two-children case conservatively.

4. **No successor/predecessor in Pulse interface.** The pure spec defines
   `bst_minimum` and `bst_maximum`, and the Pulse interface exposes them, but
   CLRS §12.2's TREE-SUCCESSOR and TREE-PREDECESSOR operations (which require
   parent-pointer traversal) are not exposed as separate Pulse operations.

5. **~~Duplicate keys silently ignored.~~** *(Addressed.)* The new lemma
   `bst_insert_noop_if_present` in `CLRS.Ch12.BST.Spec` (exported via
   `Lemmas.fsti` as `insert_noop_if_present`) makes explicit that
   `bst_valid t /\ bst_search t k ==> bst_insert t k == t`.

6. **Parent pointers maintained but not separately verified.** The
   `bst_subtree` slprop asserts `node.p == parent`, so parent pointers are
   structurally correct. However, no separate lemma states a parent-pointer
   invariant as a standalone property.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Search | O(h) ≤ height | ✅ Ghost ticks | Exact tick count |
| Minimum | O(h) ≤ height | ✅ Ghost ticks | Exact tick count |
| Maximum | O(h) ≤ height | ✅ Ghost ticks | Exact tick count |
| Insert | O(h) ≤ height | ✅ Ghost ticks | Exact tick count |
| Delete | O(h) ≤ 4h+1 | ✅ Ghost ticks | Upper bound |

The complexity is **fully linked** to the imperative implementation: the ghost
counter `ticks` is incremented by exactly `bst_search_ticks 'ft k` (etc.) in
the postcondition. These are not upper bounds — they are the exact tick counts
determined by the pure spec's structural recursion.

## Proof Structure

The proof follows a **spec-then-implement** pattern:

1. **Pure spec** (`CLRS.Ch12.BST.Spec`): Defines `bst`, `bst_valid`,
   `bst_search`, `bst_insert`, `bst_delete`, `bst_inorder`, and proves search
   correctness, insert/delete validity preservation.

2. **Key-set algebra** (`CLRS.Ch12.BST.Insert.Spec`, `CLRS.Ch12.BST.Delete.Spec`):
   Proves `key_set(insert(t,k)) = key_set(t) ∪ {k}` and
   `key_set(delete(t,k)) = key_set(t) \ {k}` using F\*'s `FiniteSet.Base`
   library. Delete uses inductive case analysis following CLRS's three cases.

3. **Complexity** (`CLRS.Ch12.BST.Complexity`): Defines tick functions mirroring
   the spec's recursion structure and proves they are bounded by tree height.

4. **Pulse implementation** (`CLRS.Ch12.BST.Impl.fst`): Recursive Pulse
   functions with `bst_subtree` slprop. Each operation's postcondition equates
   the result to the pure spec applied to the ghost tree.

Supporting lemma modules:
* `CLRS.Ch12.BST.Lemmas.fsti`: Unified interface exposing all key theorems.
* `CLRS.Ch12.BST.KeySet.fst`: `list_to_set`, `key_set`, membership lemmas.

## Files

| File | Role |
|------|------|
| `CLRS.Ch12.BST.Impl.fsti` | Public interface (types, slprop, signatures) |
| `CLRS.Ch12.BST.Impl.fst` | Pulse implementation |
| `CLRS.Ch12.BST.Spec.fst` | Pure BST spec (type, valid, search, insert, delete, correctness lemmas) |
| `CLRS.Ch12.BST.Complexity.fsti` | Tick functions + height bound signatures |
| `CLRS.Ch12.BST.Complexity.fst` | Complexity bound proofs |
| `CLRS.Ch12.BST.Insert.Spec.fst` | Insert key-set algebra proof |
| `CLRS.Ch12.BST.Delete.Spec.fst` | Delete key-set algebra proof |
| `CLRS.Ch12.BST.KeySet.fst` | `key_set`, `list_to_set` definitions |
| `CLRS.Ch12.BST.Lemmas.fsti` | Unified lemma interface |
| `CLRS.Ch12.BST.Lemmas.fst` | Lemma proofs (delegates to Insert.Spec, Delete.Spec) |
