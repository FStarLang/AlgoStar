# Red-Black Tree — CLRS-Style (CLRS §13.1–13.4)

## Top-Level Signatures

Here are the top-level signatures proven about the CLRS-faithful red-black tree
in `CLRS.Ch13.RBTree.CLRSImpl.fsti`:

### Low-Level API

```fstar
fn rb_search (tree: rb_ptr) (k: int)
  preserves rbtree_subtree tree 'ft 'parent
  returns result: option int
  ensures pure (result == S.search 'ft k)

fn rb_minimum (tree: rb_ptr) (bp: rb_node_ptr)
  preserves rbtree_subtree tree 'ft 'parent
  requires pure (tree == Some bp)
  returns result: int
  ensures pure (S.Node? 'ft /\ result == S.minimum 'ft)

fn rb_clrs_insert (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft parent
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_insert 'ft k) parent

fn rb_clrs_delete (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft 'old_parent
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_delete 'ft k) parent

fn free_rbtree (tree: rb_ptr)
  requires rbtree_subtree tree 'ft 'parent
  ensures emp
```

### Validated API (bundles BST + RB invariants)

```fstar
fn rb_new ()
  requires emp
  returns y: rb_ptr
  ensures valid_rbtree y S.Leaf (None #rb_node_ptr)

fn rb_search_v (tree: rb_ptr) (k: int)
  (#parent: G.erased rb_ptr)
  preserves valid_rbtree tree 'ft parent
  returns result: option int
  ensures pure (result == S.search 'ft k)

fn rb_insert_v (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (CS.clrs_insert 'ft k) parent **
          pure (S.mem k (CS.clrs_insert 'ft k) = true)

fn rb_delete_v (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (CS.clrs_delete 'ft k) parent **
          pure (S.mem k (CS.clrs_delete 'ft k) = false)

fn free_valid_rbtree (tree: rb_ptr)
  requires valid_rbtree tree 'ft 'parent
  ensures emp
```

### Parameters

* `tree` is a nullable pointer to an RB node (`rb_ptr = option rb_node_ptr`).
  The ghost variable `'ft` captures the pure tree shape of type `rbtree`.

* `k` is the key to search/insert/delete (unbounded `int`).

* `parent` is the expected parent pointer for the root of the subtree (CLRS
  parent-pointer invariant, as in the Chapter 12 BST).

### Node Type (with parent pointer)

```fstar
noeq
type rb_node = {
  key:   int;
  color: S.color;
  left:  rb_ptr;
  right: rb_ptr;
  p:     rb_ptr;     // parent pointer (CLRS §12.1)
}
```

Key difference from Okasaki: includes a `p` field for parent pointer, matching
CLRS's node representation.

### Separation Logic Predicates

```fstar
let rec rbtree_subtree (ct: rb_ptr) (ft: S.rbtree) (parent: rb_ptr)
  : Tot slprop (decreases ft)
  = match ft with
    | S.Leaf -> pure (ct == None)
    | S.Node c l v r ->
      exists* (bp: rb_node_ptr) (node: rb_node).
        pure (ct == Some bp) **
        (bp |-> node) **
        pure (node.key == v /\ node.color == c /\ node.p == parent) **
        rbtree_subtree node.left l (Some bp) **
        rbtree_subtree node.right r (Some bp)

let valid_rbtree (ct: rb_ptr) (ft: S.rbtree) (parent: rb_ptr) : slprop =
  rbtree_subtree ct ft parent ** pure (S.is_rbtree ft /\ S.is_bst ft)
```

Same structure as the Chapter 12 BST's `bst_subtree`, but additionally tracks
the node's color. `valid_rbtree` bundles `is_rbtree` and `is_bst`.

## Auxiliary Definitions

### Pure Spec Functions (from `CLRS.Ch13.RBTree.CLRSSpec`)

The CLRS-style spec defines rotation-based operations that mirror CLRS pseudocode:

#### `left_rotate` / `right_rotate` (§13.2)

```fstar
let left_rotate (t: rbtree) : rbtree =
  match t with
  | Node c a x (Node rc b y d) -> Node rc (Node c a x b) y d
  | _ -> t

let right_rotate (t: rbtree) : rbtree =
  match t with
  | Node c (Node lc a x b) y d -> Node lc a x (Node c b y d)
  | _ -> t
```

#### `clrs_insert` (§13.3)

```fstar
let rec clrs_ins (t: rbtree) (k: int) : Tot rbtree (decreases t) =
  match t with
  | Leaf -> Node Red Leaf k Leaf
  | Node c l v r ->
    if k < v then clrs_fixup_left c (clrs_ins l k) v r
    else if k > v then clrs_fixup_right c l v (clrs_ins r k)
    else t

let clrs_insert (t: rbtree) (k: int) : rbtree =
  make_black (clrs_ins t k)
```

Uses `clrs_fixup_left`/`clrs_fixup_right` which check uncle color:
* **Uncle Red (Case 1)**: Recolor only — no rotation.
* **Uncle Black (Cases 2/3)**: Rotate + recolor.

This directly follows CLRS §13.3 INSERT-FIXUP.

#### `clrs_delete` (§13.4)

```fstar
let rec clrs_del (t: rbtree) (k: int) : Tot (rbtree & bool) (decreases t) =
  match t with
  | Leaf -> (Leaf, false)
  | Node c l v r ->
    if k < v then
      let (l', deficit) = clrs_del l k in
      if deficit then clrs_resolve_left c l' v r
      else (Node c l' v r, false)
    else if k > v then
      let (r', deficit) = clrs_del r k in
      if deficit then clrs_resolve_right c l v r'
      else (Node c l v r', false)
    else
      match l, r with
      | Leaf, Leaf -> (Leaf, c = Black)
      | Leaf, Node _ rl rv rr -> (Node Black rl rv rr, false)
      | Node _ ll lv lr, Leaf -> (Node Black ll lv lr, false)
      | _, _ ->
        let sk = minimum r in
        let (r', deficit) = clrs_del r sk in
        if deficit then clrs_resolve_right c l sk r'
        else (Node c l sk r', false)

let clrs_delete (t: rbtree) (k: int) : rbtree =
  make_black (fst (clrs_del t k))
```

Returns `(result_tree, deficit_flag)` where `deficit = true` means the
subtree's black-height decreased by 1 (triggering fixup). Uses
`clrs_resolve_left`/`clrs_resolve_right` which implement CLRS §13.4's four
DELETE-FIXUP cases:

* **Case 1**: Sibling Red → rotate to make sibling Black, then recurse.
* **Case 2**: Sibling Black, both children Black → recolor sibling Red.
* **Case 3**: Sibling Black, near child Red → rotate to set up Case 4.
* **Case 4**: Sibling Black, far child Red → rotate + recolor.

Two-children deletion uses in-order successor replacement (`minimum r`), matching
CLRS exactly.

## What Is Proven

### Functional Correctness (in `CLRS.Ch13.RBTree.CLRSSpec`)

All proofs are fully verified with zero admits:

* **Insert membership**: `mem x (clrs_insert t k) ⟺ (x = k ∨ mem x t)`.

* **Delete membership**: `mem x (clrs_delete t k) ⟺ (mem x t ∧ x ≠ k)`.

* **Rotation lemmas**: `left_rotate`/`right_rotate` preserve `mem`, `all_lt`,
  `all_gt`, and `is_bst`.

* **Insert preserves BST**: `is_bst t ⟹ is_bst (clrs_insert t k)`.

* **Delete preserves BST**: `is_bst t ⟹ is_bst (clrs_delete t k)`.

* **Insert preserves RB**: `is_rbtree t ⟹ is_rbtree (clrs_insert t k)`.

* **Delete preserves RB**: `is_rbtree t ∧ is_bst t ⟹ is_rbtree (clrs_delete t k)`.

The CLRSSpec module is ~1184 lines of pure F\* proof covering every fixup case.

### Pulse Implementation Correctness

The Pulse postconditions link to `CS.clrs_insert` and `CS.clrs_delete`
(definitional correctness). Combined with the CLRSSpec proofs, this establishes
end-to-end correctness.

The validated API additionally provides:
* `S.mem k (CS.clrs_insert 'ft k) = true` — inserted key is present.
* `S.mem k (CS.clrs_delete 'ft k) = false` — deleted key is absent.

**Zero admits, zero assumes.** All proof obligations are mechanically discharged
by F\* and Z3.

## Specification Gaps and Limitations

1. **No complexity bounds.** Unlike the Okasaki-style implementation
   (`CLRS.Ch13.RBTree.Impl`), the CLRS-style implementation does not include
   ghost tick counters or complexity-aware API variants. There is no
   `CLRS.Ch13.RBTree.CLRSComplexity` module. The O(log n) bound can be inferred
   from the shared Spec module's height bound (Theorem 13.1) but is not proven
   for the CLRS-specific operations.

2. **Shares pure spec types with Okasaki.** The `rbtree` type, `is_rbtree`,
   `is_bst`, `search`, `mem`, etc. are imported from `CLRS.Ch13.RBTree.Spec`
   (the Okasaki module). The CLRS operations (`clrs_insert`, `clrs_delete`) are
   defined on the same type but are separate functions. No formal equivalence
   between `insert` (Okasaki) and `clrs_insert` (CLRS) is proven.

3. **Delete postcondition uses different parent parameter.** The `rb_clrs_delete`
   signature has `requires rbtree_subtree tree 'ft 'old_parent` but
   `ensures rbtree_subtree y ... parent` (a different, caller-provided parent).
   This is necessary because deletion may change the root, but means the caller
   must provide the correct parent.

4. **No separate rotation count.** CLRS §13.3–13.4 emphasizes that INSERT-FIXUP
   performs at most 2 rotations and DELETE-FIXUP at most 3. The specification
   does not separately count rotations vs. recolorings — these are bundled into
   the functional definition.

5. **Fixup is inlined, not modular.** The `clrs_fixup_left`/`clrs_fixup_right`
   and `clrs_resolve_left`/`clrs_resolve_right` functions inline the CLRS fixup
   logic. There is no separate `INSERT-FIXUP` or `DELETE-FIXUP` function that
   corresponds 1:1 to the CLRS pseudocode structure (which uses a while loop
   walking up parent pointers).

6. **Recursive, not iterative.** CLRS INSERT-FIXUP and DELETE-FIXUP are
   iterative (while loops walking up parent pointers). This implementation uses
   structural recursion on the tree shape, which is functionally equivalent but
   structurally different.

7. **Minimum required for delete but not separately exposed with ticks.** The
   `rb_minimum` operation is exposed in the low-level API but has no ghost tick
   counter.

## Key Difference from Okasaki Implementation

| Aspect | Okasaki (`CLRS.Ch13.RBTree.Impl`) | CLRS (`CLRS.Ch13.RBTree.CLRSImpl`) |
|--------|-----------------------------------|-------------------------------------|
| Insert fixup | Single `balance` function (4 rotation cases) | `clrs_fixup_left`/`right` (checks uncle color: Cases 1/2/3) |
| Delete | Kahrs-style `fuse` + `balL`/`balR` | Successor replacement + `clrs_resolve_left`/`right` (Cases 1–4) |
| Parent pointer | No | Yes (`p` field) |
| Complexity proof | ✅ O(log n) with tick functions | ❌ Not included |
| Minimum exposed | Via `S.minimum` (pure) | `rb_minimum` Pulse function |
| Operations | search, insert, delete | search, minimum, insert, delete |

Both implementations share the same `rbtree` pure type and `is_rbtree`/`is_bst`
predicates from `CLRS.Ch13.RBTree.Spec`.

## Proof Structure

1. **Shared pure spec** (`CLRS.Ch13.RBTree.Spec`): Provides `rbtree` type, BST
   and RB predicates, Okasaki balance/insert/delete. Shared between both
   implementations.

2. **CLRS-specific spec** (`CLRS.Ch13.RBTree.CLRSSpec`): ~1184 lines defining
   CLRS rotations, insert fixup, delete fixup, and proving:
   * Rotation preserves mem, all_lt, all_gt, is_bst
   * Fixup preserves mem, all_lt, all_gt, is_bst
   * Insert/delete preserve mem (membership algebra)
   * Insert/delete preserve is_bst
   * Insert/delete preserve is_rbtree (RB properties: same_bh, no_red_red,
     root_black)

3. **Pulse implementation** (`CLRS.Ch13.RBTree.CLRSImpl.fst`): Imperative
   implementation with parent pointers. Two API tiers:
   * Low-level: Direct `rbtree_subtree` slprop.
   * Validated: Bundles `is_rbtree + is_bst` in `valid_rbtree`.

## Files

| File | Role |
|------|------|
| `CLRS.Ch13.RBTree.CLRSImpl.fsti` | Public interface (types, slprop, signatures) |
| `CLRS.Ch13.RBTree.CLRSImpl.fst` | Pulse implementation |
| `CLRS.Ch13.RBTree.CLRSSpec.fst` | CLRS-style pure spec + full correctness proofs |
| `CLRS.Ch13.RBTree.Spec.fst` | Shared pure spec (types, properties, Okasaki operations) |
| `CLRS.Ch13.RBTree.Lemmas.fsti` | Shared lemma signatures |
| `CLRS.Ch13.RBTree.Lemmas.fst` | Shared lemma proofs (Theorem 13.1, etc.) |
