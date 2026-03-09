# Red-Black Tree — Okasaki-Style (CLRS §13.1–13.4)

## Top-Level Signatures

Here are the top-level signatures proven about the Okasaki-style red-black tree
in `CLRS.Ch13.RBTree.Impl.fsti`:

### Low-Level API

```fstar
fn rb_search (tree: rb_ptr) (k: int)
  preserves is_rbtree tree 'ft
  returns result: option int
  ensures pure (result == S.search 'ft k)

fn rb_insert (tree: rb_ptr) (k: int)
  requires is_rbtree tree 'ft
  returns y: rb_ptr
  ensures is_rbtree y (S.insert 'ft k)

fn rb_delete (tree: rb_ptr) (k: int)
  requires is_rbtree tree 'ft
  returns y: rb_ptr
  ensures is_rbtree y (S.delete 'ft k)

fn free_rbtree (tree: rb_ptr)
  requires is_rbtree tree 'ft
  ensures emp
```

### Validated API (bundles BST + RB invariants)

```fstar
fn rb_new ()
  requires emp
  returns y: rb_ptr
  ensures valid_rbtree y S.Leaf

fn rb_search_v (tree: rb_ptr) (k: int)
  preserves valid_rbtree tree 'ft
  returns result: option int
  ensures pure (result == S.search 'ft k)

fn rb_insert_v (tree: rb_ptr) (k: int)
  requires valid_rbtree tree 'ft
  returns y: rb_ptr
  ensures valid_rbtree y (S.insert 'ft k) **
          pure (S.mem k (S.insert 'ft k) = true)

fn rb_delete_v (tree: rb_ptr) (k: int)
  requires valid_rbtree tree 'ft
  returns y: rb_ptr
  ensures valid_rbtree y (S.delete 'ft k) **
          pure (S.mem k (S.delete 'ft k) = false)

fn free_valid_rbtree (tree: rb_ptr)
  requires valid_rbtree tree 'ft
  ensures emp
```

### Complexity-Aware API

```fstar
fn rb_search_log (tree: rb_ptr) (k: int)
  preserves valid_rbtree tree 'ft
  returns result: option int
  ensures pure (result == S.search 'ft k /\
                C.search_ticks 'ft k <= S.height 'ft + 1)

fn rb_insert_log (tree: rb_ptr) (k: int)
  requires valid_rbtree tree 'ft
  returns y: rb_ptr
  ensures valid_rbtree y (S.insert 'ft k) **
          pure (S.mem k (S.insert 'ft k) = true /\
                C.insert_ticks 'ft k <= S.height 'ft + 2)

fn rb_delete_log (tree: rb_ptr) (k: int)
  requires valid_rbtree tree 'ft
  returns y: rb_ptr
  ensures valid_rbtree y (S.delete 'ft k) **
          pure (S.mem k (S.delete 'ft k) = false /\
                C.delete_ticks 'ft k <= 2 * S.height 'ft + 2)
```

### Parameters

* `tree` is a nullable pointer to an RB node (`rb_ptr = option rb_node_ptr`).
  The ghost variable `'ft` captures the pure tree shape of type `rbtree`.

* `k` is the key to search/insert/delete (unbounded `int`).

### Node Type

```fstar
noeq
type rb_node = {
  key:   int;
  color: S.color;
  left:  rb_ptr;
  right: rb_ptr;
}
```

No parent pointer — this is a pure functional Okasaki-style implementation.

### Separation Logic Predicates

```fstar
let rec is_rbtree (ct: rb_ptr) (ft: S.rbtree)
  : Tot slprop (decreases ft)
  = match ft with
    | S.Leaf -> pure (ct == None)
    | S.Node c l v r ->
      exists* (p: rb_node_ptr) (lct: rb_ptr) (rct: rb_ptr).
        pure (ct == Some p) **
        (p |-> { key = v; color = c; left = lct; right = rct }) **
        is_rbtree lct l **
        is_rbtree rct r

let valid_rbtree (ct: rb_ptr) (ft: S.rbtree) : slprop =
  is_rbtree ct ft ** pure (S.is_rbtree ft /\ S.is_bst ft)
```

`is_rbtree` asserts ownership of the heap tree matching the ghost tree.
`valid_rbtree` additionally bundles the RB-tree and BST ordering invariants.

## Auxiliary Definitions

### `rbtree` (from `CLRS.Ch13.RBTree.Spec`)

```fstar
type color = | Red | Black

type rbtree =
  | Leaf : rbtree
  | Node : c:color -> l:rbtree -> v:int -> r:rbtree -> rbtree
```

### `is_rbtree` (predicate, from `CLRS.Ch13.RBTree.Spec`)

```fstar
let is_rbtree (t: rbtree) : bool =
  is_root_black t && no_red_red t && same_bh t
```

Three properties: root is black, no two consecutive red nodes on any path,
and all root-to-leaf paths have the same number of black nodes.

### `is_bst` (from `CLRS.Ch13.RBTree.Spec`)

```fstar
let rec is_bst (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node _ l v r ->
    all_lt l v &&
    all_gt r v &&
    is_bst l && is_bst r
```

### `balance` — Okasaki-style (from `CLRS.Ch13.RBTree.Spec`)

```fstar
let balance (c: color) (l: rbtree) (v: int) (r: rbtree) : rbtree =
  match c, l, r with
  | Black, Node Red (Node Red a x b) y c_, _ ->
    Node Red (Node Black a x b) y (Node Black c_ v r)
  | Black, Node Red a x (Node Red b y c_), _ ->
    Node Red (Node Black a x b) y (Node Black c_ v r)
  | Black, _, Node Red (Node Red b y c_) z d ->
    Node Red (Node Black l v b) y (Node Black c_ z d)
  | Black, _, Node Red b y (Node Red c_ z d) ->
    Node Red (Node Black l v b) y (Node Black c_ z d)
  | _ -> Node c l v r
```

Four rotation cases that restore the no-red-red invariant.

### `insert` (from `CLRS.Ch13.RBTree.Spec`)

```fstar
let rec ins (t: rbtree) (k: int) : rbtree =
  match t with
  | Leaf -> Node Red Leaf k Leaf
  | Node c l v r ->
    if k < v then balance c (ins l k) v r
    else if k > v then balance c l v (ins r k)
    else Node c l v r

let insert (t: rbtree) (k: int) : rbtree =
  make_black (ins t k)
```

### `delete` — Kahrs-style (from `CLRS.Ch13.RBTree.Spec`)

```fstar
let rec del (t: rbtree) (k: int) : Tot rbtree (decreases t) =
  match t with
  | Leaf -> Leaf
  | Node c l v r ->
    if k < v then
      (match l with
       | Node Black _ _ _ -> balL (del l k) v r
       | _ -> Node Red (del l k) v r)
    else if k > v then
      (match r with
       | Node Black _ _ _ -> balR l v (del r k)
       | _ -> Node Red l v (del r k))
    else
      fuse l r

let delete (t: rbtree) (k: int) : rbtree =
  make_black (del t k)
```

Deletion uses Kahrs-style `balL`/`balR` rebalancing and `fuse` to merge
children of deleted nodes, then `make_black` to restore root-is-black.

## What Is Proven

### Functional Correctness (in `CLRS.Ch13.RBTree.Lemmas`)

* **Search**: `result == S.search 'ft k` — definitional correctness.

* **Insert membership**: `mem x (insert t k) ⟺ (x = k ∨ mem x t)`.

* **Delete membership**: `mem x (delete t k) ⟺ (mem x t ∧ x ≠ k)`.

* **Insert preserves BST**: `is_bst t ⟹ is_bst (insert t k)`.

* **Delete preserves BST**: `is_bst t ⟹ is_bst (delete t k)`.

* **Insert preserves RB**: `is_rbtree t ⟹ is_rbtree (insert t k)`.

* **Delete preserves RB**: `is_rbtree t ∧ is_bst t ⟹ is_rbtree (delete t k) ∧ is_bst (delete t k)`.

* **Insert node count**: `node_count(insert t k) = if mem k t then node_count t else node_count t + 1`.

* **CLRS Theorem 13.1 (height bound)**:
  `is_rbtree t ∧ node_count t ≥ 1 ⟹ height t ≤ 2 · log2_floor(node_count t + 1)`.

* **Minimum/maximum**: Membership and optimality lemmas.

* **Successor/predecessor**: Correctness and optimality lemmas.

### Complexity (in `CLRS.Ch13.RBTree.Complexity`)

* `search_ticks t k ≤ height t + 1`
* `insert_ticks t k ≤ height t + 2`
* `delete_ticks t k ≤ 2 * height t + 2`
* `search_ticks t k ≤ 2 · log2_floor(n+1) + 1` (O(log n))
* `insert_ticks t k ≤ 2 · log2_floor(n+1) + 2` (O(log n))
* `delete_ticks t k ≤ 4 · log2_floor(n+1) + 2` (O(log n))

The delete constant is 4 (not 2) because `del` traverses a root-to-node path
(O(h)) and then `fuse` traverses the inner spines of the children (O(h)).

**Zero admits, zero assumes.** All proof obligations are mechanically discharged
by F\* and Z3.

## Specification Gaps and Limitations

1. **Balance operations are O(1) by convention.** The tick counters count
   recursive calls in `ins`/`del`/`fuse` but do not count work inside
   `balance`, `balL`, `balR`. These are non-recursive (O(1) pattern matches),
   so this is correct but the choice is implicit.

2. **Delete constant factor 4.** The `delete_ticks ≤ 4 · log2_floor(n+1) + 2`
   bound has a constant of 4 (2 from height bound × 2 from `del + fuse`). CLRS
   states O(lg n) without specifying the constant. The bound could likely be
   tightened.

3. **No amortized analysis.** CLRS notes that insert fixup does at most 2
   rotations and delete fixup at most 3 (§13.4). The specification counts
   all recursive calls equally and does not distinguish rotation count from
   recoloring count.

4. **Functional, not imperative rotations.** Okasaki-style balance replaces
   CLRS's explicit LEFT-ROTATE/RIGHT-ROTATE with a single pattern-matching
   function. This is semantically equivalent but structurally different from
   CLRS. The CLRS-faithful version is in `CLRS.Ch13.RBTree.CLRSImpl`.

5. **No parent pointers.** The `rb_node` type has no parent pointer. CLRS
   operations that walk upward (e.g., successor via parent) are implemented
   differently (top-down recursion in the pure spec).

6. **Duplicate keys silently ignored.** `ins` returns the tree unchanged when
   `k = v`. This is standard but not explicitly stated in the postcondition.

7. **Height bound requires `node_count ≥ 1`.** The logarithmic complexity
   bounds require the tree to be non-empty. Empty trees are handled separately
   as O(1) special cases.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Search | O(log n) ≤ 2·lg(n+1)+1 | ✅ Pure tick function | Upper bound |
| Insert | O(log n) ≤ 2·lg(n+1)+2 | ✅ Pure tick function | Upper bound |
| Delete | O(log n) ≤ 4·lg(n+1)+2 | ✅ Pure tick function | Upper bound |

The tick functions (`search_ticks`, `insert_ticks`, `delete_ticks`) are defined
as pure recursive functions mirroring the spec's recursion structure. The Pulse
complexity-aware API postconditions state the height-based bounds directly.

## Proof Structure

The proof is organized in layers:

1. **Pure spec** (`CLRS.Ch13.RBTree.Spec`): Defines the `rbtree` type, BST and
   RB properties, Okasaki-style `balance`/`ins`/`insert`, Kahrs-style
   `balL`/`balR`/`fuse`/`del`/`delete`, and helper predicates.

2. **Lemmas** (`CLRS.Ch13.RBTree.Lemmas`): Proves CLRS Theorem 13.1
   (height ≤ 2·bh, n ≥ 2^bh - 1), insert/delete membership, BST/RB
   preservation, balance case correctness, min/max/successor/predecessor.

3. **Complexity** (`CLRS.Ch13.RBTree.Complexity`): Defines tick counters for
   search/insert/delete, proves height-based bounds, combines with Theorem 13.1
   for logarithmic bounds.

4. **Pulse implementation** (`CLRS.Ch13.RBTree.Impl.fst`): Three API tiers:
   * Low-level: Direct `is_rbtree` slprop manipulation.
   * Validated: Bundles `is_rbtree + is_bst` in `valid_rbtree`.
   * Complexity-aware: Adds tick bounds to postconditions.

   The Pulse implementation uses a `balance_case` classifier to dispatch to the
   correct rotation without deep pattern matching on pointers:
   ```fstar
   type balance_case = BC_LL | BC_LR | BC_RL | BC_RR | BC_None
   ```

## Files

| File | Role |
|------|------|
| `CLRS.Ch13.RBTree.Impl.fsti` | Public interface (3 API tiers) |
| `CLRS.Ch13.RBTree.Impl.fst` | Pulse implementation |
| `CLRS.Ch13.RBTree.Spec.fst` | Pure spec (type, properties, operations) |
| `CLRS.Ch13.RBTree.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch13.RBTree.Lemmas.fst` | Lemma proofs (Theorem 13.1, preservation) |
| `CLRS.Ch13.RBTree.Complexity.fsti` | Tick function signatures |
| `CLRS.Ch13.RBTree.Complexity.fst` | Tick function proofs |
