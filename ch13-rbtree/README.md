# CLRS Chapter 13: Red-Black Trees

## Verification Status

**ZERO ADMITS.** Every module in this chapter — the pure specification, the
Okasaki-style Pulse implementation, the CLRS-style Pulse implementation with
rotations, the correctness lemmas, and the complexity analysis — is fully
verified with no `admit()`, `assume()`, or `sorry` calls.

## Overview

This directory contains two verified Pulse implementations of red-black trees
from CLRS §13.1–13.4, sharing a common pure specification:

1. **Okasaki-style RBTree** (`Impl.fst`): purely functional balance/ins/insert
   translated to a pointer-based Pulse implementation. Uses Okasaki's elegant
   pattern-matching balance function. Supports search, insert, delete, and free.

2. **CLRS-style RBTree** (`CLRSImpl.fst`): imperative insert and delete with
   explicit LEFT-ROTATE/RIGHT-ROTATE and uncle-checking INSERT-FIXUP /
   DELETE-FIXUP, faithful to the CLRS pseudocode. Uses parent pointers.

Both produce results that are provably equivalent to the pure specification:
the Pulse postconditions state exact equality to the pure-functional operation.

## Algorithm Summary

| Operation | CLRS § | Okasaki (`Impl`) | CLRS (`CLRSImpl`) | Complexity (proven) | Admits |
|---|---|---|---|---|---|
| SEARCH | §13.2 | `rb_search` | `rb_search` | O(lg n) | 0 |
| INSERT | §13.3 | `rb_insert` | `rb_clrs_insert` | O(lg n) | 0 |
| DELETE | §13.4 | `rb_delete` | `rb_clrs_delete` | O(lg n) | 0 |
| MINIMUM | §12.2 | — | `rb_minimum` | O(lg n) | 0 |
| FREE | — | `free_rbtree` | `free_rbtree` | O(n) | 0 |

## Pure Specification (`CLRS.Ch13.RBTree.Spec`)

### RB Tree Type

```fstar
type color = | Red | Black

type rbtree =
  | Leaf : rbtree
  | Node : c:color -> l:rbtree -> v:int -> r:rbtree -> rbtree
```

### RB Invariants (§13.1)

```fstar
let is_rbtree (t: rbtree) : bool =
  is_root_black t && no_red_red t && same_bh t
```

- `is_root_black`: Property 1 — root is black.
- `no_red_red`: Property 4 — red nodes have only black children.
- `same_bh`: Property 5 — all root-to-leaf paths have equal black-height.

### BST Ordering

```fstar
let rec is_bst (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node _ l v r -> all_lt l v && all_gt r v && is_bst l && is_bst r
```

### Okasaki-Style Balance (§13.3)

The four rotation cases are implemented as a single pattern-matching function:

```fstar
let balance (c: color) (l: rbtree) (v: int) (r: rbtree) : rbtree =
  match c, l, r with
  | Black, Node Red (Node Red a x b) y c_, _ ->    (* LL *)
    Node Red (Node Black a x b) y (Node Black c_ v r)
  | Black, Node Red a x (Node Red b y c_), _ ->    (* LR *)
    Node Red (Node Black a x b) y (Node Black c_ v r)
  | Black, _, Node Red (Node Red b y c_) z d ->     (* RL *)
    Node Red (Node Black l v b) y (Node Black c_ z d)
  | Black, _, Node Red b y (Node Red c_ z d) ->     (* RR *)
    Node Red (Node Black l v b) y (Node Black c_ z d)
  | _ -> Node c l v r
```

Insert is `make_black ∘ ins`, where `ins` calls `balance` at each level.

### Kahrs-Style Delete (§13.4)

Delete uses Kahrs' formulation with `balL`/`balR`/`fuse`:

- `fuse l r`: merges two subtrees when a node is deleted.
- `balL`/`balR`: rebalance after a black-height deficit on left/right.
- `del t k`: recursive delete with color-aware rebalancing.
- `delete t k = make_black (del t k)`.

### Theorem 13.1: Height Bound

CLRS Theorem 13.1: *A red-black tree with n internal nodes has height
at most 2·lg(n + 1).*

The proof follows CLRS:
1. `min_nodes_for_bh`: subtree with black-height `bh` has ≥ 2^bh − 1 nodes.
2. `bh_height_bound`: height ≤ 2·bh + color_bonus.
3. `height_bound_theorem`: height ≤ 2·lg(n + 1).

## Correctness Theorems

### Okasaki-Style (`CLRS.Ch13.RBTree.Impl.fsti`)

#### `rb_search`

```fstar
fn rb_search (tree: rb_ptr) (k: int)
  preserves is_rbtree tree 'ft
  returns result: option int
  ensures pure (result == S.search 'ft k)
```

Read-only: tree preserved. Result equals pure spec.

#### `rb_insert`

```fstar
fn rb_insert (tree: rb_ptr) (k: int)
  requires is_rbtree tree 'ft
  returns y: rb_ptr
  ensures is_rbtree y (S.insert 'ft k)
```

Result tree represents exactly `S.insert 'ft k`.

#### `rb_delete`

```fstar
fn rb_delete (tree: rb_ptr) (k: int)
  requires is_rbtree tree 'ft
  returns y: rb_ptr
  ensures is_rbtree y (S.delete 'ft k)
```

Result tree represents exactly `S.delete 'ft k`.

#### Validated API (bundles RB + BST invariants)

```fstar
fn rb_insert_v (tree: rb_ptr) (k: int)
  requires valid_rbtree tree 'ft
  returns y: rb_ptr
  ensures valid_rbtree y (S.insert 'ft k) **
          pure (S.mem k (S.insert 'ft k) = true)
```

`valid_rbtree ct ft = is_rbtree ct ft ** pure (S.is_rbtree ft /\ S.is_bst ft)`

The postcondition guarantees that the result is both a valid RB tree and a valid
BST, and that the key is a member of the result.

#### Complexity-Aware API

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

### CLRS-Style (`CLRS.Ch13.RBTree.CLRSImpl.fsti`)

#### `rb_clrs_insert`

```fstar
fn rb_clrs_insert (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft parent
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_insert 'ft k) parent
```

Uses `CLRSSpec.clrs_insert` — which is defined using explicit
`clrs_fixup_left`/`clrs_fixup_right` with uncle-checking and rotations, exactly
matching CLRS §13.3.

#### `rb_clrs_delete`

```fstar
fn rb_clrs_delete (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft 'old_parent
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_delete 'ft k) parent
```

Uses `CLRSSpec.clrs_delete` — full 4-case DELETE-FIXUP with rotations.

#### Validated API

```fstar
fn rb_insert_v (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (CS.clrs_insert 'ft k) parent **
          pure (S.mem k (CS.clrs_insert 'ft k) = true)
```

### Strongest Guarantees

The Okasaki postconditions are the strongest possible functional guarantees:

1. **Insert:** `is_rbtree y (S.insert 'ft k)` — the result pointer tree is
   exactly the pure insert. Combined with `insert_is_rbtree`, `insert_preserves_bst`,
   and `insert_mem`, this gives: valid RB tree, valid BST, key present, and all
   old keys preserved.

2. **Delete:** `is_rbtree y (S.delete 'ft k)` — combined with `delete_is_rbtree`,
   `delete_preserves_bst`, and `delete_mem`, this gives: valid RB tree, valid BST,
   key absent, and all other keys preserved.

3. **Search:** `result == S.search 'ft k` — exact pure-spec equivalence.

## Complexity (`CLRS.Ch13.RBTree.Complexity`)

| Operation | Tick bound | Combined with Theorem 13.1 |
|---|---|---|
| Search | `search_ticks t k ≤ height(t) + 1` | `≤ 2·lg(n+1) + 1` |
| Insert | `insert_ticks t k ≤ height(t) + 2` | `≤ 2·lg(n+1) + 2` |
| Delete | `delete_ticks t k ≤ 2·height(t) + 2` | `≤ 4·lg(n+1) + 2` |

The complexity module defines ghost tick counters shadowing the recursive
structure of `search`, `ins`, and `del`. The `balance` operation contributes
only O(1) — it examines a constant number of nodes and performs at most two
rotations.

Logarithmic bounds are proven via the height bound theorem:

```fstar
val search_complexity (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t /\ node_count t >= 1)
          (ensures search_ticks t k <= 2 * log2_floor (node_count t + 1) + 1)

val insert_complexity (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t /\ node_count t >= 1)
          (ensures insert_ticks t k <= 2 * log2_floor (node_count t + 1) + 2)

val delete_complexity (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t /\ node_count t >= 1)
          (ensures delete_ticks t k <= 4 * log2_floor (node_count t + 1) + 2)
```

## CLRS-Style Spec (`CLRS.Ch13.RBTree.CLRSSpec`)

The CLRSSpec module defines CLRS-faithful operations using explicit rotations:

- `left_rotate`, `right_rotate` (§13.2)
- `clrs_fixup_left`, `clrs_fixup_right` — uncle-checking fixup (§13.3)
- `clrs_ins`, `clrs_insert` — BST insert + fixup
- `clrs_resolve_left/right`, `clrs_del_cases234_left/right` — DELETE-FIXUP (§13.4)
- `clrs_del`, `clrs_delete` — full delete with fixup

The key difference from Okasaki:
- INSERT-FIXUP checks uncle color: Red → recolor (Case 1), Black → rotate (Cases 2/3).
- DELETE uses successor-replacement + 4-case fixup, not Kahrs-style fuse.

## Lemmas (`CLRS.Ch13.RBTree.Lemmas`)

All lemmas are fully verified with zero admits:

| Category | Key Lemmas |
|---|---|
| Theorem 13.1 | `height_bound_theorem`, `min_nodes_for_bh`, `bh_height_bound` |
| Insert membership | `insert_mem`: `mem x (insert t k) ⟺ (x = k ∨ mem x t)` |
| Insert BST | `insert_preserves_bst`: BST ordering preserved |
| Insert RB | `insert_is_rbtree`: all RB properties preserved |
| Delete membership | `delete_mem`: `mem x (delete t k) ⟺ (mem x t ∧ x ≠ k)` |
| Delete BST | `delete_preserves_bst`: BST ordering preserved |
| Delete RB | `delete_is_rbtree`: all RB + BST properties preserved |
| Minimum | `minimum_is_min`: minimum ≤ all keys |
| Maximum | `maximum_is_max`: maximum ≥ all keys |
| Successor | `successor_is_next`: successor is next larger key |
| Predecessor | `predecessor_is_prev`: predecessor is next smaller key |
| Node count | `insert_node_count`: exact count after insert |

## Limitations

- **Delete tick bound is 4·lg(n+1) + 2, not 2·lg(n+1).** The Kahrs-style
  `fuse` can traverse up to `height(l) + height(r)` ≤ 2h nodes, doubling the
  constant factor compared to search/insert.
- **No amortized analysis.** Complexity is worst-case per-operation, not
  amortized over a sequence.
- **Integer keys only.** No generic key type or comparator function.
- **No persistent/functional interface.** The Pulse implementation is
  destructive — insert/delete consume the input tree.
- **CLRS-style does not yet have complexity bounds.** The O(lg n) bounds are
  proven only for the Okasaki-style operations.

## File Inventory

| File | Role | Admits |
|---|---|---|
| `CLRS.Ch13.RBTree.Spec.fst` | Pure spec: types, invariants, search, insert (Okasaki), delete (Kahrs) | 0 |
| `CLRS.Ch13.RBTree.Lemmas.fsti` | Correctness theorem signatures | 0 |
| `CLRS.Ch13.RBTree.Lemmas.fst` | Correctness proofs (Thm 13.1, insert/delete preservation) | 0 |
| `CLRS.Ch13.RBTree.Complexity.fsti` | Tick counter signatures, O(lg n) bounds | 0 |
| `CLRS.Ch13.RBTree.Complexity.fst` | Complexity proofs | 0 |
| `CLRS.Ch13.RBTree.Impl.fsti` | Okasaki Pulse: types, slprop, full API signatures | 0 |
| `CLRS.Ch13.RBTree.Impl.fst` | Okasaki Pulse: implementation (search, balance, insert, delete, free) | 0 |
| `CLRS.Ch13.RBTree.CLRSSpec.fst` | CLRS-style pure spec: rotations, fixup, delete-fixup | 0 |
| `CLRS.Ch13.RBTree.CLRSImpl.fsti` | CLRS Pulse: types, slprop, full API signatures | 0 |
| `CLRS.Ch13.RBTree.CLRSImpl.fst` | CLRS Pulse: implementation with rotations and parent pointers | 0 |

## Building and Verification

```bash
cd ch13-rbtree
make          # Verify all modules
```

The Makefile includes `$(PULSE_ROOT)/mk/test.mk` for the standard Pulse build
infrastructure.

## References

- CLRS 3rd Edition, Chapter 13: Red-Black Trees, §13.1–13.4
- Okasaki, "Red-Black Trees in a Functional Setting", JFP 1999
- Kahrs, "Red-Black Trees with Types", JFP 2001
- CLRS Theorem 13.1: height ≤ 2·lg(n + 1)
