(**
 * CLRS Chapter 13: Red-Black Trees — Pure Functional Specification
 *
 * Covers CLRS §13.1–13.4 (properties, rotations, insertion, deletion).
 *
 * Defines:
 *   - Inductive rbtree type with Red/Black colors
 *   - BST ordering predicate (all_lt / all_gt bounds)
 *   - RB invariants: no_red_red, same_black_height, root_black
 *   - Functional search, insert with Okasaki-style balance/fixup
 *   - Functional delete with Kahrs-style balL/balR/fuse
 *   - Minimum/maximum and successor/predecessor operations
 *   - Balance case classifier (for Pulse implementation)
 *
 * The balancing approach follows Okasaki, "Red-Black Trees in a
 * Functional Setting", Journal of Functional Programming, 1999.
 *
 * Correctness lemmas (Theorem 13.1, preservation proofs, etc.) are
 * in the companion module CLRS.Ch13.RBTree.Lemmas.
 *)
module CLRS.Ch13.RBTree.Spec

open FStar.Mul

(*** Basic Definitions ***)

let max (a b: nat) : nat = if a >= b then a else b

type color = | Red | Black

type rbtree =
  | Leaf : rbtree
  | Node : c:color -> l:rbtree -> v:int -> r:rbtree -> rbtree

(*** Tree Metrics ***)

let rec height (t: rbtree) : nat =
  match t with
  | Leaf -> 0
  | Node _ l _ r -> 1 + max (height l) (height r)

let rec node_count (t: rbtree) : nat =
  match t with
  | Leaf -> 0
  | Node _ l _ r -> 1 + node_count l + node_count r

// Black-height: number of black nodes on path to leaf, not counting self.
// Leaf (NIL) has bh 0.
let rec bh (t: rbtree) : nat =
  match t with
  | Leaf -> 0
  | Node c l _ _ ->
    if c = Black then 1 + bh l else bh l

(*** RB Properties ***)

let is_root_black (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node c _ _ _ -> c = Black

// No consecutive red nodes
let rec no_red_red (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node c l _ r ->
    (if c = Red then
       (match l with Leaf -> true | Node cl _ _ _ -> cl = Black) &&
       (match r with Leaf -> true | Node cr _ _ _ -> cr = Black)
     else true) &&
    no_red_red l && no_red_red r

// All root-to-leaf paths have same number of black nodes
let rec same_bh (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node _ l _ r -> bh l = bh r && same_bh l && same_bh r

let is_rbtree (t: rbtree) : bool =
  is_root_black t && no_red_red t && same_bh t

(*** Membership and BST ***)

let rec mem (x: int) (t: rbtree) : bool =
  match t with
  | Leaf -> false
  | Node _ l v r -> x = v || mem x l || mem x r

// All keys in tree < bound
let rec all_lt (t: rbtree) (bound: int) : bool =
  match t with
  | Leaf -> true
  | Node _ l v r -> v < bound && all_lt l bound && all_lt r bound

// All keys in tree > bound
let rec all_gt (t: rbtree) (bound: int) : bool =
  match t with
  | Leaf -> true
  | Node _ l v r -> v > bound && all_gt l bound && all_gt r bound

// BST ordering: all keys in left < v, all keys in right > v
let rec is_bst (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node _ l v r ->
    all_lt l v &&
    all_gt r v &&
    is_bst l && is_bst r

(*** Search ***)

let rec search (t: rbtree) (k: int) : option int =
  match t with
  | Leaf -> None
  | Node _ l v r ->
    if k < v then search l k
    else if k > v then search r k
    else Some v

(*** Okasaki-style Balance (Insert Fixup) ***)

// The four rotation cases from Okasaki
let balance (c: color) (l: rbtree) (v: int) (r: rbtree) : rbtree =
  match c, l, r with
  // Left-left: red left child has red left grandchild
  | Black, Node Red (Node Red a x b) y c_, _ ->
    Node Red (Node Black a x b) y (Node Black c_ v r)
  // Left-right: red left child has red right grandchild
  | Black, Node Red a x (Node Red b y c_), _ ->
    Node Red (Node Black a x b) y (Node Black c_ v r)
  // Right-left: red right child has red left grandchild
  | Black, _, Node Red (Node Red b y c_) z d ->
    Node Red (Node Black l v b) y (Node Black c_ z d)
  // Right-right: red right child has red right grandchild
  | Black, _, Node Red b y (Node Red c_ z d) ->
    Node Red (Node Black l v b) y (Node Black c_ z d)
  // No fixup needed
  | _ -> Node c l v r

// Insert helper (may produce red root)
let rec ins (t: rbtree) (k: int) : rbtree =
  match t with
  | Leaf -> Node Red Leaf k Leaf
  | Node c l v r ->
    if k < v then balance c (ins l k) v r
    else if k > v then balance c l v (ins r k)
    else Node c l v r // duplicate

let make_black (t: rbtree) : rbtree =
  match t with
  | Leaf -> Leaf
  | Node _ l v r -> Node Black l v r

let insert (t: rbtree) (k: int) : rbtree =
  make_black (ins t k)

(*** Balance Case Classifier ***)

// Used by the Pulse implementation to determine which rotation to apply
// without deep pattern matching on pointers.

type balance_case =
  | BC_LL   // Left-left:   Node Red (Node Red a x b) y c_, _, v, r
  | BC_LR   // Left-right:  Node Red a x (Node Red b y c_), _, v, r
  | BC_RL   // Right-left:  _, Node Red (Node Red b y c_) z d
  | BC_RR   // Right-right: _, Node Red b y (Node Red c_ z d)
  | BC_None // No fixup needed

let classify_balance (c: color) (l: rbtree) (r: rbtree) : balance_case =
  match c, l, r with
  | Black, Node Red (Node Red _ _ _) _ _, _ -> BC_LL
  | Black, Node Red _ _ (Node Red _ _ _), _ -> BC_LR
  | Black, _, Node Red (Node Red _ _ _) _ _ -> BC_RL
  | Black, _, Node Red _ _ (Node Red _ _ _) -> BC_RR
  | _ -> BC_None

(*** Helper Predicates ***)

// For any valid subtree, height <= 2*bh + (if Red then 1 else 0)
let color_bonus (t: rbtree) : nat =
  match t with
  | Leaf -> 0
  | Node c _ _ _ -> if c = Red then 1 else 0

// log2 floor for positive integers
let rec log2_floor (n: pos) : Tot nat (decreases n) =
  if n = 1 then 0
  else 1 + log2_floor (n / 2)

// ins produces a tree where no_red_red holds everywhere except possibly at the root
let almost_no_red_red (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node _ l _ r -> no_red_red l && no_red_red r

(*** Minimum / Maximum ***)

// Find the minimum key in a non-empty BST
let rec minimum (t: rbtree{Node? t}) : int =
  match t with
  | Node _ Leaf v _ -> v
  | Node _ l _ _ -> minimum l

// Find the maximum key in a non-empty BST
let rec maximum (t: rbtree{Node? t}) : int =
  match t with
  | Node _ _ v Leaf -> v
  | Node _ _ _ r -> maximum r

(*** Successor / Predecessor — CLRS §12.2 ***)

// Successor: smallest key strictly greater than k.
// Searches from root (no parent pointers in the pure spec).
let rec successor (t: rbtree) (k: int) : option int =
  match t with
  | Leaf -> None
  | Node _ l v r ->
    if k < v then
      (match successor l k with
       | Some s -> Some s
       | None -> Some v)
    else
      successor r k

// Predecessor: largest key strictly less than k.
let rec predecessor (t: rbtree) (k: int) : option int =
  match t with
  | Leaf -> None
  | Node _ l v r ->
    if k > v then
      (match predecessor r k with
       | Some p -> Some p
       | None -> Some v)
    else
      predecessor l k

(*** Delete — Kahrs-style functional deletion ***)

// Recolor a black node to red (used in delete rebalancing).
let redden (t: rbtree) : rbtree =
  match t with
  | Node Black l v r -> Node Red l v r
  | _ -> t

// Rebalance after deletion from the left subtree caused a black-height deficit.
let balL (l: rbtree) (v: int) (r: rbtree) : rbtree =
  match l, r with
  | Node Red a x b, _ ->
    Node Red (Node Black a x b) v r
  | _, Node Black b y c ->
    balance Black l v (Node Red b y c)
  | _, Node Red (Node Black b y c) z d ->
    Node Red (Node Black l v b) y (balance Black c z (redden d))
  | _ -> Node Black l v r

// Rebalance after deletion from the right subtree caused a black-height deficit.
let balR (l: rbtree) (v: int) (r: rbtree) : rbtree =
  match l, r with
  | _, Node Red b y c ->
    Node Red l v (Node Black b y c)
  | Node Black a x b, _ ->
    balance Black (Node Red a x b) v r
  | Node Red a x (Node Black b y c), _ ->
    Node Red (balance Black (redden a) x b) y (Node Black c v r)
  | _ -> Node Black l v r

// Fuse two subtrees: merge the children of a deleted node.
let rec fuse (l r: rbtree) : Tot rbtree (decreases (node_count l + node_count r)) =
  match l, r with
  | Leaf, _ -> r
  | _, Leaf -> l
  | Node Red a x b, Node Red c y d ->
    let s = fuse b c in
    (match s with
     | Node Red b' z c' -> Node Red (Node Red a x b') z (Node Red c' y d)
     | _ -> Node Red a x (Node Red s y d))
  | Node Black a x b, Node Black c y d ->
    let s = fuse b c in
    (match s with
     | Node Red b' z c' -> Node Red (Node Black a x b') z (Node Black c' y d)
     | _ -> balL a x (Node Black s y d))
  | Node Red a x b, _ ->
    Node Red a x (fuse b r)
  | _, Node Red c y d ->
    Node Red (fuse l c) y d

// Delete helper: removes key k from tree t.
// Following Kahrs' formulation: when the target child is Black, use balL/balR
// to rebalance (the child's bh decreases by 1). When the child is not Black
// (Red or Leaf), use Node Red to absorb the parent's black level.
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

// Top-level delete: del + make root black
let delete (t: rbtree) (k: int) : rbtree =
  make_black (del t k)
