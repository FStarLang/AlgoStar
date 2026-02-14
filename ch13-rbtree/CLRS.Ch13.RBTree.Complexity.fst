(**
 * CLRS Chapter 13: Red-Black Trees — Complexity Analysis
 *
 * This module proves that search and insert operations on red-black trees
 * are O(log n), where n is the number of nodes in the tree.
 *
 * Key results:
 *   1. RB tree height h ≤ 2·lg(n+1) (CLRS Lemma 13.1, proven in Spec module)
 *   2. Search follows a path from root to leaf, taking O(h) steps = O(log n)
 *   3. Insert follows a path from root to leaf, taking O(h) steps = O(log n)
 *
 * We define "tick" functions that count the number of recursive calls or
 * loop iterations, and prove they are bounded by the height.
 *
 * NO admits. NO assumes.
 *)
module CLRS.Ch13.RBTree.Complexity

open FStar.Mul
open CLRS.Ch13.RBTree.Spec

(*** Tick Counters ***)

// Search tick count: number of recursive calls (path length from root)
let rec search_ticks (t: rbtree) (k: int) : nat =
  match t with
  | Leaf -> 1  // Base case: one tick
  | Node _ l v r ->
    if k < v then 1 + search_ticks l k
    else if k > v then 1 + search_ticks r k
    else 1  // Found: one tick

// Insert tick count: ins follows a path, then fixup is O(1) rotations
// We count the recursive calls in ins (path traversal)
let rec ins_ticks (t: rbtree) (k: int) : nat =
  match t with
  | Leaf -> 1  // Base case: create new node
  | Node _ l v r ->
    if k < v then 1 + ins_ticks l k
    else if k > v then 1 + ins_ticks r k
    else 1  // Duplicate: no recursion

// Insert tick count includes ins traversal + O(1) for make_black
let insert_ticks (t: rbtree) (k: int) : nat =
  ins_ticks t k + 1

(*** Bounds on Tick Counts ***)

// Search ticks are bounded by height + 1
let rec search_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures search_ticks t k <= height t + 1)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r ->
      if k < v then search_ticks_bounded l k
      else if k > v then search_ticks_bounded r k

// ins ticks are bounded by height + 1
let rec ins_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures ins_ticks t k <= height t + 1)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r ->
      if k < v then ins_ticks_bounded l k
      else if k > v then ins_ticks_bounded r k

// insert ticks are bounded by height + 2
let insert_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures insert_ticks t k <= height t + 2)
  = ins_ticks_bounded t k

(*** Logarithmic Bounds ***)

// For a valid RB tree with n ≥ 1 nodes, search is O(log n)
let search_complexity (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t /\ node_count t >= 1)
    (ensures search_ticks t k <= 2 * log2_floor (node_count t + 1) + 1)
  = search_ticks_bounded t k;
    height_bound_theorem t

// For a valid RB tree with n ≥ 1 nodes, insert is O(log n)
let insert_complexity (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t /\ node_count t >= 1)
    (ensures insert_ticks t k <= 2 * log2_floor (node_count t + 1) + 2)
  = insert_ticks_bounded t k;
    height_bound_theorem t

(*** Empty Tree Special Case ***)

// For empty tree (n=0), operations are O(1)
let search_empty (k: int)
  : Lemma (ensures search_ticks Leaf k = 1)
  = ()

let insert_empty (k: int)
  : Lemma (ensures insert_ticks Leaf k = 2)
  = ()

(*** Asymptotic Complexity Statements ***)

// Search is O(log n): there exists a constant c such that for all valid RB trees,
// search_ticks ≤ c * log(n+1) + c
//
// We can take c = 2 (from the factor 2 in height bound) plus the additive constant.

let search_big_o (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t)
    (ensures (node_count t >= 1 ==>
              search_ticks t k <= 2 * log2_floor (node_count t + 1) + 1) /\
             (node_count t = 0 ==>
              search_ticks t k = 1))
  = if node_count t >= 1 then
      search_complexity t k
    else
      search_empty k

let insert_big_o (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t)
    (ensures (node_count t >= 1 ==>
              insert_ticks t k <= 2 * log2_floor (node_count t + 1) + 2) /\
             (node_count t = 0 ==>
              insert_ticks t k = 2))
  = if node_count t >= 1 then
      insert_complexity t k
    else
      insert_empty k

(*** Additional Complexity Facts ***)

// The height bound is tight: height is Θ(log n)
// Lower bound: any binary tree with n nodes has height ≥ log2_floor(n)
// (This is a standard result; we already have the upper bound from Spec)

// Balance operations in insert are O(1): they only examine a constant number
// of nodes and perform at most 2 rotations (CLRS property).
// This is reflected in our tick counter by not recursing in balance.

(*** Concrete Examples ***)

// Example: A tree with 15 nodes (complete binary tree) has height ≤ 7
// log2_floor(16) = 4, so 2*4 = 8, and our bound holds.

#push-options "--z3rlimit 30 --fuel 6"
let log2_floor_16 ()
  : Lemma (log2_floor 16 = 4)
  = assert_norm (log2_floor 16 = 4)

let example_bound_15_nodes (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t /\ node_count t = 15)
    (ensures height t <= 8 /\
             search_ticks t k <= 9 /\
             insert_ticks t k <= 10)
  = log2_floor_16 ();
    height_bound_theorem t;
    search_ticks_bounded t k;
    insert_ticks_bounded t k
#pop-options

// Example: A tree with 1023 nodes has height ≤ 20
// log2_floor(1024) = 10, so 2*10 = 20.

#push-options "--z3rlimit 30 --fuel 12"
let log2_floor_1024 ()
  : Lemma (log2_floor 1024 = 10)
  = assert_norm (log2_floor 1024 = 10)

let example_bound_1023_nodes (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t /\ node_count t = 1023)
    (ensures height t <= 20 /\
             search_ticks t k <= 21 /\
             insert_ticks t k <= 22)
  = log2_floor_1024 ();
    height_bound_theorem t;
    search_ticks_bounded t k;
    insert_ticks_bounded t k
#pop-options

(*** Summary ***)

// THEOREM: For a red-black tree with n nodes:
//   - Height h ≤ 2·lg(n+1)  [CLRS Lemma 13.1, proven in Spec module]
//   - Search takes ≤ h+1 steps
//   - Insert takes ≤ h+2 steps
//   - Both operations are O(log n)
//
// This module provides executable complexity bounds via ghost tick counters,
// proving that the worst-case time complexity of search and insert is
// logarithmic in the number of nodes.
