(**
 * CLRS Chapter 13: Red-Black Trees — Complexity Analysis for CLRS-Style Operations
 *
 * Proves complexity bounds for the rotation-based CLRS insert and delete
 * operations (§13.3–13.4). Defines tick counters that mirror the recursion
 * structure of clrs_ins / clrs_del in CLRSSpec.
 *
 * Key results:
 *   - clrs_ins_ticks ≤ h+1 (path traversal, fixup is O(1))
 *   - clrs_del_ticks ≤ 2h+1 (path + successor search + successor delete)
 *   - Combined with Theorem 13.1: all O(log n)
 *
 * NO admits. NO assumes.
 *)
module CLRS.Ch13.RBTree.CLRSComplexity

open FStar.Mul
open CLRS.Ch13.RBTree.Spec
open CLRS.Ch13.RBTree.Lemmas

(*** Tick Counters ***)

// CLRS insert tick count: number of recursive calls in clrs_ins
// clrs_fixup_left/right are non-recursive (O(1)), not counted.
let rec clrs_ins_ticks (t: rbtree) (k: int) : nat =
  match t with
  | Leaf -> 1
  | Node _ l v r ->
    if k < v then 1 + clrs_ins_ticks l k
    else if k > v then 1 + clrs_ins_ticks r k
    else 1

// CLRS insert tick count includes clrs_ins traversal + O(1) for make_black
let clrs_insert_ticks (t: rbtree) (k: int) : nat =
  clrs_ins_ticks t k + 1

// Minimum tick count: walks the left spine
let rec minimum_ticks (t: rbtree{Node? t}) : nat =
  match t with
  | Node _ Leaf _ _ -> 1
  | Node _ l _ _ -> 1 + minimum_ticks l

// CLRS delete tick count:
// - Path traversal to the deletion point
// - At two-child nodes: minimum search + recursive delete of successor
// - clrs_resolve_left/right and clrs_del_cases234 are O(1), not counted
let rec clrs_del_ticks (t: rbtree) (k: int) : Tot nat (decreases t) =
  match t with
  | Leaf -> 1
  | Node _ l v r ->
    if k < v then 1 + clrs_del_ticks l k
    else if k > v then 1 + clrs_del_ticks r k
    else
      match l, r with
      | Leaf, Leaf -> 1
      | Leaf, _ -> 1
      | _, Leaf -> 1
      | _, _ -> 1 + minimum_ticks r + clrs_del_ticks r (minimum r)

// CLRS delete tick count = clrs_del_ticks + 1 (for make_black)
let clrs_delete_ticks (t: rbtree) (k: int) : nat =
  clrs_del_ticks t k + 1

(*** Height-Based Bounds ***)

// clrs_ins_ticks bounded by height + 1 (same structure as Okasaki ins_ticks)
let rec clrs_ins_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures clrs_ins_ticks t k <= height t + 1)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r ->
      if k < v then clrs_ins_ticks_bounded l k
      else if k > v then clrs_ins_ticks_bounded r k

// clrs_insert_ticks bounded by height + 2
let clrs_insert_ticks_bounded (t: rbtree) (k: int)
  : Lemma (ensures clrs_insert_ticks t k <= height t + 2)
  = clrs_ins_ticks_bounded t k

// minimum_ticks bounded by height (walks left spine, depth ≤ height)
let rec minimum_ticks_bounded (t: rbtree{Node? t})
  : Lemma (ensures minimum_ticks t <= height t)
    (decreases t)
  = match t with
    | Node _ Leaf _ _ -> ()
    | Node _ l _ _ -> minimum_ticks_bounded l

// Helper: clrs_del of the minimum element follows the left spine only.
// Since minimum(t) is the leftmost key (BST property), clrs_del always
// goes left, and at the minimum node l=Leaf so no further recursion.
// Cost: at most height(t) + 1
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec clrs_del_minimum_bounded (t: rbtree)
  : Lemma (requires is_bst t /\ Node? t)
          (ensures clrs_del_ticks t (minimum t) <= height t + 1)
    (decreases t)
  = match t with
    | Node _ Leaf v r ->
      // minimum t = v, clrs_del_ticks matches k=v with l=Leaf, cost 1
      // height t >= 1, so height t + 1 >= 2 >= 1
      ()
    | Node _ l v r ->
      // l is not Leaf (Leaf case already handled above)
      // minimum t = minimum l, and minimum l < v (by BST: all_lt l v)
      minimum_mem l;
      all_lt_mem l v (minimum l);
      // So clrs_del goes left: clrs_del_ticks t (minimum t) = 1 + clrs_del_ticks l (minimum l)
      clrs_del_minimum_bounded l
      // IH: clrs_del_ticks l (minimum l) <= height l + 1
      // Total: 1 + height l + 1 = height l + 2 <= max(height l, height r) + 2 = height t + 1
#pop-options

// clrs_del_ticks bounded by 2 * height + 1
// Proof: path traversal costs at most height(t), and the two-child
// case adds minimum_ticks + clrs_del of successor, both bounded by height.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec clrs_del_ticks_bounded (t: rbtree) (k: int)
  : Lemma (requires is_bst t)
          (ensures clrs_del_ticks t k <= 2 * height t + 1)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r ->
      if k < v then
        clrs_del_ticks_bounded l k
      else if k > v then
        clrs_del_ticks_bounded r k
      else
        match l, r with
        | Leaf, Leaf -> ()
        | Leaf, _ -> ()
        | _, Leaf -> ()
        | _, _ ->
          // Two-child case: cost = 1 + minimum_ticks r + clrs_del_ticks r (minimum r)
          minimum_ticks_bounded r;
          clrs_del_minimum_bounded r
          // minimum_ticks r <= height r
          // clrs_del_ticks r (minimum r) <= height r + 1
          // Total: 1 + height r + height r + 1 = 2*height r + 2
          // <= 2*(height t - 1) + 2 = 2*height t <= 2*height t + 1
#pop-options

// clrs_delete_ticks bounded by 2 * height + 2
let clrs_delete_ticks_bounded (t: rbtree) (k: int)
  : Lemma (requires is_bst t)
          (ensures clrs_delete_ticks t k <= 2 * height t + 2)
  = clrs_del_ticks_bounded t k

(*** Logarithmic Bounds ***)

// CLRS insert is O(log n)
let clrs_insert_complexity (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t /\ node_count t >= 1)
    (ensures clrs_insert_ticks t k <= 2 * log2_floor (node_count t + 1) + 2)
  = clrs_insert_ticks_bounded t k;
    height_bound_theorem t

// CLRS delete is O(log n)
let clrs_delete_complexity (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t /\ is_bst t /\ node_count t >= 1)
    (ensures clrs_delete_ticks t k <= 4 * log2_floor (node_count t + 1) + 2)
  = clrs_delete_ticks_bounded t k;
    height_bound_theorem t

(*** Empty Tree Special Cases ***)

let clrs_insert_empty (k: int)
  : Lemma (ensures clrs_insert_ticks Leaf k = 2)
  = ()

let clrs_delete_empty (k: int)
  : Lemma (ensures clrs_delete_ticks Leaf k = 2)
  = ()

(*** Big-O Statements ***)

let clrs_insert_big_o (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t)
    (ensures (node_count t >= 1 ==>
              clrs_insert_ticks t k <= 2 * log2_floor (node_count t + 1) + 2) /\
             (node_count t = 0 ==> clrs_insert_ticks t k = 2))
  = if node_count t >= 1 then
      clrs_insert_complexity t k
    else
      clrs_insert_empty k

let clrs_delete_big_o (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t /\ is_bst t)
    (ensures (node_count t >= 1 ==>
              clrs_delete_ticks t k <= 4 * log2_floor (node_count t + 1) + 2) /\
             (node_count t = 0 ==> clrs_delete_ticks t k = 2))
  = if node_count t >= 1 then
      clrs_delete_complexity t k
