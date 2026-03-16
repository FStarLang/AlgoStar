(**
 * CLRS Chapter 13: Red-Black Tree — Rotation-based Spec
 *
 * CLRS-faithful insert and delete using explicit LEFT-ROTATE / RIGHT-ROTATE.
 * Imports the shared rbtree type and predicates from CLRS.Ch13.RBTree.Spec
 * (Okasaki-style spec) and defines new operations:
 *
 *  - left_rotate, right_rotate (§13.2)
 *  - clrs_ins / clrs_insert with INSERT-FIXUP (§13.3)
 *  - clrs_del / clrs_delete with DELETE-FIXUP (§13.4)
 *
 * Key difference from Okasaki:
 *  INSERT-FIXUP checks uncle color:
 *    Uncle Red   → Case 1: recolor only (no rotation)
 *    Uncle Black → Cases 2/3: rotate + recolor
 *
 *  DELETE uses successor-replacement + 4-case fixup with rotations,
 *  not Kahrs-style fuse + balL/balR.
 *
 * All proofs fully verified — no admits.
 *)
module CLRS.Ch13.RBTree.CLRSSpec

open FStar.Mul
open CLRS.Ch13.RBTree.Spec
open CLRS.Ch13.RBTree.Lemmas

(*** §13.2 — Rotation Primitives ***)

let is_red_node (t: rbtree) : bool =
  match t with Node Red _ _ _ -> true | _ -> false

let set_color (c: color) (t: rbtree) : rbtree =
  match t with Node _ l v r -> Node c l v r | Leaf -> Leaf

// LEFT-ROTATE: x's right child y becomes root, x becomes y's left child
//      x              y
//     / \            / \
//    a   y    →     x   d
//       / \        / \
//      b   d      a   b
let left_rotate (t: rbtree) : rbtree =
  match t with
  | Node c a x (Node rc b y d) -> Node rc (Node c a x b) y d
  | _ -> t

// RIGHT-ROTATE: y's left child x becomes root, y becomes x's right child
//      y              x
//     / \            / \
//    x   d    →     a   y
//   / \                / \
//  a   b              b   d
let right_rotate (t: rbtree) : rbtree =
  match t with
  | Node c (Node lc a x b) y d -> Node lc a x (Node c b y d)
  | _ -> t

(*** §13.3 — CLRS INSERT with FIXUP ***)

// After inserting into the LEFT subtree, check for red-red violation
// and apply CLRS INSERT-FIXUP logic.
//
// c: parent color, l: modified left child, v: parent key, r: right child (uncle)
let clrs_fixup_left (c: color) (l: rbtree) (v: int) (r: rbtree) : rbtree =
  match c with
  | Red -> Node Red l v r  // Red parent: can't fix, propagate
  | Black ->
    match l with
    | Node Red (Node Red a x b) y c_child ->
      // LL red-red violation
      if is_red_node r then
        // Case 1: uncle Red → recolor
        Node Red (set_color Black l) v (set_color Black r)
      else
        // Case 3: uncle Black → right-rotate + recolor
        right_rotate (Node Red (set_color Black l) v r)
    | Node Red a y (Node Red b x c_child) ->
      // LR red-red violation
      if is_red_node r then
        // Case 1: uncle Red → recolor
        Node Red (set_color Black l) v (set_color Black r)
      else
        // Case 2→3: left-rotate child, then right-rotate + recolor
        let l' = left_rotate l in
        right_rotate (Node Red (set_color Black l') v r)
    | _ -> Node Black l v r  // No violation

// Symmetric: after inserting into the RIGHT subtree
let clrs_fixup_right (c: color) (l: rbtree) (v: int) (r: rbtree) : rbtree =
  match c with
  | Red -> Node Red l v r
  | Black ->
    match r with
    | Node Red (Node Red b y c_child) z d ->
      // RL red-red violation
      if is_red_node l then
        Node Red (set_color Black l) v (set_color Black r)
      else
        let r' = right_rotate r in
        left_rotate (Node Red l v (set_color Black r'))
    | Node Red b z (Node Red c_child y d) ->
      // RR red-red violation
      if is_red_node l then
        Node Red (set_color Black l) v (set_color Black r)
      else
        left_rotate (Node Red l v (set_color Black r))
    | _ -> Node Black l v r

// CLRS-style recursive insert (may produce Red root)
let rec clrs_ins (t: rbtree) (k: int) : Tot rbtree (decreases t) =
  match t with
  | Leaf -> Node Red Leaf k Leaf
  | Node c l v r ->
    if k < v then clrs_fixup_left c (clrs_ins l k) v r
    else if k > v then clrs_fixup_right c l v (clrs_ins r k)
    else t

// Top-level CLRS insert: ins + make root Black
let clrs_insert (t: rbtree) (k: int) : rbtree =
  make_black (clrs_ins t k)

(*** §13.4 — CLRS DELETE with FIXUP ***)

// DELETE-FIXUP Cases 2-4 for left deficit (sibling w is Black)
// Returns (result_tree, deficit_still_present)
let clrs_del_cases234_left (c: color) (x: rbtree) (v: int) (w: rbtree)
  : rbtree & bool =
  match w with
  | Node Black wl wy wr ->
    let rl_red = is_red_node wl in
    let rr_red = is_red_node wr in
    if not rl_red && not rr_red then
      // Case 2: both sibling children Black → recolor sibling Red
      (Node Black x v (Node Red wl wy wr), c = Black)
    else if rr_red then
      // Case 4: sibling's right child Red → left-rotate at parent
      (Node c (Node Black x v wl) wy (set_color Black wr), false)
    else
      // Case 3: sibling's left child Red, right Black
      (match wl with
       | Node _ wll wlv wlr ->
         (Node c (Node Black x v wll) wlv (Node Black wlr wy wr), false)
       | _ -> (Node c x v w, true))
  | _ -> (Node c x v w, true)

// DELETE-FIXUP for left deficit: x is the subtree with a black-height deficit
// w (= sibling, the right child of the parent) may be Red or Black
let clrs_resolve_left (c: color) (x: rbtree) (v: int) (w: rbtree) : rbtree & bool =
  match w with
  | Node Red wl wy wr ->
    // Case 1: sibling Red → left-rotate at parent (makes sibling Black)
    // Recurse with Red parent and Black sibling wl
    let (inner, deficit) = clrs_del_cases234_left Red x v wl in
    (Node Black inner wy wr, deficit)
  | Node Black _ _ _ ->
    clrs_del_cases234_left c x v w
  | _ ->
    // Sibling is Leaf: shouldn't happen in valid RB tree with deficit
    (Node c x v w, true)

// Symmetric: Cases 2-4 for right deficit (sibling w is Black)
let clrs_del_cases234_right (c: color) (w: rbtree) (v: int) (x: rbtree)
  : rbtree & bool =
  match w with
  | Node Black wl wy wr ->
    let ll_red = is_red_node wl in
    let lr_red = is_red_node wr in
    if not ll_red && not lr_red then
      (Node Black (Node Red wl wy wr) v x, c = Black)
    else if ll_red then
      // Case 4 (symmetric): sibling's left child Red → right-rotate at parent
      (Node c (set_color Black wl) wy (Node Black wr v x), false)
    else
      // Case 3 (symmetric): sibling's right child Red
      (match wr with
       | Node _ wrl wrv wrr ->
         (Node c (Node Black wl wy wrl) wrv (Node Black wrr v x), false)
       | _ -> (Node c w v x, true))
  | _ -> (Node c w v x, true)

// Symmetric: DELETE-FIXUP for right deficit
let clrs_resolve_right (c: color) (w: rbtree) (v: int) (x: rbtree) : rbtree & bool =
  match w with
  | Node Red wl wy wr ->
    let (inner, deficit) = clrs_del_cases234_right Red wr v x in
    (Node Black wl wy inner, deficit)
  | Node Black _ _ _ ->
    clrs_del_cases234_right c w v x
  | _ ->
    (Node c w v x, true)

// CLRS-style recursive delete
// Returns (result_tree, deficit_flag)
// deficit_flag = true iff the subtree's black-height decreased by 1
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
      // Delete this node
      match l, r with
      | Leaf, Leaf -> (Leaf, c = Black)
      | Leaf, Node _ rl rv rr -> (Node Black rl rv rr, false)
      | Node _ ll lv lr, Leaf -> (Node Black ll lv lr, false)
      | _, _ ->
        let sk = minimum r in
        let (r', deficit) = clrs_del r sk in
        if deficit then clrs_resolve_right c l sk r'
        else (Node c l sk r', false)

// Top-level CLRS delete
let clrs_delete (t: rbtree) (k: int) : rbtree =
  make_black (fst (clrs_del t k))

(*** INSERT — Membership Preservation ***)

#push-options "--fuel 3 --ifuel 2 --z3rlimit 20"
let left_rotate_mem (t: rbtree) (k: int)
  : Lemma (mem k (left_rotate t) <==> mem k t) = ()

let right_rotate_mem (t: rbtree) (k: int)
  : Lemma (mem k (right_rotate t) <==> mem k t) = ()

let set_color_mem (c: color) (t: rbtree) (k: int)
  : Lemma (mem k (set_color c t) <==> mem k t) = ()

let clrs_fixup_left_mem (c: color) (l: rbtree) (v: int) (r: rbtree) (k: int)
  : Lemma (mem k (clrs_fixup_left c l v r) <==> (k = v || mem k l || mem k r))
  = ()

let clrs_fixup_right_mem (c: color) (l: rbtree) (v: int) (r: rbtree) (k: int)
  : Lemma (mem k (clrs_fixup_right c l v r) <==> (k = v || mem k l || mem k r))
  = ()
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let rec clrs_ins_mem (t: rbtree) (k: int) (x: int)
  : Lemma
    (requires is_bst t)
    (ensures mem x (clrs_ins t k) <==> (x = k || mem x t))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        clrs_ins_mem l k x;
        clrs_fixup_left_mem c (clrs_ins l k) v r x
      end else if k > v then begin
        clrs_ins_mem r k x;
        clrs_fixup_right_mem c l v (clrs_ins r k) x
      end else ()
#pop-options

let clrs_insert_mem (t: rbtree) (k: int) (x: int)
  : Lemma
    (requires is_bst t)
    (ensures mem x (clrs_insert t k) <==> (x = k || mem x t))
  = clrs_ins_mem t k x

(*** INSERT — BST Preservation ***)

#push-options "--fuel 3 --ifuel 2 --z3rlimit 20"
let left_rotate_all_lt (t: rbtree) (bound: int)
  : Lemma (all_lt (left_rotate t) bound <==> all_lt t bound) = ()

let left_rotate_all_gt (t: rbtree) (bound: int)
  : Lemma (all_gt (left_rotate t) bound <==> all_gt t bound) = ()

let right_rotate_all_lt (t: rbtree) (bound: int)
  : Lemma (all_lt (right_rotate t) bound <==> all_lt t bound) = ()

let right_rotate_all_gt (t: rbtree) (bound: int)
  : Lemma (all_gt (right_rotate t) bound <==> all_gt t bound) = ()

let set_color_all_lt (c: color) (t: rbtree) (bound: int)
  : Lemma (all_lt (set_color c t) bound <==> all_lt t bound) = ()

let set_color_all_gt (c: color) (t: rbtree) (bound: int)
  : Lemma (all_gt (set_color c t) bound <==> all_gt t bound) = ()

let left_rotate_is_bst (t: rbtree)
  : Lemma (requires is_bst t) (ensures is_bst (left_rotate t))
  = match t with
    | Node c a x (Node rc b y d) ->
      all_lt_weaken a x y
    | _ -> ()

let right_rotate_is_bst (t: rbtree)
  : Lemma (requires is_bst t) (ensures is_bst (right_rotate t))
  = match t with
    | Node c (Node lc a x b) y d ->
      all_gt_weaken d y x
    | _ -> ()

let set_color_is_bst (c: color) (t: rbtree)
  : Lemma (requires is_bst t) (ensures is_bst (set_color c t)) = ()

let clrs_fixup_left_all_lt (c: color) (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma
    (requires all_lt l bound /\ v < bound /\ all_lt r bound)
    (ensures all_lt (clrs_fixup_left c l v r) bound)
  = match c with
    | Red -> ()
    | Black ->
      match l with
      | Node Red (Node Red a x b) y c_child ->
        if is_red_node r then ()
        else begin
          set_color_all_lt Black l bound;
          right_rotate_all_lt (Node Red (set_color Black l) v r) bound
        end
      | Node Red a y (Node Red b x c_child) ->
        if is_red_node r then ()
        else begin
          left_rotate_all_lt l bound;
          set_color_all_lt Black (left_rotate l) bound;
          right_rotate_all_lt (Node Red (set_color Black (left_rotate l)) v r) bound
        end
      | _ -> ()

let clrs_fixup_left_all_gt (c: color) (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma
    (requires all_gt l bound /\ v > bound /\ all_gt r bound)
    (ensures all_gt (clrs_fixup_left c l v r) bound)
  = match c with
    | Red -> ()
    | Black ->
      match l with
      | Node Red (Node Red a x b) y c_child ->
        if is_red_node r then ()
        else begin
          set_color_all_gt Black l bound;
          right_rotate_all_gt (Node Red (set_color Black l) v r) bound
        end
      | Node Red a y (Node Red b x c_child) ->
        if is_red_node r then ()
        else begin
          left_rotate_all_gt l bound;
          set_color_all_gt Black (left_rotate l) bound;
          right_rotate_all_gt (Node Red (set_color Black (left_rotate l)) v r) bound
        end
      | _ -> ()

let clrs_fixup_right_all_lt (c: color) (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma
    (requires all_lt l bound /\ v < bound /\ all_lt r bound)
    (ensures all_lt (clrs_fixup_right c l v r) bound)
  = match c with
    | Red -> ()
    | Black ->
      match r with
      | Node Red (Node Red b y c_child) z d ->
        if is_red_node l then ()
        else begin
          right_rotate_all_lt r bound;
          set_color_all_lt Black (right_rotate r) bound;
          left_rotate_all_lt (Node Red l v (set_color Black (right_rotate r))) bound
        end
      | Node Red b z (Node Red c_child y d) ->
        if is_red_node l then ()
        else begin
          set_color_all_lt Black r bound;
          left_rotate_all_lt (Node Red l v (set_color Black r)) bound
        end
      | _ -> ()

let clrs_fixup_right_all_gt (c: color) (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma
    (requires all_gt l bound /\ v > bound /\ all_gt r bound)
    (ensures all_gt (clrs_fixup_right c l v r) bound)
  = match c with
    | Red -> ()
    | Black ->
      match r with
      | Node Red (Node Red b y c_child) z d ->
        if is_red_node l then ()
        else begin
          right_rotate_all_gt r bound;
          set_color_all_gt Black (right_rotate r) bound;
          left_rotate_all_gt (Node Red l v (set_color Black (right_rotate r))) bound
        end
      | Node Red b z (Node Red c_child y d) ->
        if is_red_node l then ()
        else begin
          set_color_all_gt Black r bound;
          left_rotate_all_gt (Node Red l v (set_color Black r)) bound
        end
      | _ -> ()
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 30"
let clrs_fixup_left_is_bst (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires is_bst l /\ is_bst r /\ all_lt l v /\ all_gt r v)
    (ensures is_bst (clrs_fixup_left c l v r))
  = match c with
    | Red -> ()
    | Black ->
      match l with
      | Node Red (Node Red a x b) y c_child ->
        if is_red_node r then ()
        else begin
          set_color_is_bst Black l;
          set_color_all_lt Black l v;
          right_rotate_is_bst (Node Red (set_color Black l) v r)
        end
      | Node Red a y (Node Red b x c_child) ->
        if is_red_node r then ()
        else begin
          left_rotate_is_bst l;
          left_rotate_all_lt l v;
          set_color_is_bst Black (left_rotate l);
          set_color_all_lt Black (left_rotate l) v;
          right_rotate_is_bst (Node Red (set_color Black (left_rotate l)) v r)
        end
      | _ -> ()

let clrs_fixup_right_is_bst (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires is_bst l /\ is_bst r /\ all_lt l v /\ all_gt r v)
    (ensures is_bst (clrs_fixup_right c l v r))
  = match c with
    | Red -> ()
    | Black ->
      match r with
      | Node Red (Node Red b y c_child) z d ->
        if is_red_node l then ()
        else begin
          right_rotate_is_bst r;
          right_rotate_all_gt r v;
          set_color_is_bst Black (right_rotate r);
          set_color_all_gt Black (right_rotate r) v;
          left_rotate_is_bst (Node Red l v (set_color Black (right_rotate r)))
        end
      | Node Red b z (Node Red c_child y d) ->
        if is_red_node l then ()
        else begin
          set_color_is_bst Black r;
          set_color_all_gt Black r v;
          left_rotate_is_bst (Node Red l v (set_color Black r))
        end
      | _ -> ()
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 30"
let rec clrs_ins_all_lt (t: rbtree) (k: int) (bound: int)
  : Lemma
    (requires is_bst t /\ all_lt t bound /\ k < bound)
    (ensures all_lt (clrs_ins t k) bound)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        clrs_ins_all_lt l k bound;
        clrs_fixup_left_all_lt c (clrs_ins l k) v r bound
      end else if k > v then begin
        clrs_ins_all_lt r k bound;
        clrs_fixup_right_all_lt c l v (clrs_ins r k) bound
      end else ()

let rec clrs_ins_all_gt (t: rbtree) (k: int) (bound: int)
  : Lemma
    (requires is_bst t /\ all_gt t bound /\ k > bound)
    (ensures all_gt (clrs_ins t k) bound)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        clrs_ins_all_gt l k bound;
        clrs_fixup_left_all_gt c (clrs_ins l k) v r bound
      end else if k > v then begin
        clrs_ins_all_gt r k bound;
        clrs_fixup_right_all_gt c l v (clrs_ins r k) bound
      end else ()

let rec clrs_ins_preserves_bst (t: rbtree) (k: int)
  : Lemma
    (requires is_bst t)
    (ensures is_bst (clrs_ins t k))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        clrs_ins_preserves_bst l k;
        clrs_ins_all_lt l k v;
        clrs_fixup_left_is_bst c (clrs_ins l k) v r
      end else if k > v then begin
        clrs_ins_preserves_bst r k;
        clrs_ins_all_gt r k v;
        clrs_fixup_right_is_bst c l v (clrs_ins r k)
      end else ()
#pop-options

let clrs_insert_preserves_bst (t: rbtree) (k: int)
  : Lemma (requires is_bst t) (ensures is_bst (clrs_insert t k))
  = clrs_ins_preserves_bst t k

(*** INSERT — RB Property Preservation ***)

// "ins_almost" is stronger than almost_no_red_red:
// If root is Red with a Red child, the OTHER child must not be Red-rooted.
// This is always satisfied by clrs_ins results because only one path is modified.
let ins_almost_no_red_red (t: rbtree) : bool =
  almost_no_red_red t &&
  (match t with
   | Node Red l _ r -> not (is_red_node l && is_red_node r)
   | _ -> true)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 30"
let clrs_fixup_left_same_bh (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l = bh r)
    (ensures same_bh (clrs_fixup_left c l v r))
  = ()

let clrs_fixup_right_same_bh (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l = bh r)
    (ensures same_bh (clrs_fixup_right c l v r))
  = ()

let clrs_fixup_left_bh (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l = bh r)
    (ensures bh (clrs_fixup_left c l v r) = (if c = Black then 1 + bh l else bh l))
  = ()

let clrs_fixup_right_bh (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l = bh r)
    (ensures bh (clrs_fixup_right c l v r) = (if c = Black then 1 + bh l else bh l))
  = ()

// Under Black parent with ins_almost child, fixup restores no_red_red
#push-options "--fuel 5 --ifuel 3 --z3rlimit 30"
let clrs_fixup_left_restores (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires c = Black /\ ins_almost_no_red_red l /\ no_red_red r)
    (ensures no_red_red (clrs_fixup_left c l v r))
  = match l with
    | Node Red (Node Red a x b) y c_child ->
      // LL: ins_almost guarantees c_child not Red-rooted
      if is_red_node r then () // Case 1
      else () // Case 3: rotation safe because c_child not Red
    | Node Red a y (Node Red b x c_child) ->
      // LR: ins_almost guarantees a not Red-rooted
      if is_red_node r then () // Case 1
      else () // Case 2→3: rotation safe because a not Red
    | _ -> ()

let clrs_fixup_right_restores (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires c = Black /\ no_red_red l /\ ins_almost_no_red_red r)
    (ensures no_red_red (clrs_fixup_right c l v r))
  = match r with
    | Node Red (Node Red b y c_child) z d ->
      if is_red_node l then ()
      else ()
    | Node Red b z (Node Red c_child y d) ->
      if is_red_node l then ()
      else ()
    | _ -> ()
#pop-options

// Under Red parent, result is ins_almost (need: unmodified child not Red-rooted)
let clrs_fixup_left_almost (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires no_red_red l /\ no_red_red r /\ not (is_red_node r))
    (ensures almost_no_red_red (clrs_fixup_left Red l v r) /\
             ins_almost_no_red_red (clrs_fixup_left Red l v r))
  = ()

let clrs_fixup_right_almost (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires no_red_red l /\ no_red_red r /\ not (is_red_node l))
    (ensures almost_no_red_red (clrs_fixup_right Red l v r) /\
             ins_almost_no_red_red (clrs_fixup_right Red l v r))
  = ()
#pop-options

// clrs_ins maintains same_bh, preserves bh, and has ins_almost_no_red_red
#push-options "--fuel 3 --ifuel 1 --z3rlimit 30"
let rec clrs_ins_properties (t: rbtree) (k: int)
  : Lemma
    (requires same_bh t /\ no_red_red t)
    (ensures same_bh (clrs_ins t k) /\
             bh (clrs_ins t k) = bh t /\
             ins_almost_no_red_red (clrs_ins t k) /\
             (Node? t /\ Black? (Node?.c t) ==> no_red_red (clrs_ins t k)) /\
             (Leaf? t ==> no_red_red (clrs_ins t k)))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        clrs_ins_properties l k;
        clrs_fixup_left_same_bh c (clrs_ins l k) v r;
        clrs_fixup_left_bh c (clrs_ins l k) v r;
        if c = Black then
          clrs_fixup_left_restores c (clrs_ins l k) v r
        else
          clrs_fixup_left_almost (clrs_ins l k) v r
      end else if k > v then begin
        clrs_ins_properties r k;
        clrs_fixup_right_same_bh c l v (clrs_ins r k);
        clrs_fixup_right_bh c l v (clrs_ins r k);
        if c = Black then
          clrs_fixup_right_restores c l v (clrs_ins r k)
        else
          clrs_fixup_right_almost l v (clrs_ins r k)
      end else ()
#pop-options

let clrs_insert_is_rbtree (t: rbtree) (k: int)
  : Lemma (requires is_rbtree t)
          (ensures is_rbtree (clrs_insert t k))
  = clrs_ins_properties t k

(*** DELETE — Membership Preservation ***)

#push-options "--fuel 3 --ifuel 2 --z3rlimit 20"
let clrs_del_cases234_left_mem (c: color) (x: rbtree) (v: int)
                               (w: rbtree) (k: int)
  : Lemma (mem k (fst (clrs_del_cases234_left c x v w)) <==> (k = v || mem k x || mem k w))
  = ()

let clrs_del_cases234_right_mem (c: color) (w: rbtree)
                                (v: int) (x: rbtree) (k: int)
  : Lemma (mem k (fst (clrs_del_cases234_right c w v x)) <==> (k = v || mem k w || mem k x))
  = ()

let clrs_resolve_left_mem (c: color) (x: rbtree) (v: int) (w: rbtree) (k: int)
  : Lemma (mem k (fst (clrs_resolve_left c x v w)) <==> (k = v || mem k x || mem k w))
  = match w with
    | Node Red wl wy wr ->
      clrs_del_cases234_left_mem Red x v wl k
    | Node Black _ _ _ ->
      clrs_del_cases234_left_mem c x v w k
    | _ -> ()

let clrs_resolve_right_mem (c: color) (w: rbtree) (v: int) (x: rbtree) (k: int)
  : Lemma (mem k (fst (clrs_resolve_right c w v x)) <==> (k = v || mem k w || mem k x))
  = match w with
    | Node Red wl wy wr ->
      clrs_del_cases234_right_mem Red wr v x k
    | Node Black _ _ _ ->
      clrs_del_cases234_right_mem c w v x k
    | _ -> ()
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 30"
let rec clrs_del_mem (t: rbtree) (k: int) (x: int)
  : Lemma
    (requires is_bst t)
    (ensures mem x (fst (clrs_del t k)) <==> (mem x t /\ x <> k))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        clrs_del_mem l k x;
        bst_lt_not_mem r v k;
        if snd (clrs_del l k) then
          clrs_resolve_left_mem c (fst (clrs_del l k)) v r x
        else ()
      end else if k > v then begin
        clrs_del_mem r k x;
        bst_gt_not_mem l v k;
        if snd (clrs_del r k) then
          clrs_resolve_right_mem c l v (fst (clrs_del r k)) x
        else ()
      end else begin
        // k = v: delete this node
        match l, r with
        | Leaf, Leaf -> ()
        | Leaf, _ ->
          // result = (Node Black rl rv rr, false) = (set_color Black r, false)
          // Need: mem x r <==> (x=v || mem x r) /\ x<>v <==> mem x r /\ x<>v
          // This holds because v is not in r (all_gt r v)
          bst_lt_not_mem r v v
        | _, Leaf ->
          bst_gt_not_mem l v v
        | _, _ ->
          let sk = minimum r in
          minimum_mem r;
          assert (mem sk r);
          all_gt_mem r v sk;  // sk > v since all_gt r v
          assert (sk > v);
          bst_lt_not_mem r v v; // v not in r
          bst_gt_not_mem l v v; // v not in l
          // After deleting sk from r, mem x r' <==> mem x r /\ x<>sk
          clrs_del_mem r sk x;
          let (r', deficit) = clrs_del r sk in
          if deficit then
            clrs_resolve_right_mem c l sk r' x
          else ()
      end
#pop-options

let clrs_delete_mem (t: rbtree) (k: int) (x: int)
  : Lemma
    (requires is_bst t)
    (ensures mem x (clrs_delete t k) <==> (mem x t /\ x <> k))
  = clrs_del_mem t k x

(*** DELETE — BST Preservation ***)

#push-options "--fuel 3 --ifuel 2 --z3rlimit 20"
let clrs_del_cases234_left_all_lt (c: color) (x: rbtree) (v: int)
    (w: rbtree) (bound: int)
  : Lemma
    (requires all_lt x bound /\ v < bound /\ all_lt w bound)
    (ensures all_lt (fst (clrs_del_cases234_left c x v w)) bound)
  = ()

let clrs_del_cases234_left_all_gt (c: color) (x: rbtree) (v: int)
    (w: rbtree) (bound: int)
  : Lemma
    (requires all_gt x bound /\ v > bound /\ all_gt w bound)
    (ensures all_gt (fst (clrs_del_cases234_left c x v w)) bound)
  = ()

let clrs_del_cases234_right_all_lt (c: color) (w: rbtree)
    (v: int) (x: rbtree) (bound: int)
  : Lemma
    (requires all_lt w bound /\ v < bound /\ all_lt x bound)
    (ensures all_lt (fst (clrs_del_cases234_right c w v x)) bound)
  = ()

let clrs_del_cases234_right_all_gt (c: color) (w: rbtree)
    (v: int) (x: rbtree) (bound: int)
  : Lemma
    (requires all_gt w bound /\ v > bound /\ all_gt x bound)
    (ensures all_gt (fst (clrs_del_cases234_right c w v x)) bound)
  = ()

let clrs_resolve_left_all_lt (c: color) (x: rbtree) (v: int) (w: rbtree) (bound: int)
  : Lemma
    (requires all_lt x bound /\ v < bound /\ all_lt w bound)
    (ensures all_lt (fst (clrs_resolve_left c x v w)) bound)
  = match w with
    | Node Red wl wy wr -> clrs_del_cases234_left_all_lt Red x v wl bound
    | Node Black _ _ _ -> clrs_del_cases234_left_all_lt c x v w bound
    | _ -> ()

let clrs_resolve_left_all_gt (c: color) (x: rbtree) (v: int) (w: rbtree) (bound: int)
  : Lemma
    (requires all_gt x bound /\ v > bound /\ all_gt w bound)
    (ensures all_gt (fst (clrs_resolve_left c x v w)) bound)
  = match w with
    | Node Red wl wy wr -> clrs_del_cases234_left_all_gt Red x v wl bound
    | Node Black _ _ _ -> clrs_del_cases234_left_all_gt c x v w bound
    | _ -> ()

let clrs_resolve_right_all_lt (c: color) (w: rbtree) (v: int) (x: rbtree) (bound: int)
  : Lemma
    (requires all_lt w bound /\ v < bound /\ all_lt x bound)
    (ensures all_lt (fst (clrs_resolve_right c w v x)) bound)
  = match w with
    | Node Red wl wy wr -> clrs_del_cases234_right_all_lt Red wr v x bound
    | Node Black _ _ _ -> clrs_del_cases234_right_all_lt c w v x bound
    | _ -> ()

let clrs_resolve_right_all_gt (c: color) (w: rbtree) (v: int) (x: rbtree) (bound: int)
  : Lemma
    (requires all_gt w bound /\ v > bound /\ all_gt x bound)
    (ensures all_gt (fst (clrs_resolve_right c w v x)) bound)
  = match w with
    | Node Red wl wy wr -> clrs_del_cases234_right_all_gt Red wr v x bound
    | Node Black _ _ _ -> clrs_del_cases234_right_all_gt c w v x bound
    | _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 30"
let clrs_del_cases234_left_is_bst (c: color) (x: rbtree) (v: int) (w: rbtree)
  : Lemma
    (requires is_bst x /\ is_bst w /\ all_lt x v /\ all_gt w v)
    (ensures is_bst (fst (clrs_del_cases234_left c x v w)))
  = match w with
    | Node Black wl wy wr ->
      // all_gt w v means wy > v, all_gt wl v, all_gt wr v
      // is_bst w means all_lt wl wy, all_gt wr wy, is_bst wl, is_bst wr
      if not (is_red_node wl) && not (is_red_node wr) then
        // Case 2: (Node Black x v (Node Red wl wy wr))
        // all_lt x v: ok; all_gt (Node Red wl wy wr) v <==> all_gt w v: ok
        ()
      else if is_red_node wr then
        // Case 4: (Node c (Node Black x v wl) wy (set_color Black wr))
        // Need: all_lt (Node Black x v wl) wy <==> all_lt x wy /\ v < wy /\ all_lt wl wy
        // all_lt x v /\ v < wy ==> all_lt x wy (by weakening)
        all_lt_weaken x v wy
      else begin
        // Case 3: wl = Node _ wll wlv wlr
        // Result: (Node c (Node Black x v wll) wlv (Node Black wlr wy wr))
        match wl with
        | Node _ wll wlv wlr ->
          // Need: all_lt x wlv: all_lt x v, v < wy, all_lt wl wy ==> wlv < wy
          // But more directly: all_lt x v and v < wlv? Not necessarily.
          // Actually: all_gt wl v means wlv > v. all_lt x v. So all_lt x wlv by weakening.
          all_lt_weaken x v wlv;
          // all_gt wlr wy? No, all_gt wr wy and wlr is a child of wl.
          // all_gt (Node Black wlr wy wr) wlv: need all_gt wlr wlv (from is_bst wl), wy > wlv (from is_bst wl), all_gt wr wlv (all_gt wr wy, wy > wlv? not necessarily)
          // Actually from is_bst w: all_lt wl wy, so wlv < wy. Also all_gt wr wy.
          // From is_bst wl: all_gt wlr wlv
          // Need: all_gt (Node Black wlr wy wr) wlv: need all_gt wlr wlv (yes), wy > wlv (from all_lt wl wy), all_gt wr wlv
          // all_gt wr wy and wlv < wy ==> all_gt wr wlv (by weakening)
          all_gt_weaken wr wy wlv
        | _ -> ()
      end
    | _ -> ()

let clrs_del_cases234_right_is_bst (c: color) (w: rbtree) (v: int) (x: rbtree)
  : Lemma
    (requires is_bst w /\ is_bst x /\ all_lt w v /\ all_gt x v)
    (ensures is_bst (fst (clrs_del_cases234_right c w v x)))
  = match w with
    | Node Black wl wy wr ->
      if not (is_red_node wl) && not (is_red_node wr) then ()
      else if is_red_node wl then
        // Case 4 symmetric: (Node c (set_color Black wl) wy (Node Black wr v x))
        all_gt_weaken x v wy
      else begin
        // Case 3 symmetric: wr = Node _ wrl wrv wrr
        match wr with
        | Node _ wrl wrv wrr ->
          all_gt_weaken x v wrv;
          all_lt_weaken wl wy wrv
        | _ -> ()
      end
    | _ -> ()

let clrs_resolve_left_is_bst (c: color) (x: rbtree) (v: int) (w: rbtree)
  : Lemma
    (requires is_bst x /\ is_bst w /\ all_lt x v /\ all_gt w v)
    (ensures is_bst (fst (clrs_resolve_left c x v w)))
  = match w with
    | Node Red wl wy wr ->
      // all_gt w v means wy > v, and from is_bst w: all_lt wl wy
      all_lt_weaken x v wy;
      clrs_del_cases234_left_is_bst Red x v wl;
      clrs_del_cases234_left_all_lt Red x v wl wy
    | Node Black _ _ _ ->
      clrs_del_cases234_left_is_bst c x v w
    | _ -> ()

let clrs_resolve_right_is_bst (c: color) (w: rbtree) (v: int) (x: rbtree)
  : Lemma
    (requires is_bst w /\ is_bst x /\ all_lt w v /\ all_gt x v)
    (ensures is_bst (fst (clrs_resolve_right c w v x)))
  = match w with
    | Node Red wl wy wr ->
      all_gt_weaken x v wy;
      clrs_del_cases234_right_is_bst Red wr v x;
      clrs_del_cases234_right_all_gt Red wr v x wy
    | Node Black _ _ _ ->
      clrs_del_cases234_right_is_bst c w v x
    | _ -> ()
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 30"
let rec clrs_del_all_lt (t: rbtree) (k: int) (bound: int)
  : Lemma
    (requires is_bst t /\ all_lt t bound)
    (ensures all_lt (fst (clrs_del t k)) bound)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        clrs_del_all_lt l k bound;
        if snd (clrs_del l k) then
          clrs_resolve_left_all_lt c (fst (clrs_del l k)) v r bound
        else ()
      end else if k > v then begin
        clrs_del_all_lt r k bound;
        if snd (clrs_del r k) then
          clrs_resolve_right_all_lt c l v (fst (clrs_del r k)) bound
        else ()
      end else begin
        match l, r with
        | Leaf, Leaf -> ()
        | Leaf, Node _ rl rv rr -> ()
        | Node _ ll lv lr, Leaf -> ()
        | _, _ ->
          let sk = minimum r in
          minimum_mem r;
          all_lt_mem r bound sk;
          clrs_del_all_lt r sk bound;
          if snd (clrs_del r sk) then
            clrs_resolve_right_all_lt c l sk (fst (clrs_del r sk)) bound
          else ()
      end

let rec clrs_del_all_gt (t: rbtree) (k: int) (bound: int)
  : Lemma
    (requires is_bst t /\ all_gt t bound)
    (ensures all_gt (fst (clrs_del t k)) bound)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        clrs_del_all_gt l k bound;
        if snd (clrs_del l k) then
          clrs_resolve_left_all_gt c (fst (clrs_del l k)) v r bound
        else ()
      end else if k > v then begin
        clrs_del_all_gt r k bound;
        if snd (clrs_del r k) then
          clrs_resolve_right_all_gt c l v (fst (clrs_del r k)) bound
        else ()
      end else begin
        match l, r with
        | Leaf, Leaf -> ()
        | Leaf, Node _ rl rv rr -> ()
        | Node _ ll lv lr, Leaf -> ()
        | _, _ ->
          let sk = minimum r in
          minimum_mem r;
          all_gt_mem r bound sk;  // sk > bound
          clrs_del_all_gt r sk bound;
          if snd (clrs_del r sk) then
            clrs_resolve_right_all_gt c l sk (fst (clrs_del r sk)) bound
          else ()
      end
#pop-options

// Helper: if every element in t is > bound (provable via mem), then all_gt t bound
// We prove this structurally by induction
let rec all_gt_from_mem (t: rbtree) (bound: int)
  : Lemma
    (requires (forall x. mem x t ==> x > bound))
    (ensures all_gt t bound)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r ->
      // v > bound follows from the hypothesis (since mem v t)
      assert (mem v t);
      all_gt_from_mem l bound;
      all_gt_from_mem r bound

// After deleting sk from r (where sk = minimum r), all remaining elements > sk
#push-options "--fuel 3 --ifuel 2 --z3rlimit 30"
let clrs_del_minimum_all_gt (r: rbtree{Node? r}) 
  : Lemma
    (requires is_bst r)
    (ensures (let sk = minimum r in
              all_gt (fst (clrs_del r sk)) sk))
  = let sk = minimum r in
    let result = fst (clrs_del r sk) in
    let aux (x: int)
      : Lemma (requires mem x result)
              (ensures x > sk)
      = clrs_del_mem r sk x;
        minimum_is_min r x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    all_gt_from_mem result sk
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 30"
let rec clrs_del_preserves_bst (t: rbtree) (k: int)
  : Lemma
    (requires is_bst t)
    (ensures is_bst (fst (clrs_del t k)))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        clrs_del_preserves_bst l k;
        clrs_del_all_lt l k v;
        if snd (clrs_del l k) then
          clrs_resolve_left_is_bst c (fst (clrs_del l k)) v r
        else ()
      end else if k > v then begin
        clrs_del_preserves_bst r k;
        clrs_del_all_gt r k v;
        if snd (clrs_del r k) then
          clrs_resolve_right_is_bst c l v (fst (clrs_del r k))
        else ()
      end else begin
        match l, r with
        | Leaf, Leaf -> ()
        | Leaf, Node _ rl rv rr -> ()
        | Node _ ll lv lr, Leaf -> ()
        | _, _ ->
          let sk = minimum r in
          minimum_mem r;
          all_gt_mem r v sk;  // sk > v
          all_lt_weaken l v sk;  // all_lt l sk
          clrs_del_preserves_bst r sk;
          clrs_del_minimum_all_gt r;
          // all_gt (fst (clrs_del r sk)) sk — from clrs_del_minimum_all_gt
          if snd (clrs_del r sk) then
            clrs_resolve_right_is_bst c l sk (fst (clrs_del r sk))
          else ()
      end
#pop-options

let clrs_delete_preserves_bst (t: rbtree) (k: int)
  : Lemma (requires is_bst t) (ensures is_bst (clrs_delete t k))
  = clrs_del_preserves_bst t k

(*** DELETE — RB Property Preservation ***)

// Helper: deficit tracking invariant for clrs_resolve_left/right
#push-options "--fuel 4 --ifuel 2 --z3rlimit 30 --split_queries always"
let clrs_del_cases234_left_props (c: color) (x: rbtree) (v: int)
    (w: rbtree{Node? w /\ Black? (Node?.c w)})
  : Lemma
    (requires same_bh x /\ same_bh w /\ bh x + 1 = bh w /\
             no_red_red x /\ no_red_red w)
    (ensures (let (t, deficit) = clrs_del_cases234_left c x v w in
              same_bh t /\
              (deficit ==> bh t = bh w /\ almost_no_red_red t) /\
              (not deficit ==> bh t = (if c = Black then 1 + bh w else bh w) /\
                               no_red_red t)))
  = let Node Black wl wy wr = w in
    assert (bh x = bh wl);
    assert (bh wl = bh wr);
    match wl, wr with
    | Node Red wll wlv wlr, Node Red wrl wry wrr -> ()
    | Node Red wll wlv wlr, _ -> ()
    | _, Node Red wrl wry wrr -> ()
    | _, _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 30 --split_queries always"
let clrs_del_cases234_right_props (c: color) (w: rbtree{Node? w /\ Black? (Node?.c w)})
    (v: int) (x: rbtree)
  : Lemma
    (requires same_bh w /\ same_bh x /\ bh x + 1 = bh w /\
             no_red_red w /\ no_red_red x)
    (ensures (let (t, deficit) = clrs_del_cases234_right c w v x in
              same_bh t /\
              (deficit ==> bh t = bh w /\ almost_no_red_red t) /\
              (not deficit ==> bh t = (if c = Black then 1 + bh w else bh w) /\
                               no_red_red t)))
  = let Node Black wl wy wr = w in
    assert (bh x = bh wr);
    assert (bh wl = bh wr);
    match wr, wl with
    | Node Red wrl wrv wrr, Node Red wll wly wlr -> ()
    | Node Red wrl wrv wrr, _ -> ()
    | _, Node Red wll wly wlr -> ()
    | _, _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 30 --split_queries always"
let clrs_resolve_left_props (c: color) (x: rbtree) (v: int) (w: rbtree)
  : Lemma
    (requires same_bh x /\ same_bh w /\ bh x + 1 = bh w /\
             no_red_red x /\ no_red_red w /\
             (c = Red ==> ~(Node? w /\ Red? (Node?.c w))))
    (ensures (let (t, deficit) = clrs_resolve_left c x v w in
              same_bh t /\
              (deficit ==> bh t = bh w /\ almost_no_red_red t) /\
              (not deficit ==> bh t = (if c = Black then 1 + bh w else bh w) /\
                               no_red_red t)))
  = match w with
    | Node Red wl wy wr ->
      // Case 1: c must be Black (from precondition)
      // w Red, no_red_red w => wl, wr are Black-rooted
      // bh w = bh wl (Red), bh x + 1 = bh wl
      clrs_del_cases234_left_props Red x v wl
      // cases234 with c=Red: deficit is always false (Case 2: Red=Black is false)
      // bh inner = bh wl, no_red_red inner
      // Result: Node Black inner wy wr, bh = 1 + bh wl = 1 + bh w
      // c=Black, so postcondition wants 1 + bh w. ✓
    | Node Black _ _ _ ->
      clrs_del_cases234_left_props c x v w
    | _ -> ()

let clrs_resolve_right_props (c: color) (w: rbtree) (v: int) (x: rbtree)
  : Lemma
    (requires same_bh w /\ same_bh x /\ bh x + 1 = bh w /\
             no_red_red w /\ no_red_red x /\
             (c = Red ==> ~(Node? w /\ Red? (Node?.c w))))
    (ensures (let (t, deficit) = clrs_resolve_right c w v x in
              same_bh t /\
              (deficit ==> bh t = bh w /\ almost_no_red_red t) /\
              (not deficit ==> bh t = (if c = Black then 1 + bh w else bh w) /\
                               no_red_red t)))
  = match w with
    | Node Red wl wy wr ->
      clrs_del_cases234_right_props Red wr v x
    | Node Black _ _ _ ->
      clrs_del_cases234_right_props c w v x
    | _ -> ()
#pop-options

// Main delete RB preservation: clrs_del preserves same_bh and
// tracks deficit/no_red_red depending on deficit flag
#push-options "--fuel 3 --ifuel 1 --z3rlimit 30 --split_queries always"
let rec clrs_del_props (t: rbtree) (k: int)
  : Lemma
    (requires same_bh t /\ no_red_red t /\ is_bst t)
    (ensures (let (t', deficit) = clrs_del t k in
              same_bh t' /\
              (deficit ==>
                Node? t /\ Black? (Node?.c t) /\
                bh t' = bh t - 1 /\ no_red_red t') /\
              (not deficit ==>
                bh t' = bh t /\
                (Node? t /\ Black? (Node?.c t) ==> no_red_red t') /\
                (Node? t /\ Red? (Node?.c t) ==> no_red_red t'))))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        clrs_del_props l k;
        let (l', deficit) = clrs_del l k in
        if deficit then begin
          // l was Black, l' has bh = bh l - 1, no_red_red l'
          // Establish the c=Red ==> sibling not Red precondition
          assert (c = Red ==> ~(Node? r /\ Red? (Node?.c r)));
          clrs_resolve_left_props c l' v r
          // resolve gives us what we need:
          // resolve deficit=true ==> c=Black (only Case 2 with Black parent),
          //   bh result = bh r = bh l = bh t - 1 (since c=Black means bh t = 1+bh l)
          // resolve deficit=false ==> bh result = bh t, no_red_red result
        end else ()
      end else if k > v then begin
        clrs_del_props r k;
        let (r', deficit) = clrs_del r k in
        if deficit then begin
          assert (c = Red ==> ~(Node? l /\ Red? (Node?.c l)));
          clrs_resolve_right_props c l v r'
        end else ()
      end else begin
        match l, r with
        | Leaf, Leaf -> ()
        | Leaf, Node rc rl rv rr ->
          // c must be Black: if c=Red, then bh(Leaf)=0 and bh r = bh(Leaf)=0,
          // but r=Node, so bh r >= 1 (if rc=Black) or bh r = bh rl >= 0 (if rc=Red).
          // From same_bh: bh l = bh r, bh(Leaf)=0, so bh r=0. 
          // r=Node rc rl rv rr with bh=0 means rc=Red and bh rl=0.
          // rl=Leaf, rr=Leaf (bh=0 and same_bh).
          // But no_red_red (Node c Leaf v (Node Red Leaf rv Leaf)): c can't be Red 
          // (Red child of Red parent). Actually, c=Red is fine if r is Black.
          // If r = Node Black ... then bh r = 1 + bh rl. From bh l = bh r: 0 = 1+bh rl, impossible.
          // So rc=Red, r = Node Red Leaf rv Leaf. bh r = 0 = bh l. ✓
          // c can't be Red because no_red_red(Node Red Leaf v (Node Red ...)) requires r not Red. Contradiction.
          // So c=Black. Result = (Node Black Leaf rv Leaf, false). 
          // bh result = 1. bh t = 1+0 = 1. deficit=false, bh t' = bh t. ✓
          assert (c = Black)
        | Node lc ll lv lr, Leaf ->
          // Symmetric: c must be Black, l must be Red with Leaf children
          assert (c = Black)
        | _, _ ->
          let sk = minimum r in
          minimum_mem r;
          clrs_del_props r sk;
          let (r', deficit) = clrs_del r sk in
          if deficit then begin
            // r was Black, r' has bh = bh r - 1, no_red_red r'
            assert (c = Red ==> ~(Node? l /\ Red? (Node?.c l)));
            clrs_resolve_right_props c l sk r'
          end else ()
      end
#pop-options

let clrs_delete_is_rbtree (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t /\ is_bst t)
    (ensures is_rbtree (clrs_delete t k))
  = clrs_del_props t k
  // is_rbtree t means is_root_black t, so t is Leaf or Node Black.
  // clrs_del_props gives same_bh t' and no_red_red t' (since Node? t ==> Black? c).
  // make_black preserves same_bh and strengthens no_red_red, adds is_root_black.

(*** Membership Equivalence — Okasaki ↔ CLRS ***)

// Both Okasaki insert and CLRS insert produce the same membership set:
//   mem x (insert t k) <==> mem x (clrs_insert t k)
// This follows from both satisfying: mem x (op t k) <==> (x = k \/ mem x t).
let insert_clrs_insert_mem_equiv (t: rbtree) (k: int) (x: int)
  : Lemma
    (requires is_bst t)
    (ensures mem x (insert t k) <==> mem x (clrs_insert t k))
  = insert_mem t k x;
    clrs_insert_mem t k x

// Both Okasaki delete and CLRS delete produce the same membership set:
//   mem x (delete t k) <==> mem x (clrs_delete t k)
// Both satisfy: mem x (op t k) <==> (mem x t /\ x <> k).
let delete_clrs_delete_mem_equiv (t: rbtree) (k: int) (x: int)
  : Lemma
    (requires is_bst t)
    (ensures mem x (delete t k) <==> mem x (clrs_delete t k))
  = delete_mem t k x;
    clrs_delete_mem t k x
