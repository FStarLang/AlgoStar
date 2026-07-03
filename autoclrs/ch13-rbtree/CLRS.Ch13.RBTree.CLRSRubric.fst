module CLRS.Ch13.RBTree.CLRSRubric
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Order

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module MR = Pulse.Lib.MonotonicGhostRef
module SC = CLRS.Common.Complexity.Search.Class
module TO = Pulse.Lib.TotalOrder

type color = | Red | Black

type rbtree (a:Type0) =
  | Leaf : rbtree a
  | Node : c:color -> left:rbtree a -> key:a -> right:rbtree a -> rbtree a

noeq
type rb_node (a:Type0) = {
  key: a;
  color: color;
  left: rb_ptr a;
  right: rb_ptr a;
  p: rb_ptr a;
}
and rb_node_ptr (a:Type) = box (rb_node a)
and rb_ptr (a:Type) = option (rb_node_ptr a)

let max (x y:nat) : nat = if x >= y then x else y

let rec height (a:Type0) (t:rbtree a) : nat =
  match t with
  | Leaf -> 0
  | Node _ l _ r -> 1 + max (height a l) (height a r)

let rec node_count (a:Type0) (t:rbtree a) : nat =
  match t with
  | Leaf -> 0
  | Node _ l _ r -> 1 + node_count a l + node_count a r

let empty_model (a:Type0) : GTot (rbtree a) = Leaf

let rec find_model (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot (option a)
  =
  match t with
  | Leaf -> None
  | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then find_model a ord l key
      else if gt cmp then find_model a ord r key
      else Some k

// ---- BST Predicates ----

let lt_ord (a:Type0) (ord:erased (TO.total_order a)) (x y:a) : GTot bool =
  lt (ord.TO.compare x y)

let gt_ord (a:Type0) (ord:erased (TO.total_order a)) (x y:a) : GTot bool =
  gt (ord.TO.compare x y)

let rec all_lt (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (bound:a) : GTot bool =
  match t with
  | Leaf -> true
  | Node _ l v r -> lt_ord a ord v bound && all_lt a ord l bound && all_lt a ord r bound

let rec all_gt (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (bound:a) : GTot bool =
  match t with
  | Leaf -> true
  | Node _ l v r -> gt_ord a ord v bound && all_gt a ord l bound && all_gt a ord r bound

let rec is_bst (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) : GTot bool =
  match t with
  | Leaf -> true
  | Node _ l v r -> all_lt a ord l v && all_gt a ord r v && is_bst a ord l && is_bst a ord r

let valid (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) : GTot prop =
  is_bst a ord t = true

let is_red_node (a:Type0) (t:rbtree a) : bool =
  match t with
  | Node Red _ _ _ -> true
  | _ -> false

let set_color (a:Type0) (c:color) (t:rbtree a) : rbtree a =
  match t with
  | Node _ l k r -> Node c l k r
  | Leaf -> Leaf

let make_black (a:Type0) (t:rbtree a) : rbtree a =
  set_color a Black t

// ---- set_color is invariant for is_bst/all_lt/all_gt/find_model ----

let set_color_is_bst (a:Type0) (ord:erased (TO.total_order a)) (c:color) (t:rbtree a)
  : Lemma (ensures is_bst a ord (set_color a c t) == is_bst a ord t)
  = match t with
    | Leaf -> ()
    | Node _ l k r -> ()

let set_color_all_lt (a:Type0) (ord:erased (TO.total_order a)) (c:color) (t:rbtree a) (bound:a)
  : Lemma (ensures all_lt a ord (set_color a c t) bound == all_lt a ord t bound)
  = match t with
    | Leaf -> ()
    | Node _ l k r -> ()

let set_color_all_gt (a:Type0) (ord:erased (TO.total_order a)) (c:color) (t:rbtree a) (bound:a)
  : Lemma (ensures all_gt a ord (set_color a c t) bound == all_gt a ord t bound)
  = match t with
    | Leaf -> ()
    | Node _ l k r -> ()

let set_color_find (a:Type0) (ord:erased (TO.total_order a)) (c:color) (t:rbtree a) (key:a)
  : Lemma (ensures find_model a ord (set_color a c t) key == find_model a ord t key)
  = match t with
    | Leaf -> ()
    | Node _ l k r -> ()

// ===== BST Weaken Lemmas =====

let reveal_ord (a:Type0) (ord:erased (TO.total_order a)) : Lemma (
  (forall (x y z:a). {:pattern ord.TO.compare x y; ord.TO.compare y z}
    lt (ord.TO.compare x y) /\ lt (ord.TO.compare y z) ==> lt (ord.TO.compare x z)) /\
  (forall (x y:a). {:pattern ord.TO.compare x y}
    ord.TO.compare x y == TO.flip_order (ord.TO.compare y x)))
  = let _ = ord.TO.properties in ()

let compare_eq_is_eq (a:Type0) (ord:erased (TO.total_order a)) (x y:a)
  : Lemma (requires eq (x `ord.TO.compare` y)) (ensures x == y)
  = let _ = ord.TO.properties in ()

let compare_eq_of_eq (a:Type0) (ord:erased (TO.total_order a)) (x y:a)
  : Lemma (requires x == y) (ensures eq (x `ord.TO.compare` y) = true)
  = let _ = ord.TO.properties in ()

let flip_gt_lt (a:Type0) (ord:erased (TO.total_order a)) (x y:a)
  : Lemma (requires gt_ord a ord x y = true) (ensures lt_ord a ord y x = true)
  = reveal_ord a ord

let flip_lt_gt (a:Type0) (ord:erased (TO.total_order a)) (x y:a)
  : Lemma (requires lt_ord a ord x y = true) (ensures gt_ord a ord y x = true)
  = reveal_ord a ord

let lt_trans (a:Type0) (ord:erased (TO.total_order a)) (x y z:a)
  : Lemma (requires lt_ord a ord x y /\ lt_ord a ord y z)
          (ensures lt_ord a ord x z)
  = reveal_ord a ord

let gt_trans (a:Type0) (ord:erased (TO.total_order a)) (x y z:a)
  : Lemma (requires gt_ord a ord x y /\ gt_ord a ord y z)
          (ensures gt_ord a ord x z)
  = reveal_ord a ord

let compare_lt_trans (a:Type0) (ord:erased (TO.total_order a)) (x y z:a)
  : Lemma (requires lt (ord.TO.compare x y) /\ lt (ord.TO.compare y z))
          (ensures lt (ord.TO.compare x z))
  = reveal_ord a ord

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec find_none_all_lt (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma
      (requires all_lt a ord t key = true)
      (ensures find_model a ord t key == None)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node _ l k r ->
      find_none_all_lt a ord l key;
      find_none_all_lt a ord r key

let rec find_none_all_gt (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma
      (requires all_gt a ord t key = true)
      (ensures find_model a ord t key == None)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node _ l k r ->
      find_none_all_gt a ord l key;
      find_none_all_gt a ord r key

let rec find_some_all_lt_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (bound:a) (key:a)
  : Lemma
      (requires all_lt a ord t bound /\ Some? (find_model a ord t key))
      (ensures lt_ord a ord key bound)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node _ l v r ->
      let cmp = key `ord.TO.compare` v in
      if lt cmp then find_some_all_lt_poly a ord l bound key
      else if gt cmp then find_some_all_lt_poly a ord r bound key
      else compare_eq_is_eq a ord key v

let rec find_some_all_gt_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (bound:a) (key:a)
  : Lemma
      (requires all_gt a ord t bound /\ Some? (find_model a ord t key))
      (ensures gt_ord a ord key bound)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node _ l v r ->
      let cmp = key `ord.TO.compare` v in
      if lt cmp then find_some_all_gt_poly a ord l bound key
      else if gt cmp then find_some_all_gt_poly a ord r bound key
      else compare_eq_is_eq a ord key v
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec all_lt_weaken_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (b1 b2:a)
  : Lemma (requires all_lt a ord t b1 /\ lt_ord a ord b1 b2) (ensures all_lt a ord t b2)
          (decreases t)
  = reveal_ord a ord;
    match t with | Leaf -> () | Node _ l _ r ->
      all_lt_weaken_poly a ord l b1 b2; all_lt_weaken_poly a ord r b1 b2

let rec all_gt_weaken_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (b1 b2:a)
  : Lemma (requires all_gt a ord t b1 /\ gt_ord a ord b1 b2) (ensures all_gt a ord t b2)
          (decreases t)
  = reveal_ord a ord;
    match t with | Leaf -> () | Node _ l _ r ->
      all_gt_weaken_poly a ord l b1 b2; all_gt_weaken_poly a ord r b1 b2
#pop-options

let left_rotate (a:Type0) (t:rbtree a) : rbtree a =
  match t with
  | Node c a_ x (Node rc b y d) -> Node rc (Node c a_ x b) y d
  | _ -> t

let right_rotate (a:Type0) (t:rbtree a) : rbtree a =
  match t with
  | Node c (Node lc a_ x b) y d -> Node lc a_ x (Node c b y d)
  | _ -> t

// ===== Rotation Lemmas =====

#push-options "--fuel 3 --ifuel 2 --z3rlimit 15"
let right_rotate_all_lt
    (a:Type0) (ord:erased (TO.total_order a)) (c lc:color)
    (p:rbtree a) (x:a) (q:rbtree a) (y:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord (Node c (Node lc p x q) y r) bound)
          (ensures all_lt a ord (right_rotate a (Node c (Node lc p x q) y r)) bound)
  = ()

let right_rotate_all_gt
    (a:Type0) (ord:erased (TO.total_order a)) (c lc:color)
    (p:rbtree a) (x:a) (q:rbtree a) (y:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord (Node c (Node lc p x q) y r) bound)
          (ensures all_gt a ord (right_rotate a (Node c (Node lc p x q) y r)) bound)
  = ()

let left_rotate_all_lt
    (a:Type0) (ord:erased (TO.total_order a)) (c rc:color)
    (p:rbtree a) (x:a) (q:rbtree a) (y:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord (Node c p x (Node rc q y r)) bound)
          (ensures all_lt a ord (left_rotate a (Node c p x (Node rc q y r))) bound)
  = ()

let left_rotate_all_gt
    (a:Type0) (ord:erased (TO.total_order a)) (c rc:color)
    (p:rbtree a) (x:a) (q:rbtree a) (y:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord (Node c p x (Node rc q y r)) bound)
          (ensures all_gt a ord (left_rotate a (Node c p x (Node rc q y r))) bound)
  = ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let right_rotate_is_bst
    (a:Type0) (ord:erased (TO.total_order a)) (c lc:color)
    (p:rbtree a) (x:a) (q:rbtree a) (y:a) (r:rbtree a)
  : Lemma (requires is_bst a ord (Node c (Node lc p x q) y r))
          (ensures is_bst a ord (right_rotate a (Node c (Node lc p x q) y r)))
  = reveal_ord a ord;
    flip_lt_gt a ord x y;
    all_gt_weaken_poly a ord r y x

let left_rotate_is_bst
    (a:Type0) (ord:erased (TO.total_order a)) (c rc:color)
    (p:rbtree a) (x:a) (q:rbtree a) (y:a) (r:rbtree a)
  : Lemma (requires is_bst a ord (Node c p x (Node rc q y r)))
          (ensures is_bst a ord (left_rotate a (Node c p x (Node rc q y r))))
  = reveal_ord a ord;
    flip_gt_lt a ord y x;
    all_lt_weaken_poly a ord p x y
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let right_rotate_find
    (a:Type0) (ord:erased (TO.total_order a)) (c lc:color)
    (p:rbtree a) (x:a) (q:rbtree a) (y:a) (r:rbtree a) (key:a)
  : Lemma (requires is_bst a ord (Node c (Node lc p x q) y r))
          (ensures find_model a ord (right_rotate a (Node c (Node lc p x q) y r)) key ==
                   find_model a ord (Node c (Node lc p x q) y r) key)
  = reveal_ord a ord;
    let cx = key `ord.TO.compare` x in
    let cy = key `ord.TO.compare` y in
    if eq cx then compare_eq_is_eq a ord key x
    else if eq cy then compare_eq_is_eq a ord key y

let left_rotate_find
    (a:Type0) (ord:erased (TO.total_order a)) (c rc:color)
    (p:rbtree a) (x:a) (q:rbtree a) (y:a) (r:rbtree a) (key:a)
  : Lemma (requires is_bst a ord (Node c p x (Node rc q y r)))
          (ensures find_model a ord (left_rotate a (Node c p x (Node rc q y r))) key ==
                   find_model a ord (Node c p x (Node rc q y r)) key)
  = reveal_ord a ord;
    let cx = key `ord.TO.compare` x in
    let cy = key `ord.TO.compare` y in
    if eq cx then compare_eq_is_eq a ord key x
    else if eq cy then compare_eq_is_eq a ord key y
#pop-options

let clrs_fixup_left (a:Type0) (c:color) (l:rbtree a) (v:a) (r:rbtree a) : rbtree a =
  match c with
  | Red -> Node Red l v r
  | Black ->
      match l with
      | Node Red (Node Red _ _ _) _ _ ->
          if is_red_node a r then Node Red (set_color a Black l) v (set_color a Black r)
          else right_rotate a (Node Red (set_color a Black l) v r)
      | Node Red _ _ (Node Red _ _ _) ->
          if is_red_node a r then Node Red (set_color a Black l) v (set_color a Black r)
          else
            let l' = left_rotate a l in
            right_rotate a (Node Red (set_color a Black l') v r)
      | _ -> Node Black l v r

let clrs_fixup_right (a:Type0) (c:color) (l:rbtree a) (v:a) (r:rbtree a) : rbtree a =
  match c with
  | Red -> Node Red l v r
  | Black ->
      match r with
      | Node Red (Node Red _ _ _) _ _ ->
          if is_red_node a l then Node Red (set_color a Black l) v (set_color a Black r)
          else
            let r' = right_rotate a r in
            left_rotate a (Node Red l v (set_color a Black r'))
      | Node Red _ _ (Node Red _ _ _) ->
          if is_red_node a l then Node Red (set_color a Black l) v (set_color a Black r)
          else left_rotate a (Node Red l v (set_color a Black r))
      | _ -> Node Black l v r

// ===== clrs_fixup_left / clrs_fixup_right BST + all_lt/all_gt Lemmas =====

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let clrs_fixup_left_all_lt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord l bound /\ all_lt a ord r bound /\ lt_ord a ord v bound)
          (ensures all_lt a ord (clrs_fixup_left a c l v r) bound)
  = match c with
    | Red -> ()
    | Black ->
      match l with
      | Node Red (Node Red gll glx glr) lv lr_ ->
          if is_red_node a r then ()
          else begin
            set_color_all_lt a ord Black l bound;
            right_rotate_all_lt a ord Red Black (Node Red gll glx glr) lv lr_ v r bound
          end
      | Node Red gll_ glx_ (Node Red grl grx grr) ->
          if is_red_node a r then ()
          else begin
            left_rotate_all_lt a ord Red Red gll_ glx_ grl grx grr bound;
            set_color_all_lt a ord Black (left_rotate a l) bound;
            right_rotate_all_lt a ord Red Black (Node Red gll_ glx_ grl) grx grr v r bound
          end
      | _ -> ()

let clrs_fixup_left_all_gt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord l bound /\ all_gt a ord r bound /\ gt_ord a ord v bound)
          (ensures all_gt a ord (clrs_fixup_left a c l v r) bound)
  = match c with
    | Red -> ()
    | Black ->
      match l with
      | Node Red (Node Red gll glx glr) lv lr_ ->
          if is_red_node a r then ()
          else begin
            set_color_all_gt a ord Black l bound;
            right_rotate_all_gt a ord Red Black (Node Red gll glx glr) lv lr_ v r bound
          end
      | Node Red gll_ glx_ (Node Red grl grx grr) ->
          if is_red_node a r then ()
          else begin
            left_rotate_all_gt a ord Red Red gll_ glx_ grl grx grr bound;
            set_color_all_gt a ord Black (left_rotate a l) bound;
            right_rotate_all_gt a ord Red Black (Node Red gll_ glx_ grl) grx grr v r bound
          end
      | _ -> ()

let clrs_fixup_right_all_lt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord l bound /\ all_lt a ord r bound /\ lt_ord a ord v bound)
          (ensures all_lt a ord (clrs_fixup_right a c l v r) bound)
  = match c with
    | Red -> ()
    | Black ->
      match r with
      | Node Red (Node Red rll rlx rlr) rv rr ->
          if is_red_node a l then ()
          else begin
            right_rotate_all_lt a ord Red Red rll rlx rlr rv rr bound;
            set_color_all_lt a ord Black (right_rotate a r) bound;
            left_rotate_all_lt a ord Red Black l v rll rlx (Node Red rlr rv rr) bound
          end
      | Node Red rll_ rlx_ (Node Red rrl rrx rrr) ->
          if is_red_node a l then ()
          else begin
            set_color_all_lt a ord Black r bound;
            left_rotate_all_lt a ord Red Black l v rll_ rlx_ (Node Red rrl rrx rrr) bound
          end
      | _ -> ()

let clrs_fixup_right_all_gt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord l bound /\ all_gt a ord r bound /\ gt_ord a ord v bound)
          (ensures all_gt a ord (clrs_fixup_right a c l v r) bound)
  = match c with
    | Red -> ()
    | Black ->
      match r with
      | Node Red (Node Red rll rlx rlr) rv rr ->
          if is_red_node a l then ()
          else begin
            right_rotate_all_gt a ord Red Red rll rlx rlr rv rr bound;
            set_color_all_gt a ord Black (right_rotate a r) bound;
            left_rotate_all_gt a ord Red Black l v rll rlx (Node Red rlr rv rr) bound
          end
      | Node Red rll_ rlx_ (Node Red rrl rrx rrr) ->
          if is_red_node a l then ()
          else begin
            set_color_all_gt a ord Black r bound;
            left_rotate_all_gt a ord Red Black l v rll_ rlx_ (Node Red rrl rrx rrr) bound
          end
      | _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let clrs_fixup_left_is_bst
    (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires is_bst a ord l /\ is_bst a ord r /\ all_lt a ord l v /\ all_gt a ord r v)
          (ensures is_bst a ord (clrs_fixup_left a c l v r))
  = match c with
    | Red -> ()
    | Black ->
      match l with
      | Node Red (Node Red gll glx glr) lv lr_ ->
          if is_red_node a r then begin
            set_color_is_bst a ord Black l;
            set_color_all_lt a ord Black l v;
            set_color_is_bst a ord Black r;
            set_color_all_gt a ord Black r v
          end else begin
            set_color_is_bst a ord Black l;
            set_color_all_lt a ord Black l v;
            right_rotate_is_bst a ord Red Black (Node Red gll glx glr) lv lr_ v r
          end
      | Node Red gll_ glx_ (Node Red grl grx grr) ->
          if is_red_node a r then begin
            set_color_is_bst a ord Black l;
            set_color_all_lt a ord Black l v;
            set_color_is_bst a ord Black r;
            set_color_all_gt a ord Black r v
          end else begin
            left_rotate_is_bst a ord Red Red gll_ glx_ grl grx grr;
            left_rotate_all_lt a ord Red Red gll_ glx_ grl grx grr v;
            set_color_is_bst a ord Black (left_rotate a l);
            set_color_all_lt a ord Black (left_rotate a l) v;
            right_rotate_is_bst a ord Red Black (Node Red gll_ glx_ grl) grx grr v r
          end
      | _ -> ()

let clrs_fixup_right_is_bst
    (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires is_bst a ord l /\ is_bst a ord r /\ all_lt a ord l v /\ all_gt a ord r v)
          (ensures is_bst a ord (clrs_fixup_right a c l v r))
  = match c with
    | Red -> ()
    | Black ->
      match r with
      | Node Red (Node Red rll rlx rlr) rv rr ->
          if is_red_node a l then begin
            set_color_is_bst a ord Black l;
            set_color_all_lt a ord Black l v;
            set_color_is_bst a ord Black r;
            set_color_all_gt a ord Black r v
          end else begin
            right_rotate_is_bst a ord Red Red rll rlx rlr rv rr;
            right_rotate_all_gt a ord Red Red rll rlx rlr rv rr v;
            set_color_is_bst a ord Black (right_rotate a r);
            set_color_all_gt a ord Black (right_rotate a r) v;
            left_rotate_is_bst a ord Red Black l v rll rlx (Node Red rlr rv rr)
          end
      | Node Red rll_ rlx_ (Node Red rrl rrx rrr) ->
          if is_red_node a l then begin
            set_color_is_bst a ord Black l;
            set_color_all_lt a ord Black l v;
            set_color_is_bst a ord Black r;
            set_color_all_gt a ord Black r v
          end else begin
            set_color_is_bst a ord Black r;
            set_color_all_gt a ord Black r v;
            left_rotate_is_bst a ord Red Black l v rll_ rlx_ (Node Red rrl rrx rrr)
          end
      | _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let clrs_fixup_left_find
    (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a) (key:a)
  : Lemma (requires is_bst a ord l /\ is_bst a ord r /\ all_lt a ord l v /\ all_gt a ord r v)
          (ensures find_model a ord (clrs_fixup_left a c l v r) key ==
                   find_model a ord (Node c l v r) key)
  = reveal_ord a ord;
    match c with
    | Red -> ()
    | Black ->
      match l with
      | Node Red (Node Red gll glx glr) lv lr_ ->
          if is_red_node a r then begin
            set_color_find a ord Black l key;
            set_color_find a ord Black r key
          end else begin
            set_color_is_bst a ord Black l;
            set_color_all_lt a ord Black l v;
            right_rotate_is_bst a ord Red Black (Node Red gll glx glr) lv lr_ v r;
            right_rotate_find a ord Red Black (Node Red gll glx glr) lv lr_ v r key;
            set_color_find a ord Black l key
          end
      | Node Red gll_ glx_ (Node Red grl grx grr) ->
          if is_red_node a r then begin
            set_color_find a ord Black l key;
            set_color_find a ord Black r key
          end else begin
            left_rotate_is_bst a ord Red Red gll_ glx_ grl grx grr;
            left_rotate_all_lt a ord Red Red gll_ glx_ grl grx grr v;
            left_rotate_find a ord Red Red gll_ glx_ grl grx grr key;
            set_color_is_bst a ord Black (left_rotate a l);
            set_color_all_lt a ord Black (left_rotate a l) v;
            right_rotate_is_bst a ord Red Black (Node Red gll_ glx_ grl) grx grr v r;
            right_rotate_find a ord Red Black (Node Red gll_ glx_ grl) grx grr v r key;
            set_color_find a ord Black (left_rotate a l) key
          end
      | _ -> ()

let clrs_fixup_right_find
    (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a) (key:a)
  : Lemma (requires is_bst a ord l /\ is_bst a ord r /\ all_lt a ord l v /\ all_gt a ord r v)
          (ensures find_model a ord (clrs_fixup_right a c l v r) key ==
                   find_model a ord (Node c l v r) key)
  = reveal_ord a ord;
    match c with
    | Red -> ()
    | Black ->
      match r with
      | Node Red (Node Red rll rlx rlr) rv rr ->
          if is_red_node a l then begin
            set_color_find a ord Black l key;
            set_color_find a ord Black r key
          end else begin
            right_rotate_is_bst a ord Red Red rll rlx rlr rv rr;
            right_rotate_all_gt a ord Red Red rll rlx rlr rv rr v;
            right_rotate_find a ord Red Red rll rlx rlr rv rr key;
            set_color_is_bst a ord Black (right_rotate a r);
            set_color_all_gt a ord Black (right_rotate a r) v;
            left_rotate_is_bst a ord Red Black l v rll rlx (Node Red rlr rv rr);
            left_rotate_find a ord Red Black l v rll rlx (Node Red rlr rv rr) key;
            set_color_find a ord Black (right_rotate a r) key
          end
      | Node Red rll_ rlx_ (Node Red rrl rrx rrr) ->
          if is_red_node a l then begin
            set_color_find a ord Black l key;
            set_color_find a ord Black r key
          end else begin
            set_color_is_bst a ord Black r;
            set_color_all_gt a ord Black r v;
            left_rotate_is_bst a ord Red Black l v rll_ rlx_ (Node Red rrl rrx rrr);
            left_rotate_find a ord Red Black l v rll_ rlx_ (Node Red rrl rrx rrr) key;
            set_color_find a ord Black r key
          end
      | _ -> ()
#pop-options

let rec clrs_ins_model (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot (rbtree a)
  =
  match t with
  | Leaf -> Node Red Leaf key Leaf
  | Node c l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then clrs_fixup_left a c (clrs_ins_model a ord l key) k r
      else if gt cmp then clrs_fixup_right a c l k (clrs_ins_model a ord r key)
      else t

let clrs_insert_model (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot (rbtree a)
  =
  make_black a (clrs_ins_model a ord t key)

// ===== Insert BST + find Lemmas =====

let make_black_find_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (ensures find_model a ord (make_black a t) key == find_model a ord t key)
  = set_color_find a ord Black t key

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10"
let rec clrs_ins_all_lt (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a) (bound:a)
  : Lemma (requires all_lt a ord t bound /\ lt_ord a ord k bound)
          (ensures all_lt a ord (clrs_ins_model a ord t k) bound)
          (decreases t)
  = match t with | Leaf -> () | Node c l v r ->
      reveal_ord a ord;
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        clrs_ins_all_lt a ord l k bound;
        clrs_fixup_left_all_lt a ord c (clrs_ins_model a ord l k) v r bound
      end else if gt cmp then begin
        clrs_ins_all_lt a ord r k bound;
        clrs_fixup_right_all_lt a ord c l v (clrs_ins_model a ord r k) bound
      end else ()

let rec clrs_ins_all_gt (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a) (bound:a)
  : Lemma (requires all_gt a ord t bound /\ gt_ord a ord k bound)
          (ensures all_gt a ord (clrs_ins_model a ord t k) bound)
          (decreases t)
  = match t with | Leaf -> () | Node c l v r ->
      reveal_ord a ord;
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        clrs_ins_all_gt a ord l k bound;
        clrs_fixup_left_all_gt a ord c (clrs_ins_model a ord l k) v r bound
      end else if gt cmp then begin
        clrs_ins_all_gt a ord r k bound;
        clrs_fixup_right_all_gt a ord c l v (clrs_ins_model a ord r k) bound
      end else ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let rec clrs_ins_preserves_bst (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires is_bst a ord t) (ensures is_bst a ord (clrs_ins_model a ord t k))
          (decreases t)
  = match t with | Leaf -> () | Node c l v r ->
      reveal_ord a ord;
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        clrs_ins_preserves_bst a ord l k;
        clrs_ins_all_lt a ord l k v;
        clrs_fixup_left_is_bst a ord c (clrs_ins_model a ord l k) v r
      end else if gt cmp then begin
        clrs_ins_preserves_bst a ord r k;
        clrs_ins_all_gt a ord r k v;
        clrs_fixup_right_is_bst a ord c l v (clrs_ins_model a ord r k)
      end else ()
#pop-options

let clrs_insert_model_valid (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires valid a ord t) (ensures valid a ord (clrs_insert_model a ord t k))
  = clrs_ins_preserves_bst a ord t k;
    set_color_is_bst a ord Black (clrs_ins_model a ord t k)

#push-options "--fuel 3 --ifuel 2 --z3rlimit 20"
let rec find_ins_hit (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (requires is_bst a ord t)
          (ensures find_model a ord (clrs_ins_model a ord t key) key == Some key)
          (decreases t)
  = reveal_ord a ord;
    match t with
    | Leaf -> compare_eq_of_eq a ord key key
    | Node c l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then begin
        find_ins_hit a ord l key;
        clrs_ins_preserves_bst a ord l key;
        clrs_ins_all_lt a ord l key k;
        clrs_fixup_left_find a ord c (clrs_ins_model a ord l key) k r key
      end else if gt cmp then begin
        find_ins_hit a ord r key;
        clrs_ins_preserves_bst a ord r key;
        clrs_ins_all_gt a ord r key k;
        clrs_fixup_right_find a ord c l k (clrs_ins_model a ord r key) key
      end else compare_eq_is_eq a ord key k

let rec find_ins_other (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (inserted key:a)
  : Lemma (requires is_bst a ord t /\ SC.same_key a ord key inserted = false)
          (ensures find_model a ord (clrs_ins_model a ord t inserted) key == find_model a ord t key)
          (decreases t)
  = reveal_ord a ord;
    match t with
    | Leaf -> ()
    | Node c l k r ->
      let cmpi = inserted `ord.TO.compare` k in
      if lt cmpi then begin
        find_ins_other a ord l inserted key;
        clrs_ins_preserves_bst a ord l inserted;
        clrs_ins_all_lt a ord l inserted k;
        clrs_fixup_left_find a ord c (clrs_ins_model a ord l inserted) k r key
      end else if gt cmpi then begin
        find_ins_other a ord r inserted key;
        clrs_ins_preserves_bst a ord r inserted;
        clrs_ins_all_gt a ord r inserted k;
        clrs_fixup_right_find a ord c l k (clrs_ins_model a ord r inserted) key
      end else ()
#pop-options

let find_insert_hit (a:Type0) (ord:erased (TO.total_order a)) (m:rbtree a) (key:a)
  : Lemma (requires valid a ord m)
          (ensures find_model a ord (clrs_insert_model a ord m key) key == Some key)
  = find_ins_hit a ord m key;
    make_black_find_poly a ord (clrs_ins_model a ord m key) key

let find_insert_other (a:Type0) (ord:erased (TO.total_order a)) (m:rbtree a) (inserted key:a)
  : Lemma (requires valid a ord m /\ SC.same_key a ord key inserted = false)
          (ensures find_model a ord (clrs_insert_model a ord m inserted) key == find_model a ord m key)
  = find_ins_other a ord m inserted key;
    make_black_find_poly a ord (clrs_ins_model a ord m inserted) key

let rec minimum_model (a:Type0) (t:rbtree a) : option a =
  match t with
  | Leaf -> None
  | Node _ Leaf k _ -> Some k
  | Node _ l _ _ -> minimum_model a l

let clrs_del_cases234_left (a:Type0) (c:color) (x:rbtree a) (v:a) (w:rbtree a)
  : rbtree a & bool
  =
  match w with
  | Leaf -> (Node c x v w, true)
  | Node wc wl wy wr ->
    if Black? wc then
      let wl_red = is_red_node a wl in
      let wr_red = is_red_node a wr in
      if not wl_red && not wr_red then
        (Node Black x v (Node Red wl wy wr), c = Black)
      else if wr_red then
        (Node c (Node Black x v wl) wy (set_color a Black wr), false)
      else
        match wl with
        | Node Red wll wlv wlr ->
            (Node c (Node Black x v wll) wlv (Node Black wlr wy wr), false)
        | Node Black wll wlv wlr ->
            (Node c (Node Black x v wll) wlv (Node Black wlr wy wr), false)
        | Leaf -> (Node c x v w, true)
    else
      (Node c x v w, true)

let clrs_resolve_left (a:Type0) (c:color) (x:rbtree a) (v:a) (w:rbtree a)
  : rbtree a & bool
  =
  match w with
  | Leaf -> (Node c x v w, true)
  | Node wc wl wy wr ->
    if Red? wc then
      let inner = clrs_del_cases234_left a Red x v wl in
      (Node Black (fst inner) wy wr, snd inner)
    else
      clrs_del_cases234_left a c x v w

let clrs_del_cases234_right (a:Type0) (c:color) (w:rbtree a) (v:a) (x:rbtree a)
  : rbtree a & bool
  =
  match w with
  | Leaf -> (Node c w v x, true)
  | Node wc wl wy wr ->
    if Black? wc then
      let wl_red = is_red_node a wl in
      let wr_red = is_red_node a wr in
      if not wl_red && not wr_red then
        (Node Black (Node Red wl wy wr) v x, c = Black)
      else if wl_red then
        (Node c (set_color a Black wl) wy (Node Black wr v x), false)
      else
        match wr with
        | Node Red wrl wrv wrr ->
            (Node c (Node Black wl wy wrl) wrv (Node Black wrr v x), false)
        | Node Black wrl wrv wrr ->
            (Node c (Node Black wl wy wrl) wrv (Node Black wrr v x), false)
        | Leaf -> (Node c w v x, true)
    else
      (Node c w v x, true)

let clrs_resolve_right (a:Type0) (c:color) (w:rbtree a) (v:a) (x:rbtree a)
  : rbtree a & bool
  =
  match w with
  | Leaf -> (Node c w v x, true)
  | Node wc wl wy wr ->
    if Red? wc then
      let inner = clrs_del_cases234_right a Red wr v x in
      (Node Black wl wy (fst inner), snd inner)
    else
      clrs_del_cases234_right a c w v x

let rec clrs_del_model (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot (rbtree a & bool)
  =
  match t with
  | Leaf -> (Leaf, false)
  | Node c l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then
        let lres = clrs_del_model a ord l key in
        if snd lres then clrs_resolve_left a c (fst lres) k r
        else (Node c (fst lres) k r, false)
      else if gt cmp then
        let rres = clrs_del_model a ord r key in
        if snd rres then clrs_resolve_right a c l k (fst rres)
        else (Node c l k (fst rres), false)
      else
        match l, r with
        | Leaf, Leaf -> (Leaf, c = Black)
        | Leaf, Node _ rl rv rr -> (Node Black rl rv rr, false)
        | Node _ ll lv lr, Leaf -> (Node Black ll lv lr, false)
        | _, _ ->
            match minimum_model a r with
            | Some sk ->
                let rres = clrs_del_model a ord r sk in
                if snd rres then clrs_resolve_right a c l sk (fst rres)
                else (Node c l sk (fst rres), false)
            | None -> (Node c l k r, false)

let clrs_delete_model (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot (rbtree a)
  =
  make_black a (fst (clrs_del_model a ord t key))

let rec find_model_some_eq (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma
      (requires Some? (find_model a ord t key))
      (ensures Some?.v (find_model a ord t key) == key)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then find_model_some_eq a ord l key
      else if gt cmp then find_model_some_eq a ord r key
      else ()

let find_empty (a:Type0) (ord:erased (TO.total_order a)) (key:a)
  : Lemma (ensures find_model a ord (empty_model a) key == None)
  = ()

let rec minimum_nonempty (a:Type0) (t:rbtree a)
  : Lemma (requires Node? t) (ensures Some? (minimum_model a t))
          (decreases t)
  = match t with
    | Node _ Leaf _ _ -> ()
    | Node _ l _ _ -> minimum_nonempty a l

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec minimum_in_all_lt (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord t bound /\ Some? (minimum_model a t))
          (ensures lt_ord a ord (Some?.v (minimum_model a t)) bound)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ Leaf _ _ -> ()
    | Node _ l _ _ ->
        minimum_nonempty a l;
        minimum_in_all_lt a ord l bound

let rec minimum_gt_bound (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord t bound /\ Some? (minimum_model a t))
          (ensures gt_ord a ord (Some?.v (minimum_model a t)) bound)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ Leaf _ _ -> ()
    | Node _ l _ _ ->
        minimum_nonempty a l;
        minimum_gt_bound a ord l bound
#pop-options

let rec find_minimum_hit (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a)
  : Lemma
      (requires is_bst a ord t /\ Some? (minimum_model a t))
      (ensures find_model a ord t (Some?.v (minimum_model a t)) ==
               Some (Some?.v (minimum_model a t)))
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node _ Leaf k r ->
      compare_eq_of_eq a ord k k
  | Node _ l k r ->
      minimum_nonempty a l;
      minimum_in_all_lt a ord l k;
      find_minimum_hit a ord l

let rec all_gt_of_lt_min (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma
      (requires is_bst a ord t /\
                Some? (minimum_model a t) /\
                lt_ord a ord key (Some?.v (minimum_model a t)))
      (ensures all_gt a ord t key)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node _ Leaf k r ->
      flip_lt_gt a ord key k;
      all_gt_weaken_poly a ord r k key
  | Node _ l k r ->
      minimum_nonempty a l;
      minimum_in_all_lt a ord l k;
      all_gt_of_lt_min a ord l key;
      assert (lt_ord a ord key k = true);
      flip_lt_gt a ord key k;
      all_gt_weaken_poly a ord r k key

let lt_min_of_lt_bound (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (bound key:a)
  : Lemma
      (requires all_gt a ord t bound /\ Some? (minimum_model a t) /\ lt_ord a ord key bound)
      (ensures lt (ord.TO.compare key (Some?.v (minimum_model a t))))
  =
  minimum_gt_bound a ord t bound;
  flip_gt_lt a ord (Some?.v (minimum_model a t)) bound;
  compare_lt_trans a ord key bound (Some?.v (minimum_model a t))

let find_left_of_successor_root
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (l r dr:rbtree a) (bound key successor:a)
  : Lemma
      (requires all_gt a ord r bound /\
                Some? (minimum_model a r) /\
                successor == Some?.v (minimum_model a r) /\
                lt_ord a ord key bound)
      (ensures find_model a ord (Node c l successor dr) key == find_model a ord l key)
  =
  lt_min_of_lt_bound a ord r bound key;
  assert (ord.TO.compare key successor ==
          ord.TO.compare key (Some?.v (minimum_model a r)));
  assert (lt (ord.TO.compare key successor))

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let clrs_del_cases234_left_all_lt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (x:rbtree a) (v:a) (w:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord x bound /\ all_lt a ord w bound /\ lt_ord a ord v bound)
          (ensures all_lt a ord (fst (clrs_del_cases234_left a c x v w)) bound)
  =
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Black? wc then
        let wl_red = is_red_node a wl in
        let wr_red = is_red_node a wr in
        if not wl_red && not wr_red then ()
        else if wr_red then set_color_all_lt a ord Black wr bound
        else
          match wl with
          | Node Red _ _ _ -> ()
          | Node Black _ _ _ -> ()
          | Leaf -> ()

let clrs_del_cases234_left_all_gt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (x:rbtree a) (v:a) (w:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord x bound /\ all_gt a ord w bound /\ gt_ord a ord v bound)
          (ensures all_gt a ord (fst (clrs_del_cases234_left a c x v w)) bound)
  =
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Black? wc then
        let wl_red = is_red_node a wl in
        let wr_red = is_red_node a wr in
        if not wl_red && not wr_red then ()
        else if wr_red then set_color_all_gt a ord Black wr bound
        else
          match wl with
          | Node Red _ _ _ -> ()
          | Node Black _ _ _ -> ()
          | Leaf -> ()

let clrs_del_cases234_right_all_lt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (w:rbtree a) (v:a) (x:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord w bound /\ all_lt a ord x bound /\ lt_ord a ord v bound)
          (ensures all_lt a ord (fst (clrs_del_cases234_right a c w v x)) bound)
  =
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Black? wc then
        let wl_red = is_red_node a wl in
        let wr_red = is_red_node a wr in
        if not wl_red && not wr_red then ()
        else if wl_red then set_color_all_lt a ord Black wl bound
        else
          match wr with
          | Node Red _ _ _ -> ()
          | Node Black _ _ _ -> ()
          | Leaf -> ()

let clrs_del_cases234_right_all_gt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (w:rbtree a) (v:a) (x:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord w bound /\ all_gt a ord x bound /\ gt_ord a ord v bound)
          (ensures all_gt a ord (fst (clrs_del_cases234_right a c w v x)) bound)
  =
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Black? wc then
        let wl_red = is_red_node a wl in
        let wr_red = is_red_node a wr in
        if not wl_red && not wr_red then ()
        else if wl_red then set_color_all_gt a ord Black wl bound
        else
          match wr with
          | Node Red _ _ _ -> ()
          | Node Black _ _ _ -> ()
          | Leaf -> ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let clrs_del_cases234_left_is_bst
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (x:rbtree a) (v:a) (w:rbtree a)
  : Lemma (requires is_bst a ord x /\ is_bst a ord w /\ all_lt a ord x v /\ all_gt a ord w v)
          (ensures is_bst a ord (fst (clrs_del_cases234_left a c x v w)))
  =
  reveal_ord a ord;
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Black? wc then
        let wl_red = is_red_node a wl in
        let wr_red = is_red_node a wr in
        if not wl_red && not wr_red then ()
        else if wr_red then begin
          flip_gt_lt a ord wy v;
          all_lt_weaken_poly a ord x v wy;
          set_color_is_bst a ord Black wr;
          set_color_all_gt a ord Black wr wy
        end else
          match wl with
          | Node Red wll wlv wlr ->
              flip_gt_lt a ord wlv v;
              all_lt_weaken_poly a ord x v wlv;
              flip_lt_gt a ord wlv wy;
              all_gt_weaken_poly a ord wr wy wlv
          | Node Black wll wlv wlr ->
              flip_gt_lt a ord wlv v;
              all_lt_weaken_poly a ord x v wlv;
              flip_lt_gt a ord wlv wy;
              all_gt_weaken_poly a ord wr wy wlv
          | Leaf -> ()

let clrs_del_cases234_right_is_bst
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (w:rbtree a) (v:a) (x:rbtree a)
  : Lemma (requires is_bst a ord w /\ is_bst a ord x /\ all_lt a ord w v /\ all_gt a ord x v)
          (ensures is_bst a ord (fst (clrs_del_cases234_right a c w v x)))
  =
  reveal_ord a ord;
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Black? wc then
        let wl_red = is_red_node a wl in
        let wr_red = is_red_node a wr in
        if not wl_red && not wr_red then ()
        else if wl_red then begin
          flip_lt_gt a ord wy v;
          all_gt_weaken_poly a ord x v wy;
          set_color_is_bst a ord Black wl;
          set_color_all_lt a ord Black wl wy
        end else
          match wr with
          | Node Red wrl wrv wrr ->
              flip_lt_gt a ord wrv v;
              all_gt_weaken_poly a ord x v wrv;
              flip_gt_lt a ord wrv wy;
              all_lt_weaken_poly a ord wl wy wrv
          | Node Black wrl wrv wrr ->
              flip_lt_gt a ord wrv v;
              all_gt_weaken_poly a ord x v wrv;
              flip_gt_lt a ord wrv wy;
              all_lt_weaken_poly a ord wl wy wrv
          | Leaf -> ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let clrs_resolve_left_all_lt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (x:rbtree a) (v:a) (w:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord x bound /\ all_lt a ord w bound /\ lt_ord a ord v bound)
          (ensures all_lt a ord (fst (clrs_resolve_left a c x v w)) bound)
  =
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Red? wc then
        clrs_del_cases234_left_all_lt a ord Red x v wl bound
      else
        clrs_del_cases234_left_all_lt a ord c x v w bound

let clrs_resolve_left_all_gt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (x:rbtree a) (v:a) (w:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord x bound /\ all_gt a ord w bound /\ gt_ord a ord v bound)
          (ensures all_gt a ord (fst (clrs_resolve_left a c x v w)) bound)
  =
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Red? wc then
        clrs_del_cases234_left_all_gt a ord Red x v wl bound
      else
        clrs_del_cases234_left_all_gt a ord c x v w bound

let clrs_resolve_right_all_lt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (w:rbtree a) (v:a) (x:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord w bound /\ all_lt a ord x bound /\ lt_ord a ord v bound)
          (ensures all_lt a ord (fst (clrs_resolve_right a c w v x)) bound)
  =
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Red? wc then
        clrs_del_cases234_right_all_lt a ord Red wr v x bound
      else
        clrs_del_cases234_right_all_lt a ord c w v x bound

let clrs_resolve_right_all_gt
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (w:rbtree a) (v:a) (x:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord w bound /\ all_gt a ord x bound /\ gt_ord a ord v bound)
          (ensures all_gt a ord (fst (clrs_resolve_right a c w v x)) bound)
  =
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Red? wc then
        clrs_del_cases234_right_all_gt a ord Red wr v x bound
      else
        clrs_del_cases234_right_all_gt a ord c w v x bound
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let clrs_resolve_left_is_bst
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (x:rbtree a) (v:a) (w:rbtree a)
  : Lemma (requires is_bst a ord x /\ is_bst a ord w /\ all_lt a ord x v /\ all_gt a ord w v)
          (ensures is_bst a ord (fst (clrs_resolve_left a c x v w)))
  =
  reveal_ord a ord;
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Red? wc then begin
        flip_gt_lt a ord wy v;
        all_lt_weaken_poly a ord x v wy;
        clrs_del_cases234_left_is_bst a ord Red x v wl;
        clrs_del_cases234_left_all_lt a ord Red x v wl wy
      end else
        clrs_del_cases234_left_is_bst a ord c x v w

let clrs_resolve_right_is_bst
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (w:rbtree a) (v:a) (x:rbtree a)
  : Lemma (requires is_bst a ord w /\ is_bst a ord x /\ all_lt a ord w v /\ all_gt a ord x v)
          (ensures is_bst a ord (fst (clrs_resolve_right a c w v x)))
  =
  reveal_ord a ord;
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      if Red? wc then begin
        flip_lt_gt a ord wy v;
        all_gt_weaken_poly a ord x v wy;
        clrs_del_cases234_right_is_bst a ord Red wr v x;
        clrs_del_cases234_right_all_gt a ord Red wr v x wy
      end else
        clrs_del_cases234_right_is_bst a ord c w v x
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 20"
let rec clrs_del_all_lt (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key bound:a)
  : Lemma (requires is_bst a ord t /\ all_lt a ord t bound)
          (ensures all_lt a ord (fst (clrs_del_model a ord t key)) bound)
          (decreases t)
  =
  match t with
  | Leaf -> ()
  | Node c l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then begin
        clrs_del_all_lt a ord l key bound;
        if snd (clrs_del_model a ord l key) then
          clrs_resolve_left_all_lt a ord c (fst (clrs_del_model a ord l key)) k r bound
      end else if gt cmp then begin
        clrs_del_all_lt a ord r key bound;
        if snd (clrs_del_model a ord r key) then
          clrs_resolve_right_all_lt a ord c l k (fst (clrs_del_model a ord r key)) bound
      end else
        match l, r with
        | Leaf, _ -> ()
        | _, Leaf -> ()
        | _, _ ->
            match minimum_model a r with
            | None -> ()
            | Some successor ->
                minimum_in_all_lt a ord r bound;
                clrs_del_all_lt a ord r successor bound;
                if snd (clrs_del_model a ord r successor) then
                  clrs_resolve_right_all_lt a ord c l successor (fst (clrs_del_model a ord r successor)) bound

let rec clrs_del_all_gt (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key bound:a)
  : Lemma (requires is_bst a ord t /\ all_gt a ord t bound)
          (ensures all_gt a ord (fst (clrs_del_model a ord t key)) bound)
          (decreases t)
  =
  match t with
  | Leaf -> ()
  | Node c l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then begin
        clrs_del_all_gt a ord l key bound;
        if snd (clrs_del_model a ord l key) then
          clrs_resolve_left_all_gt a ord c (fst (clrs_del_model a ord l key)) k r bound
      end else if gt cmp then begin
        clrs_del_all_gt a ord r key bound;
        if snd (clrs_del_model a ord r key) then
          clrs_resolve_right_all_gt a ord c l k (fst (clrs_del_model a ord r key)) bound
      end else
        match l, r with
        | Leaf, _ -> ()
        | _, Leaf -> ()
        | _, _ ->
            match minimum_model a r with
            | None -> ()
            | Some successor ->
                minimum_gt_bound a ord r bound;
                clrs_del_all_gt a ord r successor bound;
                if snd (clrs_del_model a ord r successor) then
                  clrs_resolve_right_all_gt a ord c l successor (fst (clrs_del_model a ord r successor)) bound
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 20"
let rec clrs_del_all_gt_min (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a)
  : Lemma (requires is_bst a ord t /\ Some? (minimum_model a t))
          (ensures (let m = Some?.v (minimum_model a t) in
                    all_gt a ord (fst (clrs_del_model a ord t m)) m))
          (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node c Leaf k r -> ()
  | Node c l k r ->
      minimum_nonempty a l;
      let m = Some?.v (minimum_model a l) in
      minimum_in_all_lt a ord l k;
      flip_lt_gt a ord m k;
      clrs_del_all_gt_min a ord l;
      all_gt_weaken_poly a ord r k m;
      if snd (clrs_del_model a ord l m) then
        clrs_resolve_left_all_gt a ord c (fst (clrs_del_model a ord l m)) k r m
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 20"
let rec clrs_del_preserves_bst (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (requires is_bst a ord t)
          (ensures is_bst a ord (fst (clrs_del_model a ord t key)))
          (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node c l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then begin
        clrs_del_preserves_bst a ord l key;
        clrs_del_all_lt a ord l key k;
        if snd (clrs_del_model a ord l key) then
          clrs_resolve_left_is_bst a ord c (fst (clrs_del_model a ord l key)) k r
      end else if gt cmp then begin
        clrs_del_preserves_bst a ord r key;
        clrs_del_all_gt a ord r key k;
        if snd (clrs_del_model a ord r key) then
          clrs_resolve_right_is_bst a ord c l k (fst (clrs_del_model a ord r key))
      end else
        match l, r with
        | Leaf, _ -> ()
        | _, Leaf -> ()
        | _, _ ->
            match minimum_model a r with
            | None -> ()
            | Some successor ->
                clrs_del_preserves_bst a ord r successor;
                minimum_gt_bound a ord r k;
                flip_gt_lt a ord successor k;
                all_lt_weaken_poly a ord l k successor;
                clrs_del_all_gt_min a ord r;
                if snd (clrs_del_model a ord r successor) then
                  clrs_resolve_right_is_bst a ord c l successor (fst (clrs_del_model a ord r successor))
#pop-options

let clrs_delete_model_valid (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (requires valid a ord t) (ensures valid a ord (clrs_delete_model a ord t key))
  = clrs_del_preserves_bst a ord t key;
    set_color_is_bst a ord Black (fst (clrs_del_model a ord t key))

#push-options "--fuel 5 --ifuel 3 --z3rlimit 20"
let clrs_del_cases234_left_find
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (x:rbtree a) (v:a) (w:rbtree a) (key:a)
  : Lemma (requires is_bst a ord x /\ is_bst a ord w /\ all_lt a ord x v /\ all_gt a ord w v)
          (ensures find_model a ord (fst (clrs_del_cases234_left a c x v w)) key ==
                   find_model a ord (Node c x v w) key)
  =
  reveal_ord a ord;
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      let cv = key `ord.TO.compare` v in
      let cy = key `ord.TO.compare` wy in
      if Black? wc then
        let wl_red = is_red_node a wl in
        let wr_red = is_red_node a wr in
        if not wl_red && not wr_red then ()
        else if wr_red then begin
          set_color_find a ord Black wr key;
          if eq cv then compare_eq_is_eq a ord key v;
          if eq cy then compare_eq_is_eq a ord key wy
        end else
          match wl with
          | Node Red wll wlv wlr ->
              let clv = key `ord.TO.compare` wlv in
              if eq cv then compare_eq_is_eq a ord key v;
              if eq clv then compare_eq_is_eq a ord key wlv;
              if eq cy then compare_eq_is_eq a ord key wy
          | Node Black wll wlv wlr ->
              let clv = key `ord.TO.compare` wlv in
              if eq cv then compare_eq_is_eq a ord key v;
              if eq clv then compare_eq_is_eq a ord key wlv;
              if eq cy then compare_eq_is_eq a ord key wy
          | Leaf -> ()

let clrs_del_cases234_right_find
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (w:rbtree a) (v:a) (x:rbtree a) (key:a)
  : Lemma (requires is_bst a ord w /\ is_bst a ord x /\ all_lt a ord w v /\ all_gt a ord x v)
          (ensures find_model a ord (fst (clrs_del_cases234_right a c w v x)) key ==
                   find_model a ord (Node c w v x) key)
  =
  reveal_ord a ord;
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      let cv = key `ord.TO.compare` v in
      let cy = key `ord.TO.compare` wy in
      if Black? wc then
        let wl_red = is_red_node a wl in
        let wr_red = is_red_node a wr in
        if not wl_red && not wr_red then ()
        else if wl_red then begin
          set_color_find a ord Black wl key;
          if eq cv then compare_eq_is_eq a ord key v;
          if eq cy then compare_eq_is_eq a ord key wy
        end else
          match wr with
          | Node Red wrl wrv wrr ->
              let crv = key `ord.TO.compare` wrv in
              if eq cv then compare_eq_is_eq a ord key v;
              if eq cy then compare_eq_is_eq a ord key wy;
              if eq crv then compare_eq_is_eq a ord key wrv
          | Node Black wrl wrv wrr ->
              let crv = key `ord.TO.compare` wrv in
              if eq cv then compare_eq_is_eq a ord key v;
              if eq cy then compare_eq_is_eq a ord key wy;
              if eq crv then compare_eq_is_eq a ord key wrv
          | Leaf -> ()

let clrs_resolve_left_find
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (x:rbtree a) (v:a) (w:rbtree a) (key:a)
  : Lemma (requires is_bst a ord x /\ is_bst a ord w /\ all_lt a ord x v /\ all_gt a ord w v)
          (ensures find_model a ord (fst (clrs_resolve_left a c x v w)) key ==
                   find_model a ord (Node c x v w) key)
  =
  reveal_ord a ord;
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      let cv = key `ord.TO.compare` v in
      let cy = key `ord.TO.compare` wy in
      if Red? wc then begin
        clrs_del_cases234_left_find a ord Red x v wl key;
        if eq cv then compare_eq_is_eq a ord key v;
        if eq cy then compare_eq_is_eq a ord key wy
      end else
        clrs_del_cases234_left_find a ord c x v w key

let clrs_resolve_right_find
    (a:Type0) (ord:erased (TO.total_order a)) (c:color)
    (w:rbtree a) (v:a) (x:rbtree a) (key:a)
  : Lemma (requires is_bst a ord w /\ is_bst a ord x /\ all_lt a ord w v /\ all_gt a ord x v)
          (ensures find_model a ord (fst (clrs_resolve_right a c w v x)) key ==
                   find_model a ord (Node c w v x) key)
  =
  reveal_ord a ord;
  match w with
  | Leaf -> ()
  | Node wc wl wy wr ->
      let cv = key `ord.TO.compare` v in
      let cy = key `ord.TO.compare` wy in
      if Red? wc then begin
        clrs_del_cases234_right_find a ord Red wr v x key;
        if eq cv then compare_eq_is_eq a ord key v;
        if eq cy then compare_eq_is_eq a ord key wy
      end else
        clrs_del_cases234_right_find a ord c w v x key
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 20"
let rec find_clrs_del_hit (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (requires is_bst a ord t)
          (ensures find_model a ord (fst (clrs_del_model a ord t key)) key == None)
          (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node c l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then begin
        find_clrs_del_hit a ord l key;
        clrs_del_preserves_bst a ord l key;
        clrs_del_all_lt a ord l key k;
        if snd (clrs_del_model a ord l key) then
          clrs_resolve_left_find a ord c (fst (clrs_del_model a ord l key)) k r key
      end else if gt cmp then begin
        find_clrs_del_hit a ord r key;
        clrs_del_preserves_bst a ord r key;
        clrs_del_all_gt a ord r key k;
        if snd (clrs_del_model a ord r key) then
          clrs_resolve_right_find a ord c l k (fst (clrs_del_model a ord r key)) key
      end else begin
        compare_eq_is_eq a ord key k;
        match l, r with
        | Leaf, _ ->
            set_color_find a ord Black r key;
            find_none_all_gt a ord r key
        | _, Leaf ->
            set_color_find a ord Black l key;
            find_none_all_lt a ord l key
        | _, _ ->
            minimum_nonempty a r;
            match minimum_model a r with
            | None -> ()
            | Some successor ->
                minimum_gt_bound a ord r key;
                flip_gt_lt a ord successor key;
                all_lt_weaken_poly a ord l key successor;
                find_none_all_lt a ord l key;
                clrs_del_preserves_bst a ord r successor;
                clrs_del_all_gt_min a ord r;
                if snd (clrs_del_model a ord r successor) then
                  clrs_resolve_right_find a ord c l successor (fst (clrs_del_model a ord r successor)) key
      end

let rec find_clrs_del_other (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (deleted key:a)
  : Lemma (requires is_bst a ord t /\ SC.same_key a ord key deleted = false)
          (ensures find_model a ord (fst (clrs_del_model a ord t deleted)) key ==
                   find_model a ord t key)
          (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node c l k r ->
      let cmpd = deleted `ord.TO.compare` k in
      let cmpk = key `ord.TO.compare` k in
      if lt cmpd then begin
        find_clrs_del_other a ord l deleted key;
        clrs_del_preserves_bst a ord l deleted;
        clrs_del_all_lt a ord l deleted k;
        if snd (clrs_del_model a ord l deleted) then
          clrs_resolve_left_find a ord c (fst (clrs_del_model a ord l deleted)) k r key
      end else if gt cmpd then begin
        find_clrs_del_other a ord r deleted key;
        clrs_del_preserves_bst a ord r deleted;
        clrs_del_all_gt a ord r deleted k;
        if snd (clrs_del_model a ord r deleted) then
          clrs_resolve_right_find a ord c l k (fst (clrs_del_model a ord r deleted)) key
      end else begin
        compare_eq_is_eq a ord deleted k;
        if lt cmpk then begin
          match l, r with
          | Leaf, _ ->
              flip_lt_gt a ord key k;
              all_gt_weaken_poly a ord r k key;
              find_none_all_gt a ord r key;
              set_color_find a ord Black r key
          | _, Leaf -> ()
          | _, _ ->
              minimum_nonempty a r;
              match minimum_model a r with
              | None -> ()
              | Some successor ->
                  assert (successor == Some?.v (minimum_model a r));
                  minimum_gt_bound a ord r k;
                  flip_gt_lt a ord successor k;
                  all_lt_weaken_poly a ord l k successor;
                  clrs_del_preserves_bst a ord r successor;
                  clrs_del_all_gt_min a ord r;
                  find_left_of_successor_root a ord c l r (fst (clrs_del_model a ord r successor)) k key successor;
                  if snd (clrs_del_model a ord r successor) then
                    clrs_resolve_right_find a ord c l successor (fst (clrs_del_model a ord r successor)) key
        end else if gt cmpk then begin
          match l, r with
          | Leaf, _ ->
              set_color_find a ord Black r key
          | _, Leaf ->
              flip_gt_lt a ord key k;
              all_lt_weaken_poly a ord l k key;
              find_none_all_lt a ord l key;
              set_color_find a ord Black l key
          | _, _ ->
              minimum_nonempty a r;
              match minimum_model a r with
              | None -> ()
              | Some successor ->
                  assert (successor == Some?.v (minimum_model a r));
                  let cs = key `ord.TO.compare` successor in
                  if lt cs then begin
                    flip_gt_lt a ord key k;
                    all_lt_weaken_poly a ord l k key;
                    find_none_all_lt a ord l key;
                    all_gt_of_lt_min a ord r key;
                    find_none_all_gt a ord r key
                  end else if gt cs then begin
                    minimum_gt_bound a ord r k;
                    flip_gt_lt a ord successor k;
                    all_lt_weaken_poly a ord l k successor;
                    find_clrs_del_other a ord r successor key;
                    clrs_del_preserves_bst a ord r successor;
                    clrs_del_all_gt_min a ord r;
                    if snd (clrs_del_model a ord r successor) then
                      clrs_resolve_right_find a ord c l successor (fst (clrs_del_model a ord r successor)) key
                  end else begin
                    compare_eq_is_eq a ord key successor;
                    find_minimum_hit a ord r
                  end
        end else begin
          compare_eq_is_eq a ord key k;
          compare_eq_of_eq a ord key deleted;
          assert (SC.same_key a ord key deleted = true)
        end
      end
#pop-options

let find_delete_hit (a:Type0) (ord:erased (TO.total_order a)) (m:rbtree a) (key:a)
  : Lemma (requires valid a ord m)
          (ensures find_model a ord (clrs_delete_model a ord m key) key == None)
  = find_clrs_del_hit a ord m key;
    make_black_find_poly a ord (fst (clrs_del_model a ord m key)) key

let find_delete_other (a:Type0) (ord:erased (TO.total_order a)) (m:rbtree a) (deleted key:a)
  : Lemma (requires valid a ord m /\ SC.same_key a ord key deleted = false)
          (ensures find_model a ord (clrs_delete_model a ord m deleted) key == find_model a ord m key)
  = find_clrs_del_other a ord m deleted key;
    make_black_find_poly a ord (fst (clrs_del_model a ord m deleted)) key

let rec search_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot nat
  =
  match t with
  | Leaf -> 0
  | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then 1 + search_ticks a ord l key
      else if gt cmp then 1 + search_ticks a ord r key
      else 1

let rec clrs_ins_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot nat
  =
  match t with
  | Leaf -> 0
  | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then 1 + clrs_ins_ticks a ord l key
      else if gt cmp then 1 + clrs_ins_ticks a ord r key
      else 1

let clrs_insert_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot nat
  =
  clrs_ins_ticks a ord t key

let rec clrs_del_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot nat
  =
  match t with
  | Leaf -> 0
  | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then 1 + clrs_del_ticks a ord l key
      else if gt cmp then 1 + clrs_del_ticks a ord r key
      else
        match l, r with
        | Leaf, Leaf -> 1
        | Leaf, _ -> 1
        | _, Leaf -> 1
        | _, _ ->
            match minimum_model a r with
            | Some sk -> 1 + clrs_del_ticks a ord r sk
            | None -> 1

let clrs_delete_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot nat
  =
  clrs_del_ticks a ord t key

let search_bound (h:nat) (_n:nat) : nat = h
let insert_bound (h:nat) (_n:nat) : nat = h
let delete_bound (h:nat) (_n:nat) : nat = 2 * h + 1

let rec search_ticks_bounded (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (ensures search_ticks a ord t key <= search_bound (height a t) (node_count a t))
  =
  match t with
  | Leaf -> ()
  | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then search_ticks_bounded a ord l key
      else if gt cmp then search_ticks_bounded a ord r key

let rec clrs_ins_ticks_bounded (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (ensures clrs_insert_ticks a ord t key <= insert_bound (height a t) (node_count a t))
  =
  match t with
  | Leaf -> ()
  | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then clrs_ins_ticks_bounded a ord l key
      else if gt cmp then clrs_ins_ticks_bounded a ord r key

let rec clrs_del_ticks_bounded (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (ensures clrs_delete_ticks a ord t key <= delete_bound (height a t) (node_count a t))
  =
  match t with
  | Leaf -> ()
  | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then clrs_del_ticks_bounded a ord l key
      else if gt cmp then clrs_del_ticks_bounded a ord r key
      else
        match l, r with
        | Leaf, Leaf -> ()
        | Leaf, _ -> ()
        | _, Leaf -> ()
        | _, _ ->
            match minimum_model a r with
            | Some sk -> clrs_del_ticks_bounded a ord r sk
            | None -> ()

let rec rbtree_subtree (a:Type0) (ct:rb_ptr a) (ft:rbtree a) (parent:rb_ptr a)
  : Tot slprop (decreases ft)
  =
  match ft with
  | Leaf -> pure (ct == None #(rb_node_ptr a))
  | Node c l k r ->
      exists* (bp:rb_node_ptr a) (node:rb_node a).
        pure (ct == Some bp) **
        (bp |-> node) **
        pure (node.key == k /\ node.color == c /\ node.p == parent) **
        rbtree_subtree a node.left l (Some bp) **
        rbtree_subtree a node.right r (Some bp)

let owns (a:Type0) (tree:rb_ptr a) (model:rbtree a) : slprop =
  rbtree_subtree a tree model (None #(rb_node_ptr a))

ghost fn elim_leaf (a:Type0) (x:rb_ptr a) (#parent:rb_ptr a)
  requires rbtree_subtree a x Leaf parent
  ensures pure (x == None #(rb_node_ptr a))
{
  unfold (rbtree_subtree a x Leaf parent)
}

ghost fn intro_leaf (a:Type0) (x:rb_ptr a) (parent:rb_ptr a)
  requires pure (x == None #(rb_node_ptr a))
  ensures rbtree_subtree a x Leaf parent
{
  fold (rbtree_subtree a x Leaf parent)
}

ghost fn intro_node (a:Type0) (ct:rb_ptr a) (bp:rb_node_ptr a)
  (#node:rb_node a) (#lt #rt:rbtree a)
  requires
    (bp |-> node) **
    rbtree_subtree a node.left lt (Some bp) **
    rbtree_subtree a node.right rt (Some bp) **
    pure (ct == Some bp)
  ensures rbtree_subtree a ct (Node node.color lt node.key rt) node.p
{
  fold (rbtree_subtree a ct (Node node.color lt node.key rt) node.p)
}

[@@no_mkeys]
let rbtree_cases (a:Type0) (x:rb_ptr a) (ft:rbtree a) (parent:rb_ptr a) =
  match x with
  | None -> pure (ft == Leaf)
  | Some bp ->
      exists* (node:rb_node a) (lt rt:rbtree a).
        (bp |-> node) **
        pure (ft == Node node.color lt node.key rt /\ node.p == parent) **
        rbtree_subtree a node.left lt (Some bp) **
        rbtree_subtree a node.right rt (Some bp)

ghost fn cases_of_rbtree (a:Type0) (x:rb_ptr a) (ft:rbtree a) (parent:rb_ptr a)
  requires rbtree_subtree a x ft parent
  ensures rbtree_cases a x ft parent
{
  match ft {
    Leaf -> {
      unfold (rbtree_subtree a x Leaf parent);
      fold (rbtree_cases a (None #(rb_node_ptr a)) ft parent);
      rewrite rbtree_cases a (None #(rb_node_ptr a)) ft parent as rbtree_cases a x ft parent;
    }
    Node c l k r -> {
      unfold (rbtree_subtree a x (Node c l k r) parent);
      with bp node. _;
      fold (rbtree_cases a (Some bp) ft parent);
      rewrite rbtree_cases a (Some bp) ft parent as rbtree_cases a x ft parent;
    }
  }
}

ghost fn rbtree_case_none (a:Type0) (x:rb_ptr a) (#ft:rbtree a) (#parent:rb_ptr a)
  preserves rbtree_subtree a x ft parent
  requires pure (x == None #(rb_node_ptr a))
  ensures pure (ft == Leaf)
{
  rewrite each x as (None #(rb_node_ptr a));
  cases_of_rbtree a (None #(rb_node_ptr a)) ft parent;
  unfold (rbtree_cases a);
  intro_leaf a (None #(rb_node_ptr a)) parent;
  rewrite rbtree_subtree a (None #(rb_node_ptr a)) Leaf parent as rbtree_subtree a x ft parent
}

ghost fn rbtree_case_some (a:Type0) (x:rb_ptr a) (bp:rb_node_ptr a)
  (#ft:rbtree a) (#parent:rb_ptr a)
  requires rbtree_subtree a x ft parent ** pure (x == Some bp)
  ensures exists* (node:rb_node a) (lt rt:rbtree a).
    (bp |-> node) **
    rbtree_subtree a node.left lt (Some bp) **
    rbtree_subtree a node.right rt (Some bp) **
    pure (ft == Node node.color lt node.key rt /\ node.p == parent)
{
  rewrite each x as (Some bp);
  cases_of_rbtree a (Some bp) ft parent;
  unfold (rbtree_cases a)
}

fn create (a:Type0)
  (#ord:erased (TO.total_order a))
  requires emp
  returns tree:rb_ptr a
  ensures owns a tree (empty_model a) ** pure (valid a ord (empty_model a))
{
  let tree : rb_ptr a = None #(rb_node_ptr a);
  intro_leaf a tree (None #(rb_node_ptr a));
  fold (owns a tree (empty_model a));
  tree
}

fn rec free_rbtree (a:Type0) (tree:rb_ptr a)
  requires rbtree_subtree a tree 'ft 'parent
  ensures emp
  decreases 'ft
{
  match tree {
    None -> {
      cases_of_rbtree a (None #(rb_node_ptr a)) 'ft 'parent;
      unfold (rbtree_cases a)
    }
    Some bp -> {
      rbtree_case_some a (Some bp) bp;
      let node = !bp;
      free_rbtree a node.left;
      free_rbtree a node.right;
      Box.free bp
    }
  }
}

fn dispose (a:Type0)
  (tree:rb_ptr a)
  (#m:erased (rbtree a))
  requires owns a tree m
  ensures emp
{
  unfold (owns a tree m);
  free_rbtree a tree
}

ghost fn rbtree_not_leaf (a:Type0) (x:rb_ptr a) (#ft:rbtree a) (#parent:rb_ptr a)
  preserves rbtree_subtree a x ft parent
  requires pure (Node? ft)
  ensures pure (Some? x)
{
  let Node c lt v rt = ft;
  unfold (rbtree_subtree a x (Node c lt v rt) parent);
  with bp node. _;
  fold (rbtree_subtree a x (Node c lt v rt) parent);
  rewrite rbtree_subtree a x (Node c lt v rt) parent as rbtree_subtree a x ft parent
}

ghost fn rbtree_some_is_node (a:Type0) (x:rb_ptr a) (bp:rb_node_ptr a)
  (#ft:rbtree a) (#parent:rb_ptr a)
  preserves rbtree_subtree a x ft parent
  requires pure (x == Some bp)
  ensures pure (Node? ft)
{
  rbtree_case_some a x bp;
  intro_node a x bp;
  with t p. rewrite rbtree_subtree a x t p as rbtree_subtree a x ft parent
}

ghost fn consume_leaf (a:Type0) (x:rb_ptr a) (#ft:rbtree a) (#parent:rb_ptr a)
  requires rbtree_subtree a x ft parent ** pure (x == None #(rb_node_ptr a))
  ensures pure (ft == Leaf)
{
  rewrite each x as (None #(rb_node_ptr a));
  cases_of_rbtree a (None #(rb_node_ptr a)) ft parent;
  unfold (rbtree_cases a)
}

fn set_parent_ptr (a:Type0) (child:rb_ptr a) (new_parent:rb_ptr a)
  requires rbtree_subtree a child 'ft 'old_parent
  ensures rbtree_subtree a child 'ft new_parent
{
  match child {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) 'ft 'old_parent
        as rbtree_subtree a (None #(rb_node_ptr a)) Leaf 'old_parent;
      elim_leaf a (None #(rb_node_ptr a));
      intro_leaf a (None #(rb_node_ptr a)) new_parent;
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) Leaf new_parent
        as rbtree_subtree a child 'ft new_parent
    }
    Some bp -> {
      rbtree_case_some a (Some bp) bp;
      let node = !bp;
      bp := { node with p = new_parent };
      intro_node a (Some bp) bp;
      with t p. rewrite rbtree_subtree a (Some bp) t p as rbtree_subtree a child 'ft new_parent
    }
  }
}

fn new_node (a:Type0) (key:a) (c:color) (l:rb_ptr a) (r:rb_ptr a) (parent:rb_ptr a)
  (#lt #rt:erased (rbtree a)) (#lp #rp:erased (rb_ptr a))
  requires rbtree_subtree a l lt lp ** rbtree_subtree a r rt rp
  returns y:rb_ptr a
  ensures rbtree_subtree a y (Node c lt key rt) parent ** pure (Some? y)
{
  let bp = Box.alloc ({ key = key; color = c; left = l; right = r; p = parent } <: rb_node a);
  set_parent_ptr a l (Some bp);
  set_parent_ptr a r (Some bp);
  intro_node a (Some bp) bp;
  with t p. rewrite rbtree_subtree a (Some bp) t p as rbtree_subtree a (Some bp) (Node c lt key rt) parent;
  Some bp
}

fn set_node_color (a:Type0) (tree:rb_ptr a) (c:color)
  requires rbtree_subtree a tree 'ft 'parent
  returns y:rb_ptr a
  ensures rbtree_subtree a y (set_color a c 'ft) 'parent ** pure (y == tree)
{
  match tree {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) 'ft 'parent
        as rbtree_subtree a tree (set_color a c 'ft) 'parent;
      tree
    }
    Some bp -> {
      rbtree_case_some a (Some bp) bp;
      let node = !bp;
      bp := { node with color = c };
      intro_node a (Some bp) bp;
      with t p. rewrite rbtree_subtree a (Some bp) t p
        as rbtree_subtree a tree (set_color a c 'ft) 'parent;
      tree
    }
  }
}

fn root_is_color (a:Type0) (tree:rb_ptr a) (c:color)
  (#ft:erased (rbtree a)) (#parent:erased (rb_ptr a))
  preserves rbtree_subtree a tree ft parent
  returns b:bool
  ensures pure (b == (Node? ft && Node?.c ft = c))
{
  match tree {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) ft parent as rbtree_subtree a tree ft parent;
      false
    }
    Some bp -> {
      rewrite each (Some bp) as tree;
      rbtree_case_some a tree bp;
      let node = !bp;
      let res = (node.color = c);
      intro_node a tree bp;
      with t p. rewrite rbtree_subtree a tree t p as rbtree_subtree a tree ft parent;
      res
    }
  }
}

fn check_left_violation (a:Type0) (l:rb_ptr a)
  (#lt:erased (rbtree a)) (#lp:erased (rb_ptr a))
  preserves rbtree_subtree a l lt lp
  returns r:(bool & bool)
  ensures pure (
    (fst r = true /\ snd r = true <==>
      (match lt with | Node Red (Node Red _ _ _) _ _ -> true | _ -> false)) /\
    (fst r = true /\ snd r = false <==>
      (match lt with | Node Red _ _ (Node Red _ _ _) -> true | _ -> false) /\
      ~(match lt with | Node Red (Node Red _ _ _) _ _ -> true | _ -> false)) /\
    (fst r = false ==>
      ~(match lt with | Node Red (Node Red _ _ _) _ _ -> true | _ -> false) /\
      ~(match lt with | Node Red _ _ (Node Red _ _ _) -> true | _ -> false)))
{
  match l {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) lt lp as rbtree_subtree a l lt lp;
      (false, false)
    }
    Some bp -> {
      rewrite each (Some bp) as l;
      rbtree_case_some a l bp;
      let node = !bp;
      let ll_red = root_is_color a node.left Red;
      let lr_red = root_is_color a node.right Red;
      intro_node a l bp;
      with t p. rewrite rbtree_subtree a l t p as rbtree_subtree a l lt lp;
      if (Red? node.color && ll_red) {
        (true, true)
      } else if (Red? node.color && lr_red) {
        (true, false)
      } else {
        (false, false)
      }
    }
  }
}

fn check_right_violation (a:Type0) (r:rb_ptr a)
  (#rt:erased (rbtree a)) (#rp:erased (rb_ptr a))
  preserves rbtree_subtree a r rt rp
  returns res:(bool & bool)
  ensures pure (
    (fst res = true /\ snd res = true <==>
      (match rt with | Node Red (Node Red _ _ _) _ _ -> true | _ -> false)) /\
    (fst res = true /\ snd res = false <==>
      (match rt with | Node Red _ _ (Node Red _ _ _) -> true | _ -> false) /\
      ~(match rt with | Node Red (Node Red _ _ _) _ _ -> true | _ -> false)) /\
    (fst res = false ==>
      ~(match rt with | Node Red (Node Red _ _ _) _ _ -> true | _ -> false) /\
      ~(match rt with | Node Red _ _ (Node Red _ _ _) -> true | _ -> false)))
{
  match r {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) rt rp as rbtree_subtree a r rt rp;
      (false, false)
    }
    Some bp -> {
      rewrite each (Some bp) as r;
      rbtree_case_some a r bp;
      let node = !bp;
      let rl_red = root_is_color a node.left Red;
      let rr_red = root_is_color a node.right Red;
      intro_node a r bp;
      with t p. rewrite rbtree_subtree a r t p as rbtree_subtree a r rt rp;
      if (Red? node.color && rl_red) {
        (true, true)
      } else if (Red? node.color && rr_red) {
        (true, false)
      } else {
        (false, false)
      }
    }
  }
}

fn clrs_fixup_left_ptr (a:Type0) (c:color) (l:rb_ptr a) (v:a) (r:rb_ptr a) (parent:rb_ptr a)
  (#lt #rt:erased (rbtree a)) (#lp #rp:erased (rb_ptr a))
  requires rbtree_subtree a l lt lp ** rbtree_subtree a r rt rp
  returns y:rb_ptr a
  ensures rbtree_subtree a y (clrs_fixup_left a c lt v rt) parent
{
  if (Red? c) {
    let y = new_node a v Red l r parent;
    with t. rewrite rbtree_subtree a y t parent as rbtree_subtree a y (clrs_fixup_left a c lt v rt) parent;
    y
  } else {
    let viol = check_left_violation a l;
    let has_viol = fst viol;
    let is_ll = snd viol;
    if has_viol {
      let uncle_red = root_is_color a r Red;
      if uncle_red {
        let l' = set_node_color a l Black;
        let r' = set_node_color a r Black;
        let y = new_node a v Red l' r' parent;
        with t. rewrite rbtree_subtree a y t parent as rbtree_subtree a y (clrs_fixup_left a c lt v rt) parent;
        y
      } else if is_ll {
        rbtree_not_leaf a l;
        let bp = Some?.v l;
        rbtree_case_some a l bp;
        let node = !bp;
        let new_right = new_node a v Red node.right r parent;
        bp := { key = node.key; color = Black; left = node.left; right = new_right; p = parent };
        set_parent_ptr a new_right (Some bp);
        set_parent_ptr a node.left (Some bp);
        intro_node a l bp;
        with t p. rewrite rbtree_subtree a l t p as rbtree_subtree a l (clrs_fixup_left a c lt v rt) parent;
        l
      } else {
        rbtree_not_leaf a l;
        let bp = Some?.v l;
        rbtree_case_some a l bp;
        let node = !bp;
        rbtree_not_leaf a node.right;
        let rbp = Some?.v node.right;
        rbtree_case_some a node.right rbp;
        let rnode = !rbp;
        bp := { key = node.key; color = Red; left = node.left; right = rnode.left; p = parent };
        set_parent_ptr a rnode.left (Some bp);
        intro_node a l bp;
        let new_right = new_node a v Red rnode.right r parent;
        rbp := { key = rnode.key; color = Black; left = l; right = new_right; p = parent };
        set_parent_ptr a l (Some rbp);
        set_parent_ptr a new_right (Some rbp);
        intro_node a (Some rbp) rbp;
        with t p. rewrite rbtree_subtree a (Some rbp) t p as rbtree_subtree a (Some rbp) (clrs_fixup_left a c lt v rt) parent;
        Some rbp
      }
    } else {
      let y = new_node a v Black l r parent;
      with t. rewrite rbtree_subtree a y t parent as rbtree_subtree a y (clrs_fixup_left a c lt v rt) parent;
      y
    }
  }
}

fn clrs_fixup_right_ptr (a:Type0) (c:color) (l:rb_ptr a) (v:a) (r:rb_ptr a) (parent:rb_ptr a)
  (#lt #rt:erased (rbtree a)) (#lp #rp:erased (rb_ptr a))
  requires rbtree_subtree a l lt lp ** rbtree_subtree a r rt rp
  returns y:rb_ptr a
  ensures rbtree_subtree a y (clrs_fixup_right a c lt v rt) parent
{
  if (Red? c) {
    let y = new_node a v Red l r parent;
    with t. rewrite rbtree_subtree a y t parent as rbtree_subtree a y (clrs_fixup_right a c lt v rt) parent;
    y
  } else {
    let viol = check_right_violation a r;
    let has_viol = fst viol;
    let is_rl = snd viol;
    if has_viol {
      let uncle_red = root_is_color a l Red;
      if uncle_red {
        let l' = set_node_color a l Black;
        let r' = set_node_color a r Black;
        let y = new_node a v Red l' r' parent;
        with t. rewrite rbtree_subtree a y t parent as rbtree_subtree a y (clrs_fixup_right a c lt v rt) parent;
        y
      } else if is_rl {
        rbtree_not_leaf a r;
        let bp = Some?.v r;
        rbtree_case_some a r bp;
        let node = !bp;
        rbtree_not_leaf a node.left;
        let lbp = Some?.v node.left;
        rbtree_case_some a node.left lbp;
        let lnode = !lbp;
        bp := { key = node.key; color = Red; left = lnode.right; right = node.right; p = parent };
        set_parent_ptr a lnode.right (Some bp);
        intro_node a r bp;
        let new_left = new_node a v Red l lnode.left parent;
        lbp := { key = lnode.key; color = Black; left = new_left; right = r; p = parent };
        set_parent_ptr a new_left (Some lbp);
        set_parent_ptr a r (Some lbp);
        intro_node a (Some lbp) lbp;
        with t p. rewrite rbtree_subtree a (Some lbp) t p as rbtree_subtree a (Some lbp) (clrs_fixup_right a c lt v rt) parent;
        Some lbp
      } else {
        rbtree_not_leaf a r;
        let bp = Some?.v r;
        rbtree_case_some a r bp;
        let node = !bp;
        let new_left = new_node a v Red l node.left parent;
        bp := { key = node.key; color = Black; left = new_left; right = node.right; p = parent };
        set_parent_ptr a new_left (Some bp);
        set_parent_ptr a node.right (Some bp);
        intro_node a r bp;
        with t p. rewrite rbtree_subtree a r t p as rbtree_subtree a r (clrs_fixup_right a c lt v rt) parent;
        r
      }
    } else {
      let y = new_node a v Black l r parent;
      with t. rewrite rbtree_subtree a y t parent as rbtree_subtree a y (clrs_fixup_right a c lt v rt) parent;
      y
    }
  }
}

fn rec tree_search (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  preserves rbtree_subtree a tree 'ft 'parent
  requires MR.pts_to ctr #1.0R 'n
  returns result:option a
  ensures exists* ticks.
    MR.pts_to ctr #1.0R ticks **
    pure (result == find_model a ord 'ft key /\
          ticks == reveal 'n + search_ticks a ord 'ft key)
{
  match tree {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) 'ft 'parent as rbtree_subtree a tree 'ft 'parent;
      None
    }
    Some bp -> {
      rbtree_case_some a (Some bp) bp;
      let node = !bp;
      let cmp = iord key node.key;
      if (lt cmp) {
        let result = tree_search a node.left key ctr #ord iord;
        intro_node a (Some bp) bp;
        with t p. rewrite rbtree_subtree a (Some bp) t p as rbtree_subtree a tree 'ft 'parent;
        result
      } else if (gt cmp) {
        let result = tree_search a node.right key ctr #ord iord;
        intro_node a (Some bp) bp;
        with t p. rewrite rbtree_subtree a (Some bp) t p as rbtree_subtree a tree 'ft 'parent;
        result
      } else {
        intro_node a (Some bp) bp;
        with t p. rewrite rbtree_subtree a (Some bp) t p as rbtree_subtree a tree 'ft 'parent;
        Some node.key
      }
    }
  }
}

fn rec tree_minimum (a:Type0) (tree:rb_ptr a) (bp:rb_node_ptr a)
  preserves rbtree_subtree a tree 'ft 'parent
  requires pure (tree == Some bp)
  returns result:a
  ensures pure (minimum_model a 'ft == Some result)
{
  rewrite each tree as (Some bp);
  rbtree_case_some a (Some bp) bp;
  let node = !bp;
  match node.left {
    None -> {
      rbtree_case_none a node.left;
      intro_node a (Some bp) bp;
      with t p. rewrite rbtree_subtree a (Some bp) t p as rbtree_subtree a tree 'ft 'parent;
      node.key
    }
    Some lbp -> {
      let result = tree_minimum a node.left lbp;
      intro_node a (Some bp) bp;
      with t p. rewrite rbtree_subtree a (Some bp) t p as rbtree_subtree a tree 'ft 'parent;
      result
    }
  }
}

fn rec clrs_ins_ptr (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (parent:rb_ptr a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  requires rbtree_subtree a tree 'ft parent ** MR.pts_to ctr #1.0R 'n
  returns y:rb_ptr a
  ensures exists* ticks.
    rbtree_subtree a y (clrs_ins_model a ord 'ft key) parent **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks == reveal 'n + clrs_ins_ticks a ord 'ft key)
{
  match tree {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) 'ft parent
        as rbtree_subtree a (None #(rb_node_ptr a)) Leaf parent;
      elim_leaf a (None #(rb_node_ptr a));
      let left_leaf : rb_ptr a = None #(rb_node_ptr a);
      intro_leaf a left_leaf (None #(rb_node_ptr a));
      let right_leaf : rb_ptr a = None #(rb_node_ptr a);
      intro_leaf a right_leaf (None #(rb_node_ptr a));
      let y = new_node a key Red left_leaf right_leaf parent;
      with t. rewrite rbtree_subtree a y t parent as rbtree_subtree a y (clrs_ins_model a ord 'ft key) parent;
      y
    }
    Some bp -> {
      rbtree_case_some a (Some bp) bp;
      let node = !bp;
      let cmp = iord key node.key;
      if (lt cmp) {
        let new_left = clrs_ins_ptr a node.left key (Some bp) ctr #ord iord;
        Box.free bp;
        let y = clrs_fixup_left_ptr a node.color new_left node.key node.right parent;
        with t. rewrite rbtree_subtree a y t parent as rbtree_subtree a y (clrs_ins_model a ord 'ft key) parent;
        y
      } else if (gt cmp) {
        let new_right = clrs_ins_ptr a node.right key (Some bp) ctr #ord iord;
        Box.free bp;
        let y = clrs_fixup_right_ptr a node.color node.left node.key new_right parent;
        with t. rewrite rbtree_subtree a y t parent as rbtree_subtree a y (clrs_ins_model a ord 'ft key) parent;
        y
      } else {
        bp := { node with p = parent };
        intro_node a (Some bp) bp;
        with t p. rewrite rbtree_subtree a (Some bp) t p as rbtree_subtree a tree (clrs_ins_model a ord 'ft key) parent;
        tree
      }
    }
  }
}

fn make_black_ptr (a:Type0) (tree:rb_ptr a) (parent:rb_ptr a)
  requires rbtree_subtree a tree 'ft 'old_parent
  returns y:rb_ptr a
  ensures rbtree_subtree a y (make_black a 'ft) parent
{
  match tree {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) 'ft 'old_parent
        as rbtree_subtree a (None #(rb_node_ptr a)) Leaf 'old_parent;
      elim_leaf a (None #(rb_node_ptr a));
      intro_leaf a (None #(rb_node_ptr a)) parent;
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) Leaf parent
        as rbtree_subtree a tree (make_black a 'ft) parent;
      tree
    }
    Some bp -> {
      rbtree_case_some a (Some bp) bp;
      let node = !bp;
      bp := { node with color = Black; p = parent };
      intro_node a (Some bp) bp;
      with t p. rewrite rbtree_subtree a (Some bp) t p as rbtree_subtree a tree (make_black a 'ft) parent;
      tree
    }
  }
}

fn clrs_insert_ptr (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (parent:rb_ptr a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  requires rbtree_subtree a tree 'ft parent ** MR.pts_to ctr #1.0R 'n
  returns y:rb_ptr a
  ensures exists* ticks.
    rbtree_subtree a y (clrs_insert_model a ord 'ft key) parent **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks == reveal 'n + clrs_insert_ticks a ord 'ft key)
{
  let t = clrs_ins_ptr a tree key parent ctr #ord iord;
  make_black_ptr a t parent
}

fn clrs_del_cases234_left_ptr (a:Type0)
  (c:color) (x:rb_ptr a) (v:a) (w:rb_ptr a) (parent:rb_ptr a)
  (#xt #wt:erased (rbtree a)) (#xp #wp:erased (rb_ptr a))
  requires rbtree_subtree a x xt xp ** rbtree_subtree a w wt wp
  returns res:(rb_ptr a & bool)
  ensures rbtree_subtree a (fst res) (fst (clrs_del_cases234_left a c xt v wt)) parent **
          pure (snd res == snd (clrs_del_cases234_left a c xt v wt))
{
  match w {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) wt wp
        as rbtree_subtree a w wt wp;
      let y = new_node a v c x w parent;
      with t. rewrite rbtree_subtree a y t parent
        as rbtree_subtree a y (fst (clrs_del_cases234_left a c xt v wt)) parent;
      (y, true)
    }
    Some wbp -> {
      rewrite each (Some wbp) as w;
      rbtree_case_some a w wbp;
      let wn = !wbp;
      if (Black? wn.color) {
        let wl_red = root_is_color a wn.left Red;
        let wr_red = root_is_color a wn.right Red;
        if (not wl_red && not wr_red) {
          wbp := { wn with color = Red; p = parent };
          intro_node a w wbp;
          let y = new_node a v Black x w parent;
          with t. rewrite rbtree_subtree a y t parent
            as rbtree_subtree a y (fst (clrs_del_cases234_left a c xt v wt)) parent;
          (y, (Black? c))
        } else if wr_red {
          let left_child = new_node a v Black x wn.left parent;
          let wr' = set_node_color a wn.right Black;
          Box.free wbp;
          let y = new_node a wn.key c left_child wr' parent;
          with t. rewrite rbtree_subtree a y t parent
            as rbtree_subtree a y (fst (clrs_del_cases234_left a c xt v wt)) parent;
          (y, false)
        } else {
          rbtree_not_leaf a wn.left;
          let wlbp = Some?.v wn.left;
          rbtree_case_some a wn.left wlbp;
          let wln = !wlbp;
          let left_child = new_node a v Black x wln.left parent;
          wbp := { key = wn.key; color = Black; left = wln.right; right = wn.right; p = parent };
          set_parent_ptr a wln.right (Some wbp);
          intro_node a w wbp;
          Box.free wlbp;
          let y = new_node a wln.key c left_child w parent;
          with t. rewrite rbtree_subtree a y t parent
            as rbtree_subtree a y (fst (clrs_del_cases234_left a c xt v wt)) parent;
          (y, false)
        }
      } else {
        intro_node a w wbp;
        let y = new_node a v c x w parent;
        with t. rewrite rbtree_subtree a y t parent
          as rbtree_subtree a y (fst (clrs_del_cases234_left a c xt v wt)) parent;
        (y, true)
      }
    }
  }
}

fn clrs_resolve_left_ptr (a:Type0)
  (c:color) (x:rb_ptr a) (v:a) (w:rb_ptr a) (parent:rb_ptr a)
  (#xt #wt:erased (rbtree a)) (#xp #wp:erased (rb_ptr a))
  requires rbtree_subtree a x xt xp ** rbtree_subtree a w wt wp
  returns res:(rb_ptr a & bool)
  ensures rbtree_subtree a (fst res) (fst (clrs_resolve_left a c xt v wt)) parent **
          pure (snd res == snd (clrs_resolve_left a c xt v wt))
{
  match w {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) wt wp
        as rbtree_subtree a w wt wp;
      let y = new_node a v c x w parent;
      with t. rewrite rbtree_subtree a y t parent
        as rbtree_subtree a y (fst (clrs_resolve_left a c xt v wt)) parent;
      (y, true)
    }
    Some wbp -> {
      rewrite each (Some wbp) as w;
      rbtree_case_some a w wbp;
      let wn = !wbp;
      if (Red? wn.color) {
        let inner = clrs_del_cases234_left_ptr a Red x v wn.left parent;
        let y = new_node a wn.key Black (fst inner) wn.right parent;
        Box.free wbp;
        with t. rewrite rbtree_subtree a y t parent
          as rbtree_subtree a y (fst (clrs_resolve_left a c xt v wt)) parent;
        (y, snd inner)
      } else {
        intro_node a w wbp;
        let res = clrs_del_cases234_left_ptr a c x v w parent;
        with t. rewrite rbtree_subtree a (fst res) t parent
          as rbtree_subtree a (fst res) (fst (clrs_resolve_left a c xt v wt)) parent;
        res
      }
    }
  }
}

fn clrs_del_cases234_right_ptr (a:Type0)
  (c:color) (w:rb_ptr a) (v:a) (x:rb_ptr a) (parent:rb_ptr a)
  (#wt #xt:erased (rbtree a)) (#wp #xp:erased (rb_ptr a))
  requires rbtree_subtree a w wt wp ** rbtree_subtree a x xt xp
  returns res:(rb_ptr a & bool)
  ensures rbtree_subtree a (fst res) (fst (clrs_del_cases234_right a c wt v xt)) parent **
          pure (snd res == snd (clrs_del_cases234_right a c wt v xt))
{
  match w {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) wt wp
        as rbtree_subtree a w wt wp;
      let y = new_node a v c w x parent;
      with t. rewrite rbtree_subtree a y t parent
        as rbtree_subtree a y (fst (clrs_del_cases234_right a c wt v xt)) parent;
      (y, true)
    }
    Some wbp -> {
      rewrite each (Some wbp) as w;
      rbtree_case_some a w wbp;
      let wn = !wbp;
      if (Black? wn.color) {
        let wl_red = root_is_color a wn.left Red;
        let wr_red = root_is_color a wn.right Red;
        if (not wl_red && not wr_red) {
          wbp := { wn with color = Red; p = parent };
          intro_node a w wbp;
          let y = new_node a v Black w x parent;
          with t. rewrite rbtree_subtree a y t parent
            as rbtree_subtree a y (fst (clrs_del_cases234_right a c wt v xt)) parent;
          (y, (Black? c))
        } else if wl_red {
          let wl' = set_node_color a wn.left Black;
          let right_child = new_node a v Black wn.right x parent;
          Box.free wbp;
          let y = new_node a wn.key c wl' right_child parent;
          with t. rewrite rbtree_subtree a y t parent
            as rbtree_subtree a y (fst (clrs_del_cases234_right a c wt v xt)) parent;
          (y, false)
        } else {
          rbtree_not_leaf a wn.right;
          let wrbp = Some?.v wn.right;
          rbtree_case_some a wn.right wrbp;
          let wrn = !wrbp;
          let right_child = new_node a v Black wrn.right x parent;
          wbp := { key = wn.key; color = Black; left = wn.left; right = wrn.left; p = parent };
          set_parent_ptr a wrn.left (Some wbp);
          intro_node a w wbp;
          Box.free wrbp;
          let y = new_node a wrn.key c w right_child parent;
          with t. rewrite rbtree_subtree a y t parent
            as rbtree_subtree a y (fst (clrs_del_cases234_right a c wt v xt)) parent;
          (y, false)
        }
      } else {
        intro_node a w wbp;
        let y = new_node a v c w x parent;
        with t. rewrite rbtree_subtree a y t parent
          as rbtree_subtree a y (fst (clrs_del_cases234_right a c wt v xt)) parent;
        (y, true)
      }
    }
  }
}

fn clrs_resolve_right_ptr (a:Type0)
  (c:color) (w:rb_ptr a) (v:a) (x:rb_ptr a) (parent:rb_ptr a)
  (#wt #xt:erased (rbtree a)) (#wp #xp:erased (rb_ptr a))
  requires rbtree_subtree a w wt wp ** rbtree_subtree a x xt xp
  returns res:(rb_ptr a & bool)
  ensures rbtree_subtree a (fst res) (fst (clrs_resolve_right a c wt v xt)) parent **
          pure (snd res == snd (clrs_resolve_right a c wt v xt))
{
  match w {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) wt wp
        as rbtree_subtree a w wt wp;
      let y = new_node a v c w x parent;
      with t. rewrite rbtree_subtree a y t parent
        as rbtree_subtree a y (fst (clrs_resolve_right a c wt v xt)) parent;
      (y, true)
    }
    Some wbp -> {
      rewrite each (Some wbp) as w;
      rbtree_case_some a w wbp;
      let wn = !wbp;
      if (Red? wn.color) {
        let inner = clrs_del_cases234_right_ptr a Red wn.right v x parent;
        let y = new_node a wn.key Black wn.left (fst inner) parent;
        Box.free wbp;
        with t. rewrite rbtree_subtree a y t parent
          as rbtree_subtree a y (fst (clrs_resolve_right a c wt v xt)) parent;
        (y, snd inner)
      } else {
        intro_node a w wbp;
        let res = clrs_del_cases234_right_ptr a c w v x parent;
        with t. rewrite rbtree_subtree a (fst res) t parent
          as rbtree_subtree a (fst res) (fst (clrs_resolve_right a c wt v xt)) parent;
        res
      }
    }
  }
}

fn rec clrs_del_ptr (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (parent:rb_ptr a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  requires rbtree_subtree a tree 'ft parent ** MR.pts_to ctr #1.0R 'n
  returns res:(rb_ptr a & bool)
  ensures exists* ticks.
    rbtree_subtree a (fst res) (fst (clrs_del_model a ord 'ft key)) parent **
    MR.pts_to ctr #1.0R ticks **
    pure (snd res == snd (clrs_del_model a ord 'ft key) /\
          ticks == reveal 'n + clrs_del_ticks a ord 'ft key)
  decreases 'ft
{
  match tree {
    None -> {
      rbtree_case_none a (None #(rb_node_ptr a));
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) 'ft parent
        as rbtree_subtree a (None #(rb_node_ptr a)) Leaf parent;
      elim_leaf a (None #(rb_node_ptr a));
      intro_leaf a (None #(rb_node_ptr a)) parent;
      rewrite rbtree_subtree a (None #(rb_node_ptr a)) Leaf parent
        as rbtree_subtree a (None #(rb_node_ptr a)) (fst (clrs_del_model a ord 'ft key)) parent;
      ((None #(rb_node_ptr a)), false)
    }
    Some bp -> {
      rbtree_case_some a (Some bp) bp;
      let node = !bp;
      let cmp = iord key node.key;
      if (lt cmp) {
        let res = clrs_del_ptr a node.left key (Some bp) ctr #ord iord;
        Box.free bp;
        if (snd res) {
          let y = clrs_resolve_left_ptr a node.color (fst res) node.key node.right parent;
          with t. rewrite rbtree_subtree a (fst y) t parent
            as rbtree_subtree a (fst y) (fst (clrs_del_model a ord 'ft key)) parent;
          y
        } else {
          let y = new_node a node.key node.color (fst res) node.right parent;
          with t. rewrite rbtree_subtree a y t parent
            as rbtree_subtree a y (fst (clrs_del_model a ord 'ft key)) parent;
          (y, false)
        }
      } else if (gt cmp) {
        let res = clrs_del_ptr a node.right key (Some bp) ctr #ord iord;
        Box.free bp;
        if (snd res) {
          let y = clrs_resolve_right_ptr a node.color node.left node.key (fst res) parent;
          with t. rewrite rbtree_subtree a (fst y) t parent
            as rbtree_subtree a (fst y) (fst (clrs_del_model a ord 'ft key)) parent;
          y
        } else {
          let y = new_node a node.key node.color node.left (fst res) parent;
          with t. rewrite rbtree_subtree a y t parent
            as rbtree_subtree a y (fst (clrs_del_model a ord 'ft key)) parent;
          (y, false)
        }
      } else {
        match node.left {
          None -> {
            consume_leaf a node.left;
            match node.right {
              None -> {
                consume_leaf a node.right;
                Box.free bp;
                let leaf : rb_ptr a = None #(rb_node_ptr a);
                intro_leaf a leaf parent;
                rewrite rbtree_subtree a leaf Leaf parent
                  as rbtree_subtree a leaf (fst (clrs_del_model a ord 'ft key)) parent;
                (leaf, (Black? node.color))
              }
              Some rbp -> {
                rbtree_some_is_node a node.right rbp;
                rbtree_case_some a node.right rbp;
                let rn = !rbp;
                Box.free bp;
                rbp := { rn with color = Black; p = parent };
                intro_node a (Some rbp) rbp;
                with t p. rewrite rbtree_subtree a (Some rbp) t p
                  as rbtree_subtree a (Some rbp) (fst (clrs_del_model a ord 'ft key)) parent;
                ((Some rbp), false)
              }
            }
          }
          Some lbp -> {
            match node.right {
              None -> {
                consume_leaf a node.right;
                rbtree_some_is_node a node.left lbp;
                rbtree_case_some a node.left lbp;
                let ln = !lbp;
                Box.free bp;
                lbp := { ln with color = Black; p = parent };
                intro_node a (Some lbp) lbp;
                with t p. rewrite rbtree_subtree a (Some lbp) t p
                  as rbtree_subtree a (Some lbp) (fst (clrs_del_model a ord 'ft key)) parent;
                ((Some lbp), false)
              }
              Some rbp -> {
                rbtree_some_is_node a node.left lbp;
                rbtree_some_is_node a node.right rbp;
                let sk = tree_minimum a node.right rbp;
                let res = clrs_del_ptr a node.right sk (Some bp) ctr #ord iord;
                Box.free bp;
                if (snd res) {
                  let y = clrs_resolve_right_ptr a node.color node.left sk (fst res) parent;
                  with t. rewrite rbtree_subtree a (fst y) t parent
                    as rbtree_subtree a (fst y) (fst (clrs_del_model a ord 'ft key)) parent;
                  y
                } else {
                  let y = new_node a sk node.color node.left (fst res) parent;
                  with t. rewrite rbtree_subtree a y t parent
                    as rbtree_subtree a y (fst (clrs_del_model a ord 'ft key)) parent;
                  (y, false)
                }
              }
            }
          }
        }
      }
    }
  }
}

fn clrs_delete_ptr (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (parent:rb_ptr a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  requires rbtree_subtree a tree 'ft 'old_parent ** MR.pts_to ctr #1.0R 'n
  returns y:rb_ptr a
  ensures exists* ticks.
    rbtree_subtree a y (clrs_delete_model a ord 'ft key) parent **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks == reveal 'n + clrs_delete_ticks a ord 'ft key)
{
  set_parent_ptr a tree parent;
  let res = clrs_del_ptr a tree key parent ctr #ord iord;
  make_black_ptr a (fst res) parent
}

fn search (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  (#m:erased (rbtree a))
  (#i:erased nat)
  preserves owns a tree m
  requires MR.pts_to ctr #1.0R i ** pure (valid a ord m)
  returns result:option a
  ensures exists* ticks.
    MR.pts_to ctr #1.0R ticks **
    pure (result == find_model a ord m key /\
          ticks <= reveal i + search_bound (height a m) (node_count a m))
{
  unfold (owns a tree m);
  let result = tree_search a tree key ctr #ord iord;
  with ticks. assert (MR.pts_to ctr #1.0R ticks);
  search_ticks_bounded a ord m key;
  fold (owns a tree m);
  result
}

fn insert (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  (#m:erased (rbtree a))
  (#i:erased nat)
  requires owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m)
  returns tree':rb_ptr a
  ensures exists* ticks.
    owns a tree' (clrs_insert_model a ord m key) **
    MR.pts_to ctr #1.0R ticks **
    pure (valid a ord (clrs_insert_model a ord m key) /\
          ticks <= reveal i + insert_bound (height a m) (node_count a m))
{
  unfold (owns a tree m);
  let tree' = clrs_insert_ptr a tree key (None #(rb_node_ptr a)) ctr #ord iord;
  with ticks. assert (MR.pts_to ctr #1.0R ticks);
  clrs_ins_ticks_bounded a ord m key;
  clrs_insert_model_valid a ord m key;
  fold (owns a tree' (clrs_insert_model a ord m key));
  tree'
}

fn delete (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  (#m:erased (rbtree a))
  (#i:erased nat)
  requires owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m)
  returns tree':rb_ptr a
  ensures exists* ticks.
    owns a tree' (clrs_delete_model a ord m key) **
    MR.pts_to ctr #1.0R ticks **
    pure (valid a ord (clrs_delete_model a ord m key) /\
          ticks <= reveal i + delete_bound (height a m) (node_count a m))
{
  unfold (owns a tree m);
  let tree' = clrs_delete_ptr a tree key (None #(rb_node_ptr a)) ctr #ord iord;
  with ticks. assert (MR.pts_to ctr #1.0R ticks);
  clrs_del_ticks_bounded a ord m key;
  clrs_delete_model_valid a ord m key;
  fold (owns a tree' (clrs_delete_model a ord m key));
  tree'
}

instance clrs_parent_pointer_search_structure_instance :
  SC.search_structure
    rb_ptr
    rbtree
    owns
    valid
    empty_model
    find_model
    clrs_insert_model
    clrs_delete_model
    height
    node_count
    search_bound
    insert_bound
    delete_bound
= {
  create = create;
  dispose = dispose;
  search = search;
  insert = insert;
  delete = delete;
}

instance clrs_parent_pointer_search_model_laws_instance :
  SC.search_model_laws
    rbtree
    valid
    empty_model
    find_model
    clrs_insert_model
    clrs_delete_model
= {
  find_empty = find_empty;
  find_insert_hit = find_insert_hit;
  find_insert_other = find_insert_other;
  find_delete_hit = find_delete_hit;
  find_delete_other = find_delete_other;
}
