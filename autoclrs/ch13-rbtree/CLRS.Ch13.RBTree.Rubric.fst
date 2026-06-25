module CLRS.Ch13.RBTree.Rubric
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

// ---- RB Invariant Predicates ----

let rec bh (a:Type0) (t:rbtree a) : nat =
  match t with
  | Leaf -> 0
  | Node c l _ _ -> if c = Black then 1 + bh a l else bh a l

let is_root_black (a:Type0) (t:rbtree a) : bool =
  match t with
  | Leaf -> true
  | Node c _ _ _ -> c = Black

let rec no_red_red (a:Type0) (t:rbtree a) : bool =
  match t with
  | Leaf -> true
  | Node c l _ r ->
    (if c = Red then
       (match l with Leaf -> true | Node cl _ _ _ -> cl = Black) &&
       (match r with Leaf -> true | Node cr _ _ _ -> cr = Black)
     else true) &&
    no_red_red a l && no_red_red a r

let rec same_bh (a:Type0) (t:rbtree a) : bool =
  match t with
  | Leaf -> true
  | Node _ l _ r -> bh a l = bh a r && same_bh a l && same_bh a r

let is_rbtree (a:Type0) (t:rbtree a) : bool =
  is_root_black a t && no_red_red a t && same_bh a t

let almost_no_red_red (a:Type0) (t:rbtree a) : bool =
  match t with
  | Leaf -> true
  | Node _ l _ r -> no_red_red a l && no_red_red a r

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
  is_rbtree a t = true /\ is_bst a ord t = true

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

let make_black (a:Type0) (t:rbtree a) : rbtree a =
  match t with
  | Leaf -> Leaf
  | Node _ l k r -> Node Black l k r

type balance_case =
  | BC_LL
  | BC_LR
  | BC_RL
  | BC_RR
  | BC_None

let balance (a:Type0) (c:color) (l:rbtree a) (key:a) (r:rbtree a) : rbtree a =
  match c, l, r with
  | Black, Node Red (Node Red a_ x b) y c_, _ ->
      Node Red (Node Black a_ x b) y (Node Black c_ key r)
  | Black, Node Red a_ x (Node Red b y c_), _ ->
      Node Red (Node Black a_ x b) y (Node Black c_ key r)
  | Black, _, Node Red (Node Red b y c_) z d ->
      Node Red (Node Black l key b) y (Node Black c_ z d)
  | Black, _, Node Red b y (Node Red c_ z d) ->
      Node Red (Node Black l key b) y (Node Black c_ z d)
  | _ -> Node c l key r

let classify_balance (a:Type0) (c:color) (l:rbtree a) (r:rbtree a) : balance_case =
  match c, l, r with
  | Black, Node Red (Node Red _ _ _) _ _, _ -> BC_LL
  | Black, Node Red _ _ (Node Red _ _ _), _ -> BC_LR
  | Black, _, Node Red (Node Red _ _ _) _ _ -> BC_RL
  | Black, _, Node Red _ _ (Node Red _ _ _) -> BC_RR
  | _ -> BC_None

let classify_balance_lemma (a:Type0) (c:color) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (
    match classify_balance a c l r with
    | BC_LL -> (match l with
                | Node Red (Node Red a_ x b) y c_ ->
                    balance a c l v r == Node Red (Node Black a_ x b) y (Node Black c_ v r)
                | _ -> False)
    | BC_LR -> (match l with
                | Node Red a_ x (Node Red b y c_) ->
                    balance a c l v r == Node Red (Node Black a_ x b) y (Node Black c_ v r)
                | _ -> False)
    | BC_RL -> (match r with
                | Node Red (Node Red b y c_) z d ->
                    balance a c l v r == Node Red (Node Black l v b) y (Node Black c_ z d)
                | _ -> False)
    | BC_RR -> (match r with
                | Node Red b y (Node Red c_ z d) ->
                    balance a c l v r == Node Red (Node Black l v b) y (Node Black c_ z d)
                | _ -> False)
    | BC_None -> balance a c l v r == Node c l v r)
  = ()

let rec ins_model (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot (rbtree a)
  =
  match t with
  | Leaf -> Node Red Leaf key Leaf
  | Node c l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then balance a c (ins_model a ord l key) k r
      else if gt cmp then balance a c l k (ins_model a ord r key)
      else t

let insert_model (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot (rbtree a)
  =
  make_black a (ins_model a ord t key)

let rec minimum_model (a:Type0) (t:rbtree a) : option a =
  match t with
  | Leaf -> None
  | Node _ Leaf k _ -> Some k
  | Node _ l _ _ -> minimum_model a l

let redden (a:Type0) (t:rbtree a) : rbtree a =
  match t with
  | Node Black l k r -> Node Red l k r
  | _ -> t

let balL (a:Type0) (l:rbtree a) (key:a) (r:rbtree a) : rbtree a =
  match l, r with
  | Node Red a_ x b, _ ->
      Node Red (Node Black a_ x b) key r
  | _, Node Black b y c ->
      balance a Black l key (Node Red b y c)
  | _, Node Red (Node Black b y c) z d ->
      Node Red (Node Black l key b) y (balance a Black c z (redden a d))
  | _ -> Node Black l key r

let balR (a:Type0) (l:rbtree a) (key:a) (r:rbtree a) : rbtree a =
  match l, r with
  | _, Node Red b y c ->
      Node Red l key (Node Black b y c)
  | Node Black a_ x b, _ ->
      balance a Black (Node Red a_ x b) key r
  | Node Red a_ x (Node Black b y c), _ ->
      Node Red (balance a Black (redden a a_) x b) y (Node Black c key r)
  | _ -> Node Black l key r

let rec fuse_model (a:Type0) (l r:rbtree a)
  : Tot (rbtree a) (decreases (node_count a l + node_count a r))
  =
  match l, r with
  | Leaf, _ -> r
  | _, Leaf -> l
  | Node Red a_ x b, Node Red c y d ->
      let s = fuse_model a b c in
      (match s with
      | Node Red b' z c' -> Node Red (Node Red a_ x b') z (Node Red c' y d)
      | _ -> Node Red a_ x (Node Red s y d))
  | Node Black a_ x b, Node Black c y d ->
      let s = fuse_model a b c in
      (match s with
      | Node Red b' z c' -> Node Red (Node Black a_ x b') z (Node Black c' y d)
      | _ -> balL a a_ x (Node Black s y d))
  | Node Red a_ x b, _ ->
      Node Red a_ x (fuse_model a b r)
  | _, Node Red c y d ->
      Node Red (fuse_model a l c) y d

let rec del_model (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot (rbtree a)
  =
  match t with
  | Leaf -> Leaf
  | Node c l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then
        match l with
        | Node Black _ _ _ -> balL a (del_model a ord l key) k r
        | _ -> Node Red (del_model a ord l key) k r
      else if gt cmp then
        match r with
        | Node Black _ _ _ -> balR a l k (del_model a ord r key)
        | _ -> Node Red l k (del_model a ord r key)
      else
        fuse_model a l r

let delete_model (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot (rbtree a)
  =
  make_black a (del_model a ord t key)

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

let rec ins_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot nat
  =
  match t with
  | Leaf -> 0
  | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then 1 + ins_ticks a ord l key
      else if gt cmp then 1 + ins_ticks a ord r key
      else 1

let insert_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot nat
  =
  ins_ticks a ord t key

let rec del_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot nat
  =
  match t with
  | Leaf -> 0
  | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then 1 + del_ticks a ord l key
      else if gt cmp then 1 + del_ticks a ord r key
      else 1

let delete_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : GTot nat
  =
  del_ticks a ord t key

// ===== Height Bound Lemmas =====

#push-options "--fuel 2 --ifuel 0 --z3rlimit 5"
let rec min_nodes_poly (a:Type0) (t:rbtree a)
  : Lemma (requires same_bh a t /\ no_red_red a t)
          (ensures node_count a t >= pow2 (bh a t) - 1)
          (decreases (height a t))
  = match t with | Leaf -> () | Node _ l _ r ->
      min_nodes_poly a l; min_nodes_poly a r;
      Math.Lemmas.pow2_plus 1 (bh a l)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec bh_height_bound_poly (a:Type0) (t:rbtree a)
  : Lemma (requires no_red_red a t /\ same_bh a t)
          (ensures height a t <= 2 * bh a t + (if Node? t && (Node?.c t) = Red then 1 else 0))
          (decreases (height a t))
  = match t with | Leaf -> () | Node _ l _ r ->
      bh_height_bound_poly a l; bh_height_bound_poly a r
#pop-options

#push-options "--fuel 2 --ifuel 0 --z3rlimit 5"
let rec pow2_log2_le_poly (n:pos)
  : Lemma (ensures pow2 (SC.log2_floor n) <= n) (decreases n)
  = if n = 1 then ()
    else begin pow2_log2_le_poly (n/2); Math.Lemmas.pow2_plus 1 (SC.log2_floor (n/2)) end
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 5"
let rec log2_floor_ge_poly (n:pos) (k:nat)
  : Lemma (requires n >= pow2 k) (ensures SC.log2_floor n >= k) (decreases k)
  = if k = 0 then ()
    else begin
      Math.Lemmas.pow2_plus 1 (k-1);
      assert (n >= 2); assert (n/2 >= pow2 (k-1));
      log2_floor_ge_poly (n/2) (k-1)
    end
#pop-options

let height_bound_poly (a:Type0) (t:rbtree a)
  : Lemma (requires is_rbtree a t /\ node_count a t >= 1)
          (ensures height a t <= 2 * SC.log2_floor (node_count a t + 1))
  = bh_height_bound_poly a t;
    min_nodes_poly a t;
    log2_floor_ge_poly (node_count a t + 1) (bh a t)

// ===== Balance Structural Lemmas =====

#push-options "--fuel 3 --ifuel 1 --z3rlimit 5"
let balance_same_bh_poly (a:Type0) (c:color) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires same_bh a l /\ same_bh a r /\ bh a l = bh a r)
          (ensures same_bh a (balance a c l v r))
  = ()

let balance_bh_poly (a:Type0) (c:color) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires same_bh a l /\ same_bh a r /\ bh a l = bh a r)
          (ensures bh a (balance a c l v r) = bh a (Node c l v r))
  = ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let balance_restores_no_red_red_left_poly (a:Type0) (c:color) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires c = Black /\ almost_no_red_red a l /\ no_red_red a r)
          (ensures no_red_red a (balance a c l v r))
  = match l with
    | Node Red (Node Red _ _ _) _ _ -> ()
    | Node Red _ _ (Node Red _ _ _) -> ()
    | _ -> ()

let balance_restores_no_red_red_right_poly (a:Type0) (c:color) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires c = Black /\ no_red_red a l /\ almost_no_red_red a r)
          (ensures no_red_red a (balance a c l v r))
  = match r with
    | Node Red (Node Red _ _ _) _ _ -> ()
    | Node Red _ _ (Node Red _ _ _) -> ()
    | _ -> ()
#pop-options

// ===== BST Weaken Lemmas =====

let reveal_ord (a:Type0) (ord:erased (TO.total_order a)) : Lemma (
  (forall (x y z:a). {:pattern ord.TO.compare x y; ord.TO.compare y z}
    lt (ord.TO.compare x y) /\ lt (ord.TO.compare y z) ==> lt (ord.TO.compare x z)) /\
  (forall (x y:a). {:pattern ord.TO.compare x y}
    ord.TO.compare x y == TO.flip_order (ord.TO.compare y x)))
  = let _ = ord.TO.properties in ()

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

// ===== Balance BST Lemmas =====

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10"
let balance_all_lt_poly (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord l bound /\ all_lt a ord r bound /\ lt_ord a ord v bound)
          (ensures all_lt a ord (balance a c l v r) bound)
  = ()

let balance_all_gt_poly (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord l bound /\ all_gt a ord r bound /\ gt_ord a ord v bound)
          (ensures all_gt a ord (balance a c l v r) bound)
  = ()
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10"
let rec ins_all_lt_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a) (bound:a)
  : Lemma (requires all_lt a ord t bound /\ lt_ord a ord k bound)
          (ensures all_lt a ord (ins_model a ord t k) bound)
          (decreases t)
  = match t with | Leaf -> () | Node c l v r ->
      reveal_ord a ord;
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        ins_all_lt_poly a ord l k bound;
        balance_all_lt_poly a ord c (ins_model a ord l k) v r bound
      end else if gt cmp then begin
        ins_all_lt_poly a ord r k bound;
        balance_all_lt_poly a ord c l v (ins_model a ord r k) bound
      end else ()

let rec ins_all_gt_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a) (bound:a)
  : Lemma (requires all_gt a ord t bound /\ gt_ord a ord k bound)
          (ensures all_gt a ord (ins_model a ord t k) bound)
          (decreases t)
  = match t with | Leaf -> () | Node c l v r ->
      reveal_ord a ord;
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        ins_all_gt_poly a ord l k bound;
        balance_all_gt_poly a ord c (ins_model a ord l k) v r bound
      end else if gt cmp then begin
        ins_all_gt_poly a ord r k bound;
        balance_all_gt_poly a ord c l v (ins_model a ord r k) bound
      end else ()
#pop-options

// ===== balance_is_bst_poly =====

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let balance_is_bst_poly (a:Type0) (ord:erased (TO.total_order a)) (c:color) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires is_bst a ord l /\ is_bst a ord r /\ all_lt a ord l v /\ all_gt a ord r v)
          (ensures is_bst a ord (balance a c l v r))
  = reveal_ord a ord;
    match c, l, r with
    | Black, Node Red (Node Red a_ x b) y c_, _ ->
      all_lt_weaken_poly a ord a_ x y;
      all_gt_weaken_poly a ord r v y
    | Black, Node Red a_ x (Node Red b y c_), _ ->
      all_lt_weaken_poly a ord a_ x y;
      all_gt_weaken_poly a ord r v y
    | Black, _, Node Red (Node Red b y c_) z d ->
      all_lt_weaken_poly a ord l v y;
      all_gt_weaken_poly a ord d z y
    | Black, _, Node Red b y (Node Red c_ z d) ->
      all_lt_weaken_poly a ord l v y
    | _ -> ()
#pop-options

// ===== ins_preserves_bst_poly =====

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let rec ins_preserves_bst_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires is_bst a ord t) (ensures is_bst a ord (ins_model a ord t k))
          (decreases t)
  = match t with | Leaf -> () | Node c l v r ->
      reveal_ord a ord;
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        ins_preserves_bst_poly a ord l k;
        ins_all_lt_poly a ord l k v;
        balance_is_bst_poly a ord c (ins_model a ord l k) v r
      end else if gt cmp then begin
        ins_preserves_bst_poly a ord r k;
        ins_all_gt_poly a ord r k v;
        balance_is_bst_poly a ord c l v (ins_model a ord r k)
      end else ()
#pop-options

// ===== ins_properties_poly =====

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10"
let rec ins_properties_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires same_bh a t /\ no_red_red a t)
          (ensures same_bh a (ins_model a ord t k) /\
                   bh a (ins_model a ord t k) = bh a t /\
                   almost_no_red_red a (ins_model a ord t k) /\
                   (Node? t /\ Black? (Node?.c t) ==> no_red_red a (ins_model a ord t k)))
          (decreases t)
  = match t with | Leaf -> () | Node c l v r ->
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        ins_properties_poly a ord l k;
        balance_same_bh_poly a c (ins_model a ord l k) v r;
        balance_bh_poly a c (ins_model a ord l k) v r;
        if c = Black then balance_restores_no_red_red_left_poly a c (ins_model a ord l k) v r
        else ()
      end else if gt cmp then begin
        ins_properties_poly a ord r k;
        balance_same_bh_poly a c l v (ins_model a ord r k);
        balance_bh_poly a c l v (ins_model a ord r k);
        if c = Black then balance_restores_no_red_red_right_poly a c l v (ins_model a ord r k)
        else ()
      end else ()
#pop-options

// ===== Insert Validity =====

let insert_is_rbtree_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires is_rbtree a t) (ensures is_rbtree a (insert_model a ord t k))
  = ins_properties_poly a ord t k

let insert_preserves_bst_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires is_bst a ord t) (ensures is_bst a ord (insert_model a ord t k))
  = ins_preserves_bst_poly a ord t k

let insert_model_valid (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires valid a ord t) (ensures valid a ord (insert_model a ord t k))
  = insert_is_rbtree_poly a ord t k; insert_preserves_bst_poly a ord t k

// ===== Delete Structural Lemmas =====

#push-options "--fuel 5 --ifuel 3 --z3rlimit 15"
let balL_props_poly (a:Type0) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires same_bh a l /\ same_bh a r /\ bh a l + 1 = bh a r /\
                    almost_no_red_red a l /\ no_red_red a r)
          (ensures same_bh a (balL a l v r) /\ bh a (balL a l v r) = bh a r /\
                   almost_no_red_red a (balL a l v r))
  = match l, r with
    | Node Red _ _ _, _ -> ()
    | _, Node Black b y c ->
      balance_same_bh_poly a Black l v (Node Red b y c);
      balance_bh_poly a Black l v (Node Red b y c);
      balance_restores_no_red_red_right_poly a Black l v (Node Red b y c)
    | _, Node Red (Node Black b y c) z d ->
      balance_same_bh_poly a Black c z (redden a d);
      balance_bh_poly a Black c z (redden a d);
      balance_restores_no_red_red_right_poly a Black c z (redden a d)
    | _ -> ()

let balL_strong_poly (a:Type0) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires same_bh a l /\ same_bh a r /\ bh a l + 1 = bh a r /\
                    almost_no_red_red a l /\ no_red_red a r /\
                    (Leaf? r \/ Black? (Node?.c r)))
          (ensures same_bh a (balL a l v r) /\ bh a (balL a l v r) = bh a r /\
                   no_red_red a (balL a l v r))
  = match l, r with
    | Node Red _ _ _, _ -> ()
    | _, Node Black b y c ->
      balance_same_bh_poly a Black l v (Node Red b y c);
      balance_bh_poly a Black l v (Node Red b y c);
      balance_restores_no_red_red_right_poly a Black l v (Node Red b y c)
    | _ -> ()

let balR_props_poly (a:Type0) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires same_bh a l /\ same_bh a r /\ bh a l = bh a r + 1 /\
                    no_red_red a l /\ almost_no_red_red a r)
          (ensures same_bh a (balR a l v r) /\ bh a (balR a l v r) = bh a l /\
                   almost_no_red_red a (balR a l v r))
  = match l, r with
    | _, Node Red _ _ _ -> ()
    | Node Black a_ x b, _ ->
      balance_same_bh_poly a Black (Node Red a_ x b) v r;
      balance_bh_poly a Black (Node Red a_ x b) v r;
      balance_restores_no_red_red_left_poly a Black (Node Red a_ x b) v r
    | Node Red a_ x (Node Black b y c), _ ->
      balance_same_bh_poly a Black (redden a a_) x b;
      balance_bh_poly a Black (redden a a_) x b;
      balance_restores_no_red_red_left_poly a Black (redden a a_) x b
    | _ -> ()

let balR_strong_poly (a:Type0) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires same_bh a l /\ same_bh a r /\ bh a l = bh a r + 1 /\
                    no_red_red a l /\ almost_no_red_red a r /\
                    (Leaf? l \/ Black? (Node?.c l)))
          (ensures same_bh a (balR a l v r) /\ bh a (balR a l v r) = bh a l /\
                   no_red_red a (balR a l v r))
  = match l, r with
    | _, Node Red _ _ _ -> ()
    | Node Black a_ x b, _ ->
      balance_same_bh_poly a Black (Node Red a_ x b) v r;
      balance_bh_poly a Black (Node Red a_ x b) v r;
      balance_restores_no_red_red_left_poly a Black (Node Red a_ x b) v r
    | _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 15"
let rec fuse_props_poly (a:Type0) (l r:rbtree a)
  : Lemma (requires same_bh a l /\ same_bh a r /\ bh a l = bh a r /\
                    no_red_red a l /\ no_red_red a r)
          (ensures same_bh a (fuse_model a l r) /\ bh a (fuse_model a l r) = bh a l /\
                   ((Leaf? l \/ Black? (Node?.c l)) /\ (Leaf? r \/ Black? (Node?.c r)) ==>
                     no_red_red a (fuse_model a l r)) /\
                   almost_no_red_red a (fuse_model a l r))
          (decreases (node_count a l + node_count a r))
  = match l, r with
    | Leaf, _ | _, Leaf -> ()
    | Node Red a_ x b, Node Red c y d ->
      fuse_props_poly a b c;
      (match fuse_model a b c with | Node Red _ _ _ -> () | _ -> ())
    | Node Black a_ x b, Node Black c y d ->
      fuse_props_poly a b c;
      (match fuse_model a b c with
       | Node Red _ _ _ -> ()
       | _ -> balL_props_poly a a_ x (Node Black (fuse_model a b c) y d))
    | Node Red a_ x b, _ -> fuse_props_poly a b r
    | _, Node Red c y d -> fuse_props_poly a l c
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 15"
let rec del_props_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires same_bh a t /\ no_red_red a t)
          (ensures same_bh a (del_model a ord t k) /\
                   (Leaf? t ==> del_model a ord t k == Leaf) /\
                   (Node? t /\ Black? (Node?.c t) ==>
                     bh a (del_model a ord t k) = bh a t - 1 /\
                     almost_no_red_red a (del_model a ord t k)) /\
                   (Node? t /\ Red? (Node?.c t) ==>
                     bh a (del_model a ord t k) = bh a t /\
                     no_red_red a (del_model a ord t k)))
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        match l with
        | Node Black _ _ _ ->
          del_props_poly a ord l k;
          if c = Red then balL_strong_poly a (del_model a ord l k) v r
          else balL_props_poly a (del_model a ord l k) v r
        | _ ->
          (match l with
           | Leaf -> ()
           | Node Red _ _ _ -> del_props_poly a ord l k)
      end else if gt cmp then begin
        match r with
        | Node Black _ _ _ ->
          del_props_poly a ord r k;
          if c = Red then balR_strong_poly a l v (del_model a ord r k)
          else balR_props_poly a l v (del_model a ord r k)
        | _ ->
          (match r with
           | Leaf -> ()
           | Node Red _ _ _ -> del_props_poly a ord r k)
      end else fuse_props_poly a l r
#pop-options

let delete_is_rbtree_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires is_rbtree a t) (ensures is_rbtree a (delete_model a ord t k))
  = del_props_poly a ord t k

// ===== Delete BST Preservation =====

#push-options "--fuel 4 --ifuel 2 --z3rlimit 15"
let balL_all_lt_poly (a:Type0) (ord:erased (TO.total_order a)) (l:rbtree a) (v:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord l bound /\ all_lt a ord r bound /\ lt_ord a ord v bound)
          (ensures all_lt a ord (balL a l v r) bound)
  = match l, r with
    | _, Node Black b y c -> balance_all_lt_poly a ord Black l v (Node Red b y c) bound
    | _, Node Red (Node Black b y c) z d -> balance_all_lt_poly a ord Black c z (redden a d) bound
    | _ -> ()

let balL_all_gt_poly (a:Type0) (ord:erased (TO.total_order a)) (l:rbtree a) (v:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord l bound /\ all_gt a ord r bound /\ gt_ord a ord v bound)
          (ensures all_gt a ord (balL a l v r) bound)
  = match l, r with
    | _, Node Black b y c -> balance_all_gt_poly a ord Black l v (Node Red b y c) bound
    | _, Node Red (Node Black b y c) z d -> balance_all_gt_poly a ord Black c z (redden a d) bound
    | _ -> ()

let balR_all_lt_poly (a:Type0) (ord:erased (TO.total_order a)) (l:rbtree a) (v:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord l bound /\ all_lt a ord r bound /\ lt_ord a ord v bound)
          (ensures all_lt a ord (balR a l v r) bound)
  = match l, r with
    | Node Black a_ x b, _ -> balance_all_lt_poly a ord Black (Node Red a_ x b) v r bound
    | Node Red a_ x (Node Black b y c), _ -> balance_all_lt_poly a ord Black (redden a a_) x b bound
    | _ -> ()

let balR_all_gt_poly (a:Type0) (ord:erased (TO.total_order a)) (l:rbtree a) (v:a) (r:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord l bound /\ all_gt a ord r bound /\ gt_ord a ord v bound)
          (ensures all_gt a ord (balR a l v r) bound)
  = match l, r with
    | Node Black a_ x b, _ -> balance_all_gt_poly a ord Black (Node Red a_ x b) v r bound
    | Node Red a_ x (Node Black b y c), _ -> balance_all_gt_poly a ord Black (redden a a_) x b bound
    | _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 15"
let rec fuse_all_lt_poly (a:Type0) (ord:erased (TO.total_order a)) (l r:rbtree a) (bound:a)
  : Lemma (requires all_lt a ord l bound /\ all_lt a ord r bound)
          (ensures all_lt a ord (fuse_model a l r) bound)
          (decreases (node_count a l + node_count a r))
  = match l, r with
    | Leaf, _ | _, Leaf -> ()
    | Node Red a_ x b, Node Red c y d ->
      fuse_all_lt_poly a ord b c bound;
      (match fuse_model a b c with | Node Red _ _ _ -> () | _ -> ())
    | Node Black a_ x b, Node Black c y d ->
      fuse_all_lt_poly a ord b c bound;
      (match fuse_model a b c with
       | Node Red _ _ _ -> ()
       | _ -> balL_all_lt_poly a ord a_ x (Node Black (fuse_model a b c) y d) bound)
    | Node Red a_ x b, _ -> fuse_all_lt_poly a ord b r bound
    | _, Node Red c y d -> fuse_all_lt_poly a ord l c bound

let rec fuse_all_gt_poly (a:Type0) (ord:erased (TO.total_order a)) (l r:rbtree a) (bound:a)
  : Lemma (requires all_gt a ord l bound /\ all_gt a ord r bound)
          (ensures all_gt a ord (fuse_model a l r) bound)
          (decreases (node_count a l + node_count a r))
  = match l, r with
    | Leaf, _ | _, Leaf -> ()
    | Node Red a_ x b, Node Red c y d ->
      fuse_all_gt_poly a ord b c bound;
      (match fuse_model a b c with | Node Red _ _ _ -> () | _ -> ())
    | Node Black a_ x b, Node Black c y d ->
      fuse_all_gt_poly a ord b c bound;
      (match fuse_model a b c with
       | Node Red _ _ _ -> ()
       | _ -> balL_all_gt_poly a ord a_ x (Node Black (fuse_model a b c) y d) bound)
    | Node Red a_ x b, _ -> fuse_all_gt_poly a ord b r bound
    | _, Node Red c y d -> fuse_all_gt_poly a ord l c bound
#pop-options

#push-options "--fuel 5 --ifuel 3 --z3rlimit 20"
let balL_is_bst_poly (a:Type0) (ord:erased (TO.total_order a)) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires is_bst a ord l /\ is_bst a ord r /\ all_lt a ord l v /\ all_gt a ord r v)
          (ensures is_bst a ord (balL a l v r))
  = reveal_ord a ord;
    match l, r with
    | _, Node Black b y c -> balance_is_bst_poly a ord Black l v (Node Red b y c)
    | _, Node Red (Node Black b y c) z d ->
      all_lt_weaken_poly a ord l v y;
      all_gt_weaken_poly a ord d z y;
      balance_is_bst_poly a ord Black c z (redden a d);
      balance_all_gt_poly a ord Black c z (redden a d) y
    | _ -> ()

let balR_is_bst_poly (a:Type0) (ord:erased (TO.total_order a)) (l:rbtree a) (v:a) (r:rbtree a)
  : Lemma (requires is_bst a ord l /\ is_bst a ord r /\ all_lt a ord l v /\ all_gt a ord r v)
          (ensures is_bst a ord (balR a l v r))
  = reveal_ord a ord;
    match l, r with
    | Node Black a_ x b, _ -> balance_is_bst_poly a ord Black (Node Red a_ x b) v r
    | Node Red a_ x (Node Black b y c), _ ->
      all_gt_weaken_poly a ord r v y;
      all_lt_weaken_poly a ord a_ x y;
      balance_is_bst_poly a ord Black (redden a a_) x b;
      balance_all_lt_poly a ord Black (redden a a_) x b y
    | _ -> ()
#pop-options

#push-options "--fuel 5 --ifuel 3 --z3rlimit 20"
let rec fuse_is_bst_poly (a:Type0) (ord:erased (TO.total_order a)) (l r:rbtree a) (sep:a)
  : Lemma (requires is_bst a ord l /\ is_bst a ord r /\ all_lt a ord l sep /\ all_gt a ord r sep)
          (ensures is_bst a ord (fuse_model a l r))
          (decreases (node_count a l + node_count a r))
  = reveal_ord a ord;
    match l, r with
    | Leaf, _ | _, Leaf -> ()
    | Node Red a_ x b, Node Red c y d ->
      all_gt_weaken_poly a ord c sep x;
      all_lt_weaken_poly a ord b sep y;
      fuse_is_bst_poly a ord b c sep;
      fuse_all_gt_poly a ord b c x;
      fuse_all_lt_poly a ord b c y;
      (match fuse_model a b c with
       | Node Red b' z c' ->
         all_lt_weaken_poly a ord a_ x z;
         all_gt_weaken_poly a ord d y z
       | _ -> all_gt_weaken_poly a ord d y x)
    | Node Black a_ x b, Node Black c y d ->
      all_gt_weaken_poly a ord c sep x;
      all_lt_weaken_poly a ord b sep y;
      fuse_is_bst_poly a ord b c sep;
      fuse_all_gt_poly a ord b c x;
      fuse_all_lt_poly a ord b c y;
      (match fuse_model a b c with
       | Node Red b' z c' ->
         all_lt_weaken_poly a ord a_ x z;
         all_gt_weaken_poly a ord d y z
       | _ ->
         all_gt_weaken_poly a ord d y x;
         balL_is_bst_poly a ord a_ x (Node Black (fuse_model a b c) y d))
    | Node Red a_ x b, _ ->
      all_gt_weaken_poly a ord r sep x;
      fuse_is_bst_poly a ord b r sep;
      fuse_all_gt_poly a ord b r x
    | _, Node Red c y d ->
      all_lt_weaken_poly a ord l sep y;
      fuse_is_bst_poly a ord l c sep;
      fuse_all_lt_poly a ord l c y
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 15"
let rec del_all_lt_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a) (bound:a)
  : Lemma (requires is_bst a ord t /\ all_lt a ord t bound)
          (ensures all_lt a ord (del_model a ord t k) bound)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r ->
      reveal_ord a ord;
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        del_all_lt_poly a ord l k bound;
        (match l with
         | Node Black _ _ _ -> balL_all_lt_poly a ord (del_model a ord l k) v r bound
         | _ -> ())
      end else if gt cmp then begin
        del_all_lt_poly a ord r k bound;
        (match r with
         | Node Black _ _ _ -> balR_all_lt_poly a ord l v (del_model a ord r k) bound
         | _ -> ())
      end else fuse_all_lt_poly a ord l r bound

let rec del_all_gt_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a) (bound:a)
  : Lemma (requires is_bst a ord t /\ all_gt a ord t bound)
          (ensures all_gt a ord (del_model a ord t k) bound)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r ->
      reveal_ord a ord;
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        del_all_gt_poly a ord l k bound;
        (match l with
         | Node Black _ _ _ -> balL_all_gt_poly a ord (del_model a ord l k) v r bound
         | _ -> ())
      end else if gt cmp then begin
        del_all_gt_poly a ord r k bound;
        (match r with
         | Node Black _ _ _ -> balR_all_gt_poly a ord l v (del_model a ord r k) bound
         | _ -> ())
      end else fuse_all_gt_poly a ord l r bound
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let rec del_preserves_bst_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires is_bst a ord t) (ensures is_bst a ord (del_model a ord t k))
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r ->
      reveal_ord a ord;
      let cmp = k `ord.TO.compare` v in
      if lt cmp then begin
        del_preserves_bst_poly a ord l k;
        del_all_lt_poly a ord l k v;
        (match l with
         | Node Black _ _ _ -> balL_is_bst_poly a ord (del_model a ord l k) v r
         | _ -> ())
      end else if gt cmp then begin
        del_preserves_bst_poly a ord r k;
        del_all_gt_poly a ord r k v;
        (match r with
         | Node Black _ _ _ -> balR_is_bst_poly a ord l v (del_model a ord r k)
         | _ -> ())
      end else fuse_is_bst_poly a ord l r v
#pop-options

let delete_preserves_bst_poly (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires is_bst a ord t) (ensures is_bst a ord (delete_model a ord t k))
  = del_preserves_bst_poly a ord t k

let delete_model_valid (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (k:a)
  : Lemma (requires valid a ord t) (ensures valid a ord (delete_model a ord t k))
  = delete_is_rbtree_poly a ord t k; delete_preserves_bst_poly a ord t k

// ===== SC Tick Bound Lemmas =====

let rec search_ticks_le_height (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (ensures search_ticks a ord t key <= height a t) (decreases t)
  = match t with | Leaf -> () | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then search_ticks_le_height a ord l key
      else if gt cmp then search_ticks_le_height a ord r key
      else ()

let rec ins_ticks_le_height (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (ensures ins_ticks a ord t key <= height a t) (decreases t)
  = match t with | Leaf -> () | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then ins_ticks_le_height a ord l key
      else if gt cmp then ins_ticks_le_height a ord r key
      else ()

let rec del_ticks_le_height (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (ensures del_ticks a ord t key <= height a t) (decreases t)
  = match t with | Leaf -> () | Node _ l k r ->
      let cmp = key `ord.TO.compare` k in
      if lt cmp then del_ticks_le_height a ord l key
      else if gt cmp then del_ticks_le_height a ord r key
      else ()

let search_ticks_bounded_sc (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (requires valid a ord t)
          (ensures search_ticks a ord t key <= SC.rb_search_bound (height a t) (node_count a t))
  = search_ticks_le_height a ord t key;
    if node_count a t = 0 then ()
    else height_bound_poly a t

let insert_ticks_bounded_sc (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (requires valid a ord t)
          (ensures insert_ticks a ord t key <= SC.rb_insert_bound (height a t) (node_count a t))
  = ins_ticks_le_height a ord t key;
    if node_count a t = 0 then ()
    else height_bound_poly a t

let delete_ticks_bounded_sc (a:Type0) (ord:erased (TO.total_order a)) (t:rbtree a) (key:a)
  : Lemma (requires valid a ord t)
          (ensures delete_ticks a ord t key <= SC.rb_delete_bound (height a t) (node_count a t))
  = del_ticks_le_height a ord t key;
    if node_count a t = 0 then ()
    else height_bound_poly a t

let rec rb_subtree (a:Type0) (ct:rb_ptr a) (ft:rbtree a)
  : Tot slprop (decreases ft)
  =
  match ft with
  | Leaf -> pure (ct == None #(rb_node_ptr a))
  | Node c l k r ->
      exists* (bp:rb_node_ptr a) (node:rb_node a).
        pure (ct == Some bp) **
        (bp |-> node) **
        pure (node.key == k /\ node.color == c) **
        rb_subtree a node.left l **
        rb_subtree a node.right r

let owns (a:Type0) (tree:rb_ptr a) (model:rbtree a) : slprop =
  rb_subtree a tree model

ghost fn elim_rb_leaf (a:Type0) (x:rb_ptr a)
  requires rb_subtree a x Leaf
  ensures pure (x == None #(rb_node_ptr a))
{
  unfold (rb_subtree a x Leaf)
}

ghost fn intro_rb_leaf (a:Type0) (x:rb_ptr a)
  requires pure (x == None #(rb_node_ptr a))
  ensures rb_subtree a x Leaf
{
  fold (rb_subtree a x Leaf)
}

ghost fn intro_rb_node (a:Type0) (ct:rb_ptr a) (bp:rb_node_ptr a)
  (#node:rb_node a) (#lt #rt:rbtree a)
  requires
    (bp |-> node) **
    rb_subtree a node.left lt **
    rb_subtree a node.right rt **
    pure (ct == Some bp)
  ensures rb_subtree a ct (Node node.color lt node.key rt)
{
  fold (rb_subtree a ct (Node node.color lt node.key rt))
}

[@@no_mkeys]
let rb_cases (a:Type0) (x:rb_ptr a) (ft:rbtree a) =
  match x with
  | None -> pure (ft == Leaf)
  | Some bp ->
      exists* (node:rb_node a) (lt rt:rbtree a).
        (bp |-> node) **
        pure (ft == Node node.color lt node.key rt) **
        rb_subtree a node.left lt **
        rb_subtree a node.right rt

ghost fn cases_of_rb (a:Type0) (x:rb_ptr a) (ft:rbtree a)
  requires rb_subtree a x ft
  ensures rb_cases a x ft
{
  match ft {
    Leaf -> {
      unfold (rb_subtree a x Leaf);
      fold (rb_cases a (None #(rb_node_ptr a)) ft);
      rewrite rb_cases a (None #(rb_node_ptr a)) ft as rb_cases a x ft;
    }
    Node c l k r -> {
      unfold (rb_subtree a x (Node c l k r));
      with bp node. _;
      fold (rb_cases a (Some bp) ft);
      rewrite rb_cases a (Some bp) ft as rb_cases a x ft;
    }
  }
}

ghost fn rb_case_none (a:Type0) (x:rb_ptr a) (#ft:rbtree a)
  preserves rb_subtree a x ft
  requires pure (x == None #(rb_node_ptr a))
  ensures pure (ft == Leaf)
{
  rewrite each x as (None #(rb_node_ptr a));
  cases_of_rb a (None #(rb_node_ptr a)) ft;
  unfold (rb_cases a);
  intro_rb_leaf a (None #(rb_node_ptr a));
  rewrite rb_subtree a (None #(rb_node_ptr a)) Leaf as rb_subtree a x ft
}

ghost fn rb_case_some (a:Type0) (x:rb_ptr a) (bp:rb_node_ptr a)
  (#ft:rbtree a)
  requires rb_subtree a x ft ** pure (x == Some bp)
  ensures exists* (node:rb_node a) (lt rt:rbtree a).
    (bp |-> node) **
    rb_subtree a node.left lt **
    rb_subtree a node.right rt **
    pure (ft == Node node.color lt node.key rt)
{
  rewrite each x as (Some bp);
  cases_of_rb a (Some bp) ft;
  unfold (rb_cases a)
}

ghost fn rb_subtree_some_is_node (a:Type0) (x:rb_ptr a) (bp:rb_node_ptr a)
  (#ft:rbtree a)
  preserves rb_subtree a x ft
  requires pure (x == Some bp)
  ensures pure (Node? ft)
{
  rb_case_some a x bp;
  intro_rb_node a x bp;
  with t. rewrite rb_subtree a x t as rb_subtree a x ft
}

ghost fn rb_not_leaf (a:Type0) (x:rb_ptr a) (#ft:rbtree a)
  preserves rb_subtree a x ft
  requires pure (Node? ft)
  ensures pure (Some? x)
{
  let Node c lt v rt = ft;
  unfold (rb_subtree a x (Node c lt v rt));
  with bp node. _;
  fold (rb_subtree a x (Node c lt v rt));
  rewrite rb_subtree a x (Node c lt v rt) as rb_subtree a x ft
}

fn rec tree_search (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  preserves rb_subtree a tree 'ft
  requires MR.pts_to ctr #1.0R 'n
  returns result:option a
  ensures exists* ticks.
    MR.pts_to ctr #1.0R ticks **
    pure (result == find_model a ord 'ft key /\
          ticks == reveal 'n + search_ticks a ord 'ft key)
{
  match tree {
    None -> {
      rb_case_none a (None #(rb_node_ptr a));
      rewrite rb_subtree a (None #(rb_node_ptr a)) 'ft as rb_subtree a tree 'ft;
      None
    }
    Some bp -> {
      rb_case_some a (Some bp) bp;
      let node = !bp;
      let cmp = iord key node.key;
      if (lt cmp) {
        let result = tree_search a node.left key ctr #ord iord;
        intro_rb_node a (Some bp) bp;
        with t. rewrite rb_subtree a (Some bp) t as rb_subtree a tree 'ft;
        result
      } else if (gt cmp) {
        let result = tree_search a node.right key ctr #ord iord;
        intro_rb_node a (Some bp) bp;
        with t. rewrite rb_subtree a (Some bp) t as rb_subtree a tree 'ft;
        result
      } else {
        intro_rb_node a (Some bp) bp;
        with t. rewrite rb_subtree a (Some bp) t as rb_subtree a tree 'ft;
        Some node.key
      }
    }
  }
}

fn new_node (a:Type0) (key:a) (c:color) (l:rb_ptr a) (r:rb_ptr a)
  (#lt #rt:erased (rbtree a))
  requires rb_subtree a l lt ** rb_subtree a r rt
  returns y:rb_ptr a
  ensures rb_subtree a y (Node c lt key rt) ** pure (Some? y)
{
  let bp = Box.alloc ({ key = key; color = c; left = l; right = r } <: rb_node a);
  intro_rb_node a (Some bp) bp;
  Some bp
}

fn check_right_balance (a:Type0) (r:rb_ptr a)
  (#rt:erased (rbtree a))
  preserves rb_subtree a r rt
  returns bc:balance_case
  ensures pure (bc == (match rt with
    | Node Red (Node Red _ _ _) _ _ -> BC_RL
    | Node Red _ _ (Node Red _ _ _) -> BC_RR
    | _ -> BC_None))
{
  match r {
    None -> {
      rb_case_none a (None #(rb_node_ptr a));
      rewrite rb_subtree a (None #(rb_node_ptr a)) rt as rb_subtree a r rt;
      BC_None
    }
    Some rp -> {
      rewrite each (Some rp) as r;
      rb_case_some a r rp;
      let rn = !rp;
      if (Red? rn.color) {
        match rn.left {
          None -> {
            rb_case_none a rn.left;
            match rn.right {
              None -> {
                rb_case_none a rn.right;
                intro_rb_node a r rp;
                with t. rewrite rb_subtree a r t as rb_subtree a r rt;
                BC_None
              }
              Some rrp -> {
                rb_case_some a rn.right rrp;
                let rrn = !rrp;
                let res = (if (Red? rrn.color) then BC_RR else BC_None);
                intro_rb_node a rn.right rrp;
                intro_rb_node a r rp;
                with t. rewrite rb_subtree a r t as rb_subtree a r rt;
                res
              }
            }
          }
          Some rlp -> {
            rb_case_some a rn.left rlp;
            let rln = !rlp;
            if (Red? rln.color) {
              intro_rb_node a rn.left rlp;
              intro_rb_node a r rp;
              with t. rewrite rb_subtree a r t as rb_subtree a r rt;
              BC_RL
            } else {
              intro_rb_node a rn.left rlp;
              match rn.right {
                None -> {
                  rb_case_none a rn.right;
                  intro_rb_node a r rp;
                  with t. rewrite rb_subtree a r t as rb_subtree a r rt;
                  BC_None
                }
                Some rrp -> {
                  rb_case_some a rn.right rrp;
                  let rrn = !rrp;
                  let res = (if (Red? rrn.color) then BC_RR else BC_None);
                  intro_rb_node a rn.right rrp;
                  intro_rb_node a r rp;
                  with t. rewrite rb_subtree a r t as rb_subtree a r rt;
                  res
                }
              }
            }
          }
        }
      } else {
        intro_rb_node a r rp;
        with t. rewrite rb_subtree a r t as rb_subtree a r rt;
        BC_None
      }
    }
  }
}

fn classify_runtime (a:Type0) (c:color) (l:rb_ptr a) (r:rb_ptr a)
  (#lt #rt:erased (rbtree a))
  preserves rb_subtree a l lt ** rb_subtree a r rt
  returns bc:balance_case
  ensures pure (bc == classify_balance a c lt rt)
{
  if (Red? c) {
    BC_None
  } else {
    match l {
      None -> {
        rb_case_none a (None #(rb_node_ptr a));
        rewrite rb_subtree a (None #(rb_node_ptr a)) lt as rb_subtree a l lt;
        check_right_balance a r
      }
      Some lp -> {
        rewrite each (Some lp) as l;
        rb_case_some a l lp;
        let ln = !lp;
        if (Red? ln.color) {
          match ln.left {
            None -> {
              rb_case_none a ln.left;
              match ln.right {
                None -> {
                  rb_case_none a ln.right;
                  intro_rb_node a l lp;
                  with t. rewrite rb_subtree a l t as rb_subtree a l lt;
                  check_right_balance a r
                }
                Some lrp -> {
                  rb_case_some a ln.right lrp;
                  let lrn = !lrp;
                  if (Red? lrn.color) {
                    intro_rb_node a ln.right lrp;
                    intro_rb_node a l lp;
                    with t. rewrite rb_subtree a l t as rb_subtree a l lt;
                    BC_LR
                  } else {
                    intro_rb_node a ln.right lrp;
                    intro_rb_node a l lp;
                    with t. rewrite rb_subtree a l t as rb_subtree a l lt;
                    check_right_balance a r
                  }
                }
              }
            }
            Some llp -> {
              rb_case_some a ln.left llp;
              let lln = !llp;
              if (Red? lln.color) {
                intro_rb_node a ln.left llp;
                intro_rb_node a l lp;
                with t. rewrite rb_subtree a l t as rb_subtree a l lt;
                BC_LL
              } else {
                intro_rb_node a ln.left llp;
                match ln.right {
                  None -> {
                    rb_case_none a ln.right;
                    intro_rb_node a l lp;
                    with t. rewrite rb_subtree a l t as rb_subtree a l lt;
                    check_right_balance a r
                  }
                  Some lrp -> {
                    rb_case_some a ln.right lrp;
                    let lrn = !lrp;
                    if (Red? lrn.color) {
                      intro_rb_node a ln.right lrp;
                      intro_rb_node a l lp;
                      with t. rewrite rb_subtree a l t as rb_subtree a l lt;
                      BC_LR
                    } else {
                      intro_rb_node a ln.right lrp;
                      intro_rb_node a l lp;
                      with t. rewrite rb_subtree a l t as rb_subtree a l lt;
                      check_right_balance a r
                    }
                  }
                }
              }
            }
          }
        } else {
          intro_rb_node a l lp;
          with t. rewrite rb_subtree a l t as rb_subtree a l lt;
          check_right_balance a r
        }
      }
    }
  }
}

fn balance_ll (a:Type0) (l:rb_ptr a) (v:a) (r:rb_ptr a)
  (#lt #rt:erased (rbtree a))
  requires rb_subtree a l lt ** rb_subtree a r rt **
           pure (BC_LL? (classify_balance a Black lt rt))
  returns y:rb_ptr a
  ensures rb_subtree a y (balance a Black lt v rt)
{
  classify_balance_lemma a Black lt v rt;
  rb_not_leaf a l;
  let lp = Some?.v l;
  rb_case_some a l lp;
  let ln = !lp;
  rb_not_leaf a ln.left;
  let llp = Some?.v ln.left;
  rb_case_some a ln.left llp;
  let lln = !llp;
  llp := { key = lln.key; color = Black; left = lln.left; right = lln.right };
  intro_rb_node a ln.left llp;
  let right_black = new_node a v Black ln.right r;
  lp := { key = ln.key; color = Red; left = ln.left; right = right_black };
  intro_rb_node a l lp;
  with t. rewrite rb_subtree a l t as rb_subtree a l (balance a Black lt v rt);
  l
}

fn balance_lr (a:Type0) (l:rb_ptr a) (v:a) (r:rb_ptr a)
  (#lt #rt:erased (rbtree a))
  requires rb_subtree a l lt ** rb_subtree a r rt **
           pure (BC_LR? (classify_balance a Black lt rt))
  returns y:rb_ptr a
  ensures rb_subtree a y (balance a Black lt v rt)
{
  classify_balance_lemma a Black lt v rt;
  rb_not_leaf a l;
  let lp = Some?.v l;
  rb_case_some a l lp;
  let ln = !lp;
  rb_not_leaf a ln.right;
  let lrp = Some?.v ln.right;
  rb_case_some a ln.right lrp;
  let lrn = !lrp;
  lp := { key = ln.key; color = Black; left = ln.left; right = lrn.left };
  intro_rb_node a l lp;
  let right_black = new_node a v Black lrn.right r;
  lrp := { key = lrn.key; color = Red; left = l; right = right_black };
  intro_rb_node a (Some lrp) lrp;
  with t. rewrite rb_subtree a (Some lrp) t as rb_subtree a (Some lrp) (balance a Black lt v rt);
  Some lrp
}

fn balance_rl (a:Type0) (l:rb_ptr a) (v:a) (r:rb_ptr a)
  (#lt #rt:erased (rbtree a))
  requires rb_subtree a l lt ** rb_subtree a r rt **
           pure (BC_RL? (classify_balance a Black lt rt))
  returns y:rb_ptr a
  ensures rb_subtree a y (balance a Black lt v rt)
{
  classify_balance_lemma a Black lt v rt;
  rb_not_leaf a r;
  let rp = Some?.v r;
  rb_case_some a r rp;
  let rn = !rp;
  rb_not_leaf a rn.left;
  let rlp = Some?.v rn.left;
  rb_case_some a rn.left rlp;
  let rln = !rlp;
  let left_black = new_node a v Black l rln.left;
  rp := { key = rn.key; color = Black; left = rln.right; right = rn.right };
  intro_rb_node a r rp;
  rlp := { key = rln.key; color = Red; left = left_black; right = r };
  intro_rb_node a (Some rlp) rlp;
  with t. rewrite rb_subtree a (Some rlp) t as rb_subtree a (Some rlp) (balance a Black lt v rt);
  Some rlp
}

fn balance_rr (a:Type0) (l:rb_ptr a) (v:a) (r:rb_ptr a)
  (#lt #rt:erased (rbtree a))
  requires rb_subtree a l lt ** rb_subtree a r rt **
           pure (BC_RR? (classify_balance a Black lt rt))
  returns y:rb_ptr a
  ensures rb_subtree a y (balance a Black lt v rt)
{
  classify_balance_lemma a Black lt v rt;
  rb_not_leaf a r;
  let rp = Some?.v r;
  rb_case_some a r rp;
  let rn = !rp;
  rb_not_leaf a rn.right;
  let rrp = Some?.v rn.right;
  rb_case_some a rn.right rrp;
  let rrn = !rrp;
  let left_black = new_node a v Black l rn.left;
  rrp := { key = rrn.key; color = Black; left = rrn.left; right = rrn.right };
  intro_rb_node a rn.right rrp;
  rp := { key = rn.key; color = Red; left = left_black; right = rn.right };
  intro_rb_node a r rp;
  with t. rewrite rb_subtree a r t as rb_subtree a r (balance a Black lt v rt);
  r
}

fn rb_balance (a:Type0) (c:color) (l:rb_ptr a) (v:a) (r:rb_ptr a)
  (#lt #rt:erased (rbtree a))
  requires rb_subtree a l lt ** rb_subtree a r rt
  returns y:rb_ptr a
  ensures rb_subtree a y (balance a c lt v rt)
{
  let bc = classify_runtime a c l r;
  match bc {
    BC_LL -> {
      let y = balance_ll a l v r;
      rewrite rb_subtree a y (balance a Black lt v rt) as rb_subtree a y (balance a c lt v rt);
      y
    }
    BC_LR -> {
      let y = balance_lr a l v r;
      rewrite rb_subtree a y (balance a Black lt v rt) as rb_subtree a y (balance a c lt v rt);
      y
    }
    BC_RL -> {
      let y = balance_rl a l v r;
      rewrite rb_subtree a y (balance a Black lt v rt) as rb_subtree a y (balance a c lt v rt);
      y
    }
    BC_RR -> {
      let y = balance_rr a l v r;
      rewrite rb_subtree a y (balance a Black lt v rt) as rb_subtree a y (balance a c lt v rt);
      y
    }
    BC_None -> {
      classify_balance_lemma a c lt v rt;
      let y = new_node a v c l r;
      with t. rewrite rb_subtree a y t as rb_subtree a y (balance a c lt v rt);
      y
    }
  }
}

fn rec tree_ins (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  requires rb_subtree a tree 'ft ** MR.pts_to ctr #1.0R 'n
  returns y:rb_ptr a
  ensures exists* ticks.
    rb_subtree a y (ins_model a ord 'ft key) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks == reveal 'n + ins_ticks a ord 'ft key)
{
  match tree {
    None -> {
      rb_case_none a (None #(rb_node_ptr a));
      rewrite rb_subtree a (None #(rb_node_ptr a)) 'ft
        as rb_subtree a (None #(rb_node_ptr a)) Leaf;
      elim_rb_leaf a (None #(rb_node_ptr a));
      let left_nil : rb_ptr a = None #(rb_node_ptr a);
      let right_nil : rb_ptr a = None #(rb_node_ptr a);
      intro_rb_leaf a left_nil;
      intro_rb_leaf a right_nil;
      let y = new_node a key Red left_nil right_nil;
      with t. rewrite rb_subtree a y t as rb_subtree a y (ins_model a ord 'ft key);
      y
    }
    Some bp -> {
      rb_case_some a (Some bp) bp;
      let node = !bp;
      let cmp = iord key node.key;
      if (lt cmp) {
        let new_left = tree_ins a node.left key ctr #ord iord;
        Box.free bp;
        let y = rb_balance a node.color new_left node.key node.right;
        with t. rewrite rb_subtree a y t
          as rb_subtree a y (ins_model a ord 'ft key);
        y
      } else if (gt cmp) {
        let new_right = tree_ins a node.right key ctr #ord iord;
        Box.free bp;
        let y = rb_balance a node.color node.left node.key new_right;
        with t. rewrite rb_subtree a y t
          as rb_subtree a y (ins_model a ord 'ft key);
        y
      } else {
        intro_rb_node a (Some bp) bp;
        with t. rewrite rb_subtree a (Some bp) t
          as rb_subtree a tree (ins_model a ord 'ft key);
        tree
      }
    }
  }
}

fn rb_make_black (a:Type0) (tree:rb_ptr a)
  requires rb_subtree a tree 'ft
  returns y:rb_ptr a
  ensures rb_subtree a y (make_black a 'ft)
{
  match tree {
    None -> {
      rb_case_none a (None #(rb_node_ptr a));
      rewrite rb_subtree a (None #(rb_node_ptr a)) 'ft as rb_subtree a tree (make_black a 'ft);
      tree
    }
    Some bp -> {
      rb_case_some a (Some bp) bp;
      let node = !bp;
      bp := { node with color = Black };
      intro_rb_node a (Some bp) bp;
      with t. rewrite rb_subtree a (Some bp) t as rb_subtree a tree (make_black a 'ft);
      tree
    }
  }
}

fn tree_insert (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  requires rb_subtree a tree 'ft ** MR.pts_to ctr #1.0R 'n
  returns y:rb_ptr a
  ensures exists* ticks.
    rb_subtree a y (insert_model a ord 'ft key) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks == reveal 'n + insert_ticks a ord 'ft key)
{
  let t = tree_ins a tree key ctr #ord iord;
  rb_make_black a t
}

ghost fn consume_rb_leaf (a:Type0) (x:rb_ptr a) (#ft:rbtree a)
  requires rb_subtree a x ft ** pure (x == None #(rb_node_ptr a))
  ensures pure (ft == Leaf)
{
  rewrite each x as (None #(rb_node_ptr a));
  cases_of_rb a (None #(rb_node_ptr a)) ft;
  unfold (rb_cases a)
}

fn rb_redden (a:Type0) (tree:rb_ptr a)
  requires rb_subtree a tree 'ft
  returns y:rb_ptr a
  ensures rb_subtree a y (redden a 'ft)
{
  match tree {
    None -> {
      rb_case_none a (None #(rb_node_ptr a));
      rewrite rb_subtree a (None #(rb_node_ptr a)) 'ft as rb_subtree a tree (redden a 'ft);
      tree
    }
    Some bp -> {
      rb_case_some a (Some bp) bp;
      let node = !bp;
      if (Black? node.color) {
        bp := { node with color = Red };
        intro_rb_node a (Some bp) bp;
        with t. rewrite rb_subtree a (Some bp) t as rb_subtree a tree (redden a 'ft);
        tree
      } else {
        bp := node;
        intro_rb_node a (Some bp) bp;
        with t. rewrite rb_subtree a (Some bp) t as rb_subtree a tree (redden a 'ft);
        tree
      }
    }
  }
}

fn is_color (a:Type0) (tree:rb_ptr a) (c:color)
  (#ft:erased (rbtree a))
  preserves rb_subtree a tree ft
  returns b:bool
  ensures pure (b == (Node? ft && Node?.c ft = c))
{
  match tree {
    None -> {
      rb_case_none a (None #(rb_node_ptr a));
      rewrite rb_subtree a (None #(rb_node_ptr a)) ft as rb_subtree a tree ft;
      false
    }
    Some bp -> {
      rewrite each (Some bp) as tree;
      rb_case_some a tree bp;
      let node = !bp;
      let res = (node.color = c);
      bp := node;
      intro_rb_node a tree bp;
      with t. rewrite rb_subtree a tree t as rb_subtree a tree ft;
      res
    }
  }
}

fn rb_balL (a:Type0) (l:rb_ptr a) (v:a) (r:rb_ptr a)
  (#lt #rt:erased (rbtree a))
  requires rb_subtree a l lt ** rb_subtree a r rt
  returns y:rb_ptr a
  ensures rb_subtree a y (balL a lt v rt)
{
  let l_red = is_color a l Red;
  if l_red {
    rb_not_leaf a l;
    let lp = Some?.v l;
    rb_case_some a l lp;
    let ln = !lp;
    lp := { key = ln.key; color = Black; left = ln.left; right = ln.right };
    intro_rb_node a l lp;
    let y = new_node a v Red l r;
    with t. rewrite rb_subtree a y t as rb_subtree a y (balL a lt v rt);
    y
  } else {
    let r_black = is_color a r Black;
    if r_black {
      rb_not_leaf a r;
      let rp = Some?.v r;
      rb_case_some a r rp;
      let rn = !rp;
      rp := { key = rn.key; color = Red; left = rn.left; right = rn.right };
      intro_rb_node a r rp;
      let y = rb_balance a Black l v r;
      with t. rewrite rb_subtree a y t as rb_subtree a y (balL a lt v rt);
      y
    } else {
      let r_red = is_color a r Red;
      if r_red {
        rb_not_leaf a r;
        let rp = Some?.v r;
        rb_case_some a r rp;
        let rn = !rp;
        let rl_black = is_color a rn.left Black;
        if rl_black {
          rb_not_leaf a rn.left;
          let rlp = Some?.v rn.left;
          rb_case_some a rn.left rlp;
          let rln = !rlp;
          let rd = rb_redden a rn.right;
          let right_balanced = rb_balance a Black rln.right rn.key rd;
          let left_black = new_node a v Black l rln.left;
          Box.free rp;
          rlp := { key = rln.key; color = Red; left = left_black; right = right_balanced };
          intro_rb_node a (Some rlp) rlp;
          with t. rewrite rb_subtree a (Some rlp) t as rb_subtree a (Some rlp) (balL a lt v rt);
          Some rlp
        } else {
          rp := rn;
          intro_rb_node a r rp;
          with t. rewrite rb_subtree a r t as rb_subtree a r rt;
          let y = new_node a v Black l r;
          with t. rewrite rb_subtree a y t as rb_subtree a y (balL a lt v rt);
          y
        }
      } else {
        let y = new_node a v Black l r;
        with t. rewrite rb_subtree a y t as rb_subtree a y (balL a lt v rt);
        y
      }
    }
  }
}

fn rb_balR (a:Type0) (l:rb_ptr a) (v:a) (r:rb_ptr a)
  (#lt #rt:erased (rbtree a))
  requires rb_subtree a l lt ** rb_subtree a r rt
  returns y:rb_ptr a
  ensures rb_subtree a y (balR a lt v rt)
{
  let r_red = is_color a r Red;
  if r_red {
    rb_not_leaf a r;
    let rp = Some?.v r;
    rb_case_some a r rp;
    let rn = !rp;
    rp := { key = rn.key; color = Black; left = rn.left; right = rn.right };
    intro_rb_node a r rp;
    let y = new_node a v Red l r;
    with t. rewrite rb_subtree a y t as rb_subtree a y (balR a lt v rt);
    y
  } else {
    let l_black = is_color a l Black;
    if l_black {
      rb_not_leaf a l;
      let lp = Some?.v l;
      rb_case_some a l lp;
      let ln = !lp;
      lp := { key = ln.key; color = Red; left = ln.left; right = ln.right };
      intro_rb_node a l lp;
      let y = rb_balance a Black l v r;
      with t. rewrite rb_subtree a y t as rb_subtree a y (balR a lt v rt);
      y
    } else {
      let l_red = is_color a l Red;
      if l_red {
        rb_not_leaf a l;
        let lp = Some?.v l;
        rb_case_some a l lp;
        let ln = !lp;
        let lr_black = is_color a ln.right Black;
        if lr_black {
          rb_not_leaf a ln.right;
          let lrp = Some?.v ln.right;
          rb_case_some a ln.right lrp;
          let lrn = !lrp;
          let la = rb_redden a ln.left;
          let left_balanced = rb_balance a Black la ln.key lrn.left;
          let right_black = new_node a v Black lrn.right r;
          Box.free lp;
          lrp := { key = lrn.key; color = Red; left = left_balanced; right = right_black };
          intro_rb_node a (Some lrp) lrp;
          with t. rewrite rb_subtree a (Some lrp) t as rb_subtree a (Some lrp) (balR a lt v rt);
          Some lrp
        } else {
          lp := ln;
          intro_rb_node a l lp;
          with t. rewrite rb_subtree a l t as rb_subtree a l lt;
          let y = new_node a v Black l r;
          with t. rewrite rb_subtree a y t as rb_subtree a y (balR a lt v rt);
          y
        }
      } else {
        let y = new_node a v Black l r;
        with t. rewrite rb_subtree a y t as rb_subtree a y (balR a lt v rt);
        y
      }
    }
  }
}

fn rec rb_fuse (a:Type0) (l:rb_ptr a) (r:rb_ptr a)
  (#lt #rt:erased (rbtree a))
  requires rb_subtree a l lt ** rb_subtree a r rt
  returns y:rb_ptr a
  ensures rb_subtree a y (fuse_model a lt rt)
  decreases (node_count a lt + node_count a rt)
{
  match l {
    None -> {
      cases_of_rb a (None #(rb_node_ptr a)) lt;
      unfold (rb_cases a);
      with t. rewrite rb_subtree a r t as rb_subtree a r (fuse_model a lt rt);
      r
    }
    Some lp -> {
      match r {
        None -> {
          cases_of_rb a (None #(rb_node_ptr a)) rt;
          unfold (rb_cases a);
          rewrite each (Some lp) as l;
          with t. rewrite rb_subtree a l t as rb_subtree a l (fuse_model a lt rt);
          l
        }
        Some rp -> {
          rewrite each (Some lp) as l;
          rewrite each (Some rp) as r;
          rb_case_some a l lp;
          rb_case_some a r rp;
          let ln = !lp;
          let rn = !rp;
          if (Red? ln.color && Red? rn.color) {
            let s = rb_fuse a ln.right rn.left;
            let s_red = is_color a s Red;
            if s_red {
              rb_not_leaf a s;
              let sp = Some?.v s;
              rb_case_some a s sp;
              let sn = !sp;
              lp := { key = ln.key; color = Red; left = ln.left; right = sn.left };
              intro_rb_node a l lp;
              rp := { key = rn.key; color = Red; left = sn.right; right = rn.right };
              intro_rb_node a r rp;
              sp := { key = sn.key; color = Red; left = l; right = r };
              intro_rb_node a s sp;
              with t. rewrite rb_subtree a s t as rb_subtree a s (fuse_model a lt rt);
              s
            } else {
              rp := { key = rn.key; color = Red; left = s; right = rn.right };
              intro_rb_node a r rp;
              lp := { key = ln.key; color = Red; left = ln.left; right = r };
              intro_rb_node a l lp;
              with t. rewrite rb_subtree a l t as rb_subtree a l (fuse_model a lt rt);
              l
            }
          } else if (Black? ln.color && Black? rn.color) {
            let s = rb_fuse a ln.right rn.left;
            let s_red = is_color a s Red;
            if s_red {
              rb_not_leaf a s;
              let sp = Some?.v s;
              rb_case_some a s sp;
              let sn = !sp;
              lp := { key = ln.key; color = Black; left = ln.left; right = sn.left };
              intro_rb_node a l lp;
              rp := { key = rn.key; color = Black; left = sn.right; right = rn.right };
              intro_rb_node a r rp;
              sp := { key = sn.key; color = Red; left = l; right = r };
              intro_rb_node a s sp;
              with t. rewrite rb_subtree a s t as rb_subtree a s (fuse_model a lt rt);
              s
            } else {
              rp := { key = rn.key; color = Black; left = s; right = rn.right };
              intro_rb_node a r rp;
              Box.free lp;
              let y = rb_balL a ln.left ln.key r;
              with t. rewrite rb_subtree a y t as rb_subtree a y (fuse_model a lt rt);
              y
            }
          } else if (Red? ln.color) {
            rp := rn;
            intro_rb_node a r rp;
            with t. rewrite rb_subtree a r t as rb_subtree a r rt;
            let fused = rb_fuse a ln.right r;
            lp := { key = ln.key; color = Red; left = ln.left; right = fused };
            intro_rb_node a l lp;
            with t. rewrite rb_subtree a l t as rb_subtree a l (fuse_model a lt rt);
            l
          } else {
            lp := ln;
            intro_rb_node a l lp;
            with t. rewrite rb_subtree a l t as rb_subtree a l lt;
            let fused = rb_fuse a l rn.left;
            rp := { key = rn.key; color = Red; left = fused; right = rn.right };
            intro_rb_node a r rp;
            with t. rewrite rb_subtree a r t as rb_subtree a r (fuse_model a lt rt);
            r
          }
        }
      }
    }
  }
}

fn rec tree_minimum (a:Type0) (tree:rb_ptr a) (bp:rb_node_ptr a)
  preserves rb_subtree a tree 'ft
  requires pure (tree == Some bp)
  returns result:a
  ensures pure (minimum_model a 'ft == Some result)
{
  rewrite each tree as (Some bp);
  rb_case_some a (Some bp) bp;
  let node = !bp;
  match node.left {
    None -> {
      rb_case_none a node.left;
      intro_rb_node a (Some bp) bp;
      with t. rewrite rb_subtree a (Some bp) t as rb_subtree a tree 'ft;
      node.key
    }
    Some lbp -> {
      let result = tree_minimum a node.left lbp;
      intro_rb_node a (Some bp) bp;
      with t. rewrite rb_subtree a (Some bp) t as rb_subtree a tree 'ft;
      result
    }
  }
}

fn rec tree_del (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  requires rb_subtree a tree 'ft ** MR.pts_to ctr #1.0R 'n
  returns y:rb_ptr a
  ensures exists* ticks.
    rb_subtree a y (del_model a ord 'ft key) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks == reveal 'n + del_ticks a ord 'ft key)
  decreases 'ft
{
  match tree {
    None -> {
      rb_case_none a (None #(rb_node_ptr a));
      rewrite rb_subtree a (None #(rb_node_ptr a)) 'ft
        as rb_subtree a (None #(rb_node_ptr a)) Leaf;
      rewrite rb_subtree a (None #(rb_node_ptr a)) Leaf
        as rb_subtree a (None #(rb_node_ptr a)) (del_model a ord 'ft key);
      None #(rb_node_ptr a)
    }
    Some bp -> {
      rb_case_some a (Some bp) bp;
      let node = !bp;
      let cmp = iord key node.key;
      if (lt cmp) {
        let l_was_black = is_color a node.left Black;
        let new_left = tree_del a node.left key ctr #ord iord;
        if l_was_black {
          Box.free bp;
          let y = rb_balL a new_left node.key node.right;
          with t. rewrite rb_subtree a y t as rb_subtree a y (del_model a ord 'ft key);
          y
        } else {
          Box.free bp;
          let y = new_node a node.key Red new_left node.right;
          with t. rewrite rb_subtree a y t as rb_subtree a y (del_model a ord 'ft key);
          y
        }
      } else if (gt cmp) {
        let r_was_black = is_color a node.right Black;
        let new_right = tree_del a node.right key ctr #ord iord;
        if r_was_black {
          Box.free bp;
          let y = rb_balR a node.left node.key new_right;
          with t. rewrite rb_subtree a y t as rb_subtree a y (del_model a ord 'ft key);
          y
        } else {
          Box.free bp;
          let y = new_node a node.key Red node.left new_right;
          with t. rewrite rb_subtree a y t as rb_subtree a y (del_model a ord 'ft key);
          y
        }
      } else {
        Box.free bp;
        let y = rb_fuse a node.left node.right;
        with t. rewrite rb_subtree a y t as rb_subtree a y (del_model a ord 'ft key);
        y
      }
    }
  }
}

fn tree_delete (a:Type0)
  (tree:rb_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  requires rb_subtree a tree 'ft ** MR.pts_to ctr #1.0R 'n
  returns y:rb_ptr a
  ensures exists* ticks.
    rb_subtree a y (delete_model a ord 'ft key) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks == reveal 'n + delete_ticks a ord 'ft key)
{
  let t = tree_del a tree key ctr #ord iord;
  rb_make_black a t
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
          ticks <= reveal i + SC.rb_search_bound (height a m) (node_count a m))
{
  unfold (owns a tree m);
  let result = tree_search a tree key ctr #ord iord;
  with ticks. assert (MR.pts_to ctr #1.0R ticks);
  search_ticks_bounded_sc a ord m key;
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
    owns a tree' (insert_model a ord m key) **
    MR.pts_to ctr #1.0R ticks **
    pure (valid a ord (insert_model a ord m key) /\
          ticks <= reveal i + SC.rb_insert_bound (height a m) (node_count a m))
{
  unfold (owns a tree m);
  let tree' = tree_insert a tree key ctr #ord iord;
  with ticks. assert (MR.pts_to ctr #1.0R ticks);
  insert_ticks_bounded_sc a ord m key;
  insert_model_valid a ord m key;
  fold (owns a tree' (insert_model a ord m key));
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
    owns a tree' (delete_model a ord m key) **
    MR.pts_to ctr #1.0R ticks **
    pure (valid a ord (delete_model a ord m key) /\
          ticks <= reveal i + SC.rb_delete_bound (height a m) (node_count a m))
{
  unfold (owns a tree m);
  let tree' = tree_delete a tree key ctr #ord iord;
  with ticks. assert (MR.pts_to ctr #1.0R ticks);
  delete_ticks_bounded_sc a ord m key;
  delete_model_valid a ord m key;
  fold (owns a tree' (delete_model a ord m key));
  tree'
}

instance rb_search_structure_instance :
  SC.search_structure
    rb_ptr
    rbtree
    owns
    valid
    find_model
    insert_model
    delete_model
    height
    node_count
    SC.rb_search_bound
    SC.rb_insert_bound
    SC.rb_delete_bound
= {
  search = search;
  insert = insert;
  delete = delete;
}
