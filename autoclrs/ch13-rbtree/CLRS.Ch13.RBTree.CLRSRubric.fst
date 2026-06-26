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

let left_rotate (a:Type0) (t:rbtree a) : rbtree a =
  match t with
  | Node c a_ x (Node rc b y d) -> Node rc (Node c a_ x b) y d
  | _ -> t

let right_rotate (a:Type0) (t:rbtree a) : rbtree a =
  match t with
  | Node c (Node lc a_ x b) y d -> Node lc a_ x (Node c b y d)
  | _ -> t

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

let valid (a:Type0) (_ord:erased (TO.total_order a)) (_t:rbtree a) : GTot prop = True

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
  fold (owns a tree' (clrs_delete_model a ord m key));
  tree'
}

instance clrs_parent_pointer_search_structure_instance :
  SC.search_structure
    rb_ptr
    rbtree
    owns
    valid
    find_model
    clrs_insert_model
    clrs_delete_model
    height
    node_count
    search_bound
    insert_bound
    delete_bound
= {
  search = search;
  insert = insert;
  delete = delete;
}
