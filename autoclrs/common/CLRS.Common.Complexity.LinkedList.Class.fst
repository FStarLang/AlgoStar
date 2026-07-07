module CLRS.Common.Complexity.LinkedList.Class
#lang-pulse

open Pulse

module BC = CLRS.Common.Complexity.Box.Class
module L = FStar.List.Tot
module MR = Pulse.Lib.MonotonicGhostRef

let snoc (#a:Type) (l:list a) (x:a) : list a = L.append l [x]

let rec mem_by (#a:Type0) (same:a -> a -> Tot bool) (x:a) (l:list a)
  : Tot bool (decreases l)
  = match l with
    | [] -> false
    | hd :: tl -> if same x hd then true else mem_by same x tl

let rec remove_first_by (#a:Type0) (same:a -> a -> Tot bool) (x:a) (l:list a)
  : Tot (list a) (decreases l)
  = match l with
    | [] -> []
    | hd :: tl -> if same x hd then tl else hd :: remove_first_by same x tl

let rec remove_last_by (#a:Type0) (same:a -> a -> Tot bool) (x:a) (l:list a)
  : Tot (list a) (decreases l)
  = match l with
    | [] -> []
    | hd :: tl ->
      if mem_by same x tl then hd :: remove_last_by same x tl
      else if same x hd then tl
      else hd :: tl

let constant_bound (c:nat) (_n:nat) : nat = c
let linear_bound (per_node base:nat) (n:nat) : nat = per_node * n + base

class linked_list_structure
  (ctr:BC.ticks_t)
  (box:([@@@strictly_positive] _:Type0 -> Type0))
  {| boxes:BC.box_class ctr box |}
  (a:Type0)
  (repr:Type0)
  (owns: repr -> list a -> slprop)
  (insert_head_bound append_tail_bound search_bound delete_first_bound delete_last_bound: nat -> nat)
= {
  insert_head:
    (fn (xs:repr)
        (x:a)
        (#l:erased (list a))
        (#i:erased nat)
      requires owns xs l ** MR.pts_to ctr #1.0R i
      returns xs':repr
      ensures exists* ticks.
        owns xs' (x :: l) **
        MR.pts_to ctr #1.0R ticks **
        pure (ticks <= i + insert_head_bound (L.length l)));

  append_tail:
    (fn (xs:repr)
        (x:a)
        (#l:erased (list a))
        (#i:erased nat)
      requires owns xs l ** MR.pts_to ctr #1.0R i
      returns xs':repr
      ensures exists* ticks.
        owns xs' (snoc l x) **
        MR.pts_to ctr #1.0R ticks **
        pure (ticks <= i + append_tail_bound (L.length l)));

  search:
    (fn (xs:repr)
        (same:a -> a -> Tot bool)
        (x:a)
        (#l:erased (list a))
        (#i:erased nat)
      requires owns xs l ** MR.pts_to ctr #1.0R i
      returns found:bool
      ensures exists* ticks.
        owns xs l **
        MR.pts_to ctr #1.0R ticks **
        pure (found <==> mem_by same x l /\ ticks <= i + search_bound (L.length l)));

  delete_first:
    (fn (xs:repr)
        (same:a -> a -> Tot bool)
        (x:a)
        (#l:erased (list a))
        (#i:erased nat)
      requires owns xs l ** MR.pts_to ctr #1.0R i
      returns xs':repr
      ensures exists* ticks.
        owns xs' (remove_first_by same x l) **
        MR.pts_to ctr #1.0R ticks **
        pure (ticks <= i + delete_first_bound (L.length l)));

  delete_last:
    (fn (xs:repr)
        (same:a -> a -> Tot bool)
        (x:a)
        (#l:erased (list a))
        (#i:erased nat)
      requires owns xs l ** MR.pts_to ctr #1.0R i
      returns xs':repr
      ensures exists* ticks.
        owns xs' (remove_last_by same x l) **
        MR.pts_to ctr #1.0R ticks **
        pure (ticks <= i + delete_last_bound (L.length l)))
}
