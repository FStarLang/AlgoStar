module CLRS.Common.Complexity.Search.Class
open Pulse
#lang-pulse

module MR = Pulse.Lib.MonotonicGhostRef
module TO = Pulse.Lib.TotalOrder
open FStar.Order

(*
  Complexity-aware ordered search structures.

  Like CLRS.Common.Complexity.Sorting.Class.array_sort, the operations
  themselves quantify over the key type `a`.  A client receives only an
  instrumented total order on that abstract key type, so every comparison used
  by search/insert/delete must go through `iord` and is reflected in `ticks_t`.

  The abstract `repr`/`model` split lets a family describe either a pointer
  implementation or a pure model.  The ch12 BST and ch13 RB tree rubric modules
  instantiate these type constructors with polymorphic tree models.
*)

let preorder_nat : FStar.Preorder.preorder nat = (fun (x y:nat) -> b2t (x <= y))

let ticks_t = MR.mref #nat preorder_nat

let instrumented_total_order (a:Type) (ord:TO.total_order a) (ctr:ticks_t) =
  fn (x y:a) (#i:erased nat)
  requires MR.pts_to ctr #1.0R i
  returns o:order
  ensures MR.pts_to ctr #1.0R (i + 1)
  ensures pure (o == x `ord.TO.compare` y)

let rec log2_floor (n:pos) : Tot nat (decreases n) =
  if n = 1 then 0 else 1 + log2_floor (n / 2)

let bst_search_bound (h:nat) (_n:nat) : nat = h

let bst_insert_bound (h:nat) (_n:nat) : nat = h

let bst_delete_bound (h:nat) (_n:nat) : nat = 4 * h + 1

let rb_search_bound (_h:nat) (n:nat) : nat =
  if n = 0 then 1 else 2 * log2_floor (n + 1) + 1

let rb_insert_bound (_h:nat) (n:nat) : nat =
  if n = 0 then 2 else 2 * log2_floor (n + 1) + 2

let rb_delete_bound (_h:nat) (n:nat) : nat =
  if n = 0 then 2 else 4 * log2_floor (n + 1) + 2

let same_key (a:Type0) (ord:erased (TO.total_order a)) (x y:a) : GTot bool =
  eq (x `ord.TO.compare` y)

class search_model_laws
  (model: Type0 -> Type0)
  (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
  (empty_model: (a:Type0) -> GTot (model a))
  (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
  (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
  (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
= {
  find_empty:
    ((a:Type0) ->
     (ord:erased (TO.total_order a)) ->
     (key:a) ->
       Lemma
         (ensures find_model a ord (empty_model a) key == None));

  find_insert_hit:
    ((a:Type0) ->
     (ord:erased (TO.total_order a)) ->
     (m:model a) ->
     (key:a) ->
       Lemma
         (requires valid a ord m)
         (ensures find_model a ord (insert_model a ord m key) key == Some key));

  find_insert_other:
    ((a:Type0) ->
     (ord:erased (TO.total_order a)) ->
     (m:model a) ->
     (inserted:a) ->
     (key:a) ->
       Lemma
         (requires valid a ord m /\ same_key a ord key inserted = false)
         (ensures find_model a ord (insert_model a ord m inserted) key ==
                  find_model a ord m key));

  find_delete_hit:
    ((a:Type0) ->
     (ord:erased (TO.total_order a)) ->
     (m:model a) ->
     (key:a) ->
       Lemma
         (requires valid a ord m)
         (ensures find_model a ord (delete_model a ord m key) key == None));

  find_delete_other:
    ((a:Type0) ->
     (ord:erased (TO.total_order a)) ->
     (m:model a) ->
     (deleted:a) ->
     (key:a) ->
       Lemma
         (requires valid a ord m /\ same_key a ord key deleted = false)
         (ensures find_model a ord (delete_model a ord m deleted) key ==
                  find_model a ord m key));
}

class search_structure
  (repr: Type0 -> Type0)
  (model: Type0 -> Type0)
  (owns: (a:Type0) -> repr a -> model a -> slprop)
  (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
  (empty_model: (a:Type0) -> GTot (model a))
  (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
  (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
  (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
  (height: (a:Type0) -> model a -> nat)
  (size: (a:Type0) -> model a -> nat)
  (search_bound insert_bound delete_bound: nat -> nat -> nat)
= {
  create:
    (fn (a:Type0)
        (#ord:erased (TO.total_order a))
      requires emp
      returns tree:repr a
      ensures owns a tree (empty_model a) ** pure (valid a ord (empty_model a)));

  dispose:
    (fn (a:Type0)
        (tree:repr a)
        (#m:erased (model a))
      requires owns a tree m
      ensures emp);

  search:
    (fn (a:Type0)
        (tree:repr a)
        (key:a)
        (ctr:ticks_t)
        (#ord:erased (TO.total_order a))
        (iord:instrumented_total_order a ord ctr)
        (#m:erased (model a))
        (#i:erased nat)
      preserves owns a tree m
      requires MR.pts_to ctr #1.0R i ** pure (valid a ord m)
      returns result:option a
      ensures exists* ticks.
        MR.pts_to ctr #1.0R ticks **
        pure (
          result == find_model a ord m key /\
          ticks <= i + search_bound (height a m) (size a m)));

  insert:
    (fn (a:Type0)
        (tree:repr a)
        (key:a)
        (ctr:ticks_t)
        (#ord:erased (TO.total_order a))
        (iord:instrumented_total_order a ord ctr)
        (#m:erased (model a))
        (#i:erased nat)
      requires owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m)
      returns tree':repr a
      ensures exists* ticks.
        owns a tree' (insert_model a ord m key) **
        MR.pts_to ctr #1.0R ticks **
        pure (
          valid a ord (insert_model a ord m key) /\
          ticks <= i + insert_bound (height a m) (size a m)));

  delete:
    (fn (a:Type0)
        (tree:repr a)
        (key:a)
        (ctr:ticks_t)
        (#ord:erased (TO.total_order a))
        (iord:instrumented_total_order a ord ctr)
        (#m:erased (model a))
        (#i:erased nat)
      requires owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m)
      returns tree':repr a
      ensures exists* ticks.
        owns a tree' (delete_model a ord m key) **
        MR.pts_to ctr #1.0R ticks **
        pure (
          valid a ord (delete_model a ord m key) /\
          ticks <= i + delete_bound (height a m) (size a m)));
}
