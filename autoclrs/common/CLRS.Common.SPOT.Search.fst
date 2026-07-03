module CLRS.Common.SPOT.Search
open Pulse
#lang-pulse

module SC = CLRS.Common.Complexity.Search.Class
module MR = Pulse.Lib.MonotonicGhostRef
module TO = Pulse.Lib.TotalOrder

open FStar.Order

(*
  SPOT: small proof-oriented test.

  This module contains tiny clients of Search.Class.  It does not instantiate a
  concrete tree.  The first group quantifies over search_model_laws and checks
  that the exposed laws are strong enough for client-side reasoning about empty,
  insert, delete, and small compositions.  The final Pulse SPOT quantifies over
  search_structure and search_model_laws and checks that a client can allocate
  a structure, mutate it, search the final model, prove the expected membership
  facts, and dispose it without depending on any concrete instance.
*)

let spot_empty_lookup
    (model: Type0 -> Type0)
    (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (empty_model: (a:Type0) -> GTot (model a))
    (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#laws: SC.search_model_laws model valid empty_model find_model insert_model delete_model)
    (a:Type0) (ord:erased (TO.total_order a)) (key:a)
  : Lemma (ensures find_model a ord (empty_model a) key == None)
  =
  laws.find_empty a ord key

let spot_insert_finds_inserted
    (model: Type0 -> Type0)
    (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (empty_model: (a:Type0) -> GTot (model a))
    (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#laws: SC.search_model_laws model valid empty_model find_model insert_model delete_model)
    (a:Type0) (ord:erased (TO.total_order a)) (m:model a) (key:a)
  : Lemma
      (requires valid a ord m)
      (ensures find_model a ord (insert_model a ord m key) key == Some key)
  =
  laws.find_insert_hit a ord m key

let spot_insert_preserves_other
    (model: Type0 -> Type0)
    (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (empty_model: (a:Type0) -> GTot (model a))
    (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#laws: SC.search_model_laws model valid empty_model find_model insert_model delete_model)
    (a:Type0) (ord:erased (TO.total_order a)) (m:model a) (inserted key:a)
  : Lemma
      (requires valid a ord m /\ SC.same_key a ord key inserted = false)
      (ensures find_model a ord (insert_model a ord m inserted) key == find_model a ord m key)
  =
  laws.find_insert_other a ord m inserted key

let spot_delete_removes_deleted
    (model: Type0 -> Type0)
    (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (empty_model: (a:Type0) -> GTot (model a))
    (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#laws: SC.search_model_laws model valid empty_model find_model insert_model delete_model)
    (a:Type0) (ord:erased (TO.total_order a)) (m:model a) (key:a)
  : Lemma
      (requires valid a ord m)
      (ensures find_model a ord (delete_model a ord m key) key == None)
  =
  laws.find_delete_hit a ord m key

let spot_delete_preserves_other
    (model: Type0 -> Type0)
    (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (empty_model: (a:Type0) -> GTot (model a))
    (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#laws: SC.search_model_laws model valid empty_model find_model insert_model delete_model)
    (a:Type0) (ord:erased (TO.total_order a)) (m:model a) (deleted key:a)
  : Lemma
      (requires valid a ord m /\ SC.same_key a ord key deleted = false)
      (ensures find_model a ord (delete_model a ord m deleted) key == find_model a ord m key)
  =
  laws.find_delete_other a ord m deleted key

let spot_insert_insert_delete_keeps_other
    (model: Type0 -> Type0)
    (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (empty_model: (a:Type0) -> GTot (model a))
    (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#laws: SC.search_model_laws model valid empty_model find_model insert_model delete_model)
    (a:Type0) (ord:erased (TO.total_order a)) (m:model a) (x y:a)
  : Lemma
      (requires valid a ord m /\
                valid a ord (insert_model a ord m x) /\
                valid a ord (insert_model a ord (insert_model a ord m x) y) /\
                SC.same_key a ord y x = false)
      (ensures find_model a ord
                 (delete_model a ord (insert_model a ord (insert_model a ord m x) y) x)
                 y == Some y)
  =
  laws.find_insert_other a ord (insert_model a ord m x) y x;
  laws.find_insert_hit a ord (insert_model a ord m x) y;
  laws.find_delete_other a ord (insert_model a ord (insert_model a ord m x) y) x y

let spot_structure_final_model
    (model: Type0 -> Type0)
    (empty_model: (a:Type0) -> GTot (model a))
    (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (a:Type0)
    (ord:erased (TO.total_order a))
    (x y z:a)
  : GTot (model a)
  =
  let m0 = empty_model a in
  let m1 = insert_model a ord m0 x in
  let m2 = insert_model a ord m1 y in
  let m3 = insert_model a ord m2 z in
  delete_model a ord m3 z

let spot_structure_final_model_expected
    (model: Type0 -> Type0)
    (valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (empty_model: (a:Type0) -> GTot (model a))
    (find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#laws: SC.search_model_laws model valid empty_model find_model insert_model delete_model)
    (a:Type0)
    (ord:erased (TO.total_order a))
    (x y z:a)
  : Lemma
      (requires
        valid a ord (empty_model a) /\
        valid a ord (insert_model a ord (empty_model a) x) /\
        valid a ord (insert_model a ord (insert_model a ord (empty_model a) x) y) /\
        valid a ord
          (insert_model a ord
            (insert_model a ord (insert_model a ord (empty_model a) x) y)
            z) /\
        SC.same_key a ord x y = false /\
        SC.same_key a ord x z = false /\
        SC.same_key a ord y z = false)
      (ensures
        find_model a ord
          (spot_structure_final_model
            model empty_model insert_model delete_model a ord x y z)
          x == Some x /\
        find_model a ord
          (spot_structure_final_model
            model empty_model insert_model delete_model a ord x y z)
          y == Some y /\
        find_model a ord
          (spot_structure_final_model
            model empty_model insert_model delete_model a ord x y z)
          z == None)
  =
  let m0 = empty_model a in
  let m1 = insert_model a ord m0 x in
  let m2 = insert_model a ord m1 y in
  let m3 = insert_model a ord m2 z in
  let m4 = delete_model a ord m3 z in
  laws.find_insert_hit a ord m0 x;
  laws.find_insert_other a ord m1 y x;
  laws.find_insert_other a ord m2 z x;
  laws.find_delete_other a ord m3 z x;
  assert (find_model a ord m4 x == Some x);
  laws.find_insert_hit a ord m1 y;
  laws.find_insert_other a ord m2 z y;
  laws.find_delete_other a ord m3 z y;
  assert (find_model a ord m4 y == Some y);
  laws.find_delete_hit a ord m3 z;
  assert (find_model a ord m4 z == None)

let ss_create
    (#repr: Type0 -> Type0)
    (#model: Type0 -> Type0)
    (#owns: (a:Type0) -> repr a -> model a -> slprop)
    (#valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (#empty_model: (a:Type0) -> GTot (model a))
    (#find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (#insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#height: (a:Type0) -> model a -> nat)
    (#size: (a:Type0) -> model a -> nat)
    (#search_bound #insert_bound #delete_bound: nat -> nat -> nat)
    (structure:
      SC.search_structure
        repr model owns valid empty_model find_model insert_model delete_model
        height size search_bound insert_bound delete_bound)
    (a:Type0)
    (#ord:erased (TO.total_order a))
  : stt (repr a)
      emp
      (fun tree -> owns a tree (empty_model a) ** pure (valid a ord (empty_model a)))
  =
  structure.create a

let ss_dispose
    (#repr: Type0 -> Type0)
    (#model: Type0 -> Type0)
    (#owns: (a:Type0) -> repr a -> model a -> slprop)
    (#valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (#empty_model: (a:Type0) -> GTot (model a))
    (#find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (#insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#height: (a:Type0) -> model a -> nat)
    (#size: (a:Type0) -> model a -> nat)
    (#search_bound #insert_bound #delete_bound: nat -> nat -> nat)
    (structure:
      SC.search_structure
        repr model owns valid empty_model find_model insert_model delete_model
        height size search_bound insert_bound delete_bound)
    (a:Type0)
    (tree:repr a)
    (#m:erased (model a))
  : stt unit
      (owns a tree m)
      (fun _ -> emp)
  =
  structure.dispose a tree

let ss_search
    (#repr: Type0 -> Type0)
    (#model: Type0 -> Type0)
    (#owns: (a:Type0) -> repr a -> model a -> slprop)
    (#valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (#empty_model: (a:Type0) -> GTot (model a))
    (#find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (#insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#height: (a:Type0) -> model a -> nat)
    (#size: (a:Type0) -> model a -> nat)
    (#search_bound #insert_bound #delete_bound: nat -> nat -> nat)
    (structure:
      SC.search_structure
        repr model owns valid empty_model find_model insert_model delete_model
        height size search_bound insert_bound delete_bound)
    (a:Type0)
    (tree:repr a)
    (key:a)
    (ctr:SC.ticks_t)
    (#ord:erased (TO.total_order a))
    (iord:SC.instrumented_total_order a ord ctr)
    (#m:erased (model a))
    (#i:erased nat)
  : stt (option a)
      (owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m))
      (fun result ->
        owns a tree m **
        exists* ticks.
          MR.pts_to ctr #1.0R ticks **
          pure (
            result == find_model a ord m key /\
            ticks <= i + search_bound (height a m) (size a m)))
  =
  structure.search a tree key ctr iord

let ss_insert
    (#repr: Type0 -> Type0)
    (#model: Type0 -> Type0)
    (#owns: (a:Type0) -> repr a -> model a -> slprop)
    (#valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (#empty_model: (a:Type0) -> GTot (model a))
    (#find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (#insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#height: (a:Type0) -> model a -> nat)
    (#size: (a:Type0) -> model a -> nat)
    (#search_bound #insert_bound #delete_bound: nat -> nat -> nat)
    (structure:
      SC.search_structure
        repr model owns valid empty_model find_model insert_model delete_model
        height size search_bound insert_bound delete_bound)
    (a:Type0)
    (tree:repr a)
    (key:a)
    (ctr:SC.ticks_t)
    (#ord:erased (TO.total_order a))
    (iord:SC.instrumented_total_order a ord ctr)
    (#m:erased (model a))
    (#i:erased nat)
  : stt (repr a)
      (owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m))
      (fun tree' ->
        exists* ticks.
          owns a tree' (insert_model a ord m key) **
          MR.pts_to ctr #1.0R ticks **
          pure (
            valid a ord (insert_model a ord m key) /\
            ticks <= i + insert_bound (height a m) (size a m)))
  =
  structure.insert a tree key ctr iord

let ss_delete
    (#repr: Type0 -> Type0)
    (#model: Type0 -> Type0)
    (#owns: (a:Type0) -> repr a -> model a -> slprop)
    (#valid: (a:Type0) -> erased (TO.total_order a) -> model a -> GTot prop)
    (#empty_model: (a:Type0) -> GTot (model a))
    (#find_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (option a))
    (#insert_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#delete_model: (a:Type0) -> erased (TO.total_order a) -> model a -> a -> GTot (model a))
    (#height: (a:Type0) -> model a -> nat)
    (#size: (a:Type0) -> model a -> nat)
    (#search_bound #insert_bound #delete_bound: nat -> nat -> nat)
    (structure:
      SC.search_structure
        repr model owns valid empty_model find_model insert_model delete_model
        height size search_bound insert_bound delete_bound)
    (a:Type0)
    (tree:repr a)
    (key:a)
    (ctr:SC.ticks_t)
    (#ord:erased (TO.total_order a))
    (iord:SC.instrumented_total_order a ord ctr)
    (#m:erased (model a))
    (#i:erased nat)
  : stt (repr a)
      (owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m))
      (fun tree' ->
        exists* ticks.
          owns a tree' (delete_model a ord m key) **
          MR.pts_to ctr #1.0R ticks **
          pure (
            valid a ord (delete_model a ord m key) /\
            ticks <= i + delete_bound (height a m) (size a m)))
  =
  structure.delete a tree key ctr iord

fn spot_structure_pulse_client
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
    (#structure:
      SC.search_structure
        repr
        model
        owns
        valid
        empty_model
        find_model
        insert_model
        delete_model
        height
        size
        search_bound
        insert_bound
        delete_bound)
    (#laws: SC.search_model_laws model valid empty_model find_model insert_model delete_model)
    (a:Type0)
    (#ord:erased (TO.total_order a))
    (x y z:a)
    (ctr:SC.ticks_t)
    (iord:SC.instrumented_total_order a ord ctr)
    (#i:erased nat)
  requires MR.pts_to ctr #1.0R i
  requires pure (
    SC.same_key a ord x y = false /\
    SC.same_key a ord x z = false /\
    SC.same_key a ord y z = false)
  returns results:(option a & option a & option a)
  ensures exists* ticks.
    MR.pts_to ctr #1.0R ticks **
    pure (results == (Some x, Some y, None))
{
  let tree0 = ss_create structure a #ord;
  let tree1 = ss_insert structure a tree0 x ctr #ord iord;
  with ticks1. assert (MR.pts_to ctr #1.0R ticks1);

  let tree2 = ss_insert structure a tree1 y ctr #ord iord;
  with ticks2. assert (MR.pts_to ctr #1.0R ticks2);

  let tree3 = ss_insert structure a tree2 z ctr #ord iord;
  with ticks3. assert (MR.pts_to ctr #1.0R ticks3);

  let tree4 = ss_delete structure a tree3 z ctr #ord iord;
  with ticks4. assert (MR.pts_to ctr #1.0R ticks4);

  spot_structure_final_model_expected
    model valid empty_model find_model insert_model delete_model #laws a ord x y z;

  let rx = ss_search structure a tree4 x ctr #ord iord;
  with ticks5. assert (MR.pts_to ctr #1.0R ticks5);
  assert (pure (rx == find_model a ord
    (spot_structure_final_model
      model empty_model insert_model delete_model a ord x y z) x));
  assert (pure (rx == Some x));

  let ry = ss_search structure a tree4 y ctr #ord iord;
  with ticks6. assert (MR.pts_to ctr #1.0R ticks6);
  assert (pure (ry == find_model a ord
    (spot_structure_final_model
      model empty_model insert_model delete_model a ord x y z) y));
  assert (pure (ry == Some y));

  let rz = ss_search structure a tree4 z ctr #ord iord;
  with ticks7. assert (MR.pts_to ctr #1.0R ticks7);
  assert (pure (rz == find_model a ord
    (spot_structure_final_model
      model empty_model insert_model delete_model a ord x y z) z));
  assert (pure (rz == None));

  ss_dispose structure a tree4;
  assert (pure ((rx, ry, rz) == (Some x, Some y, None)));
  (rx, ry, rz)
}
