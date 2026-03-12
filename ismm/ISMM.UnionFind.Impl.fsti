(*
   ISMM Union-Find — Imperative Pulse Implementation Interface

   Three arrays: tag, parent, rank
   Operations: make_set, find_set (with path compression), union (by rank)
   
   All postconditions reference ISMM.UnionFind.Spec via bridge `to_uf`.
*)

module ISMM.UnionFind.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = ISMM.UnionFind.Spec

// ========== Bridge: imperative arrays <-> pure spec ==========

let to_nat_seq (s: Seq.seq SZ.t) (n: nat) : Seq.seq nat =
  Seq.init n (fun (i: nat{i < n}) ->
    if i < Seq.length s then (SZ.v (Seq.index s i) <: nat) else (0 <: nat))

let to_int_seq (s: Seq.seq SZ.t) (n: nat) : Seq.seq int =
  Seq.init n (fun (i: nat{i < n}) ->
    if i < Seq.length s then (SZ.v (Seq.index s i) <: int) else (0 <: int))

let to_uf (stag sparent srank: Seq.seq SZ.t) (n: nat) : Spec.uf_state =
  { Spec.n = n;
    Spec.tag = to_int_seq stag n;
    Spec.parent = to_nat_seq sparent n;
    Spec.rank = to_nat_seq srank n }

// ========== Imperative forest invariants ==========

val to_nat_seq_index (s: Seq.seq SZ.t) (n: nat) (i: nat{i < n /\ i < Seq.length s})
  : Lemma (Seq.index (to_nat_seq s n) i == SZ.v (Seq.index s i))

val to_int_seq_index (s: Seq.seq SZ.t) (n: nat) (i: nat{i < n /\ i < Seq.length s})
  : Lemma (Seq.index (to_int_seq s n) i == SZ.v (Seq.index s i))

val well_formed (parent: Seq.seq SZ.t) (n: nat) : prop

val is_root_at (parent: Seq.seq SZ.t) (i: nat) : prop

val is_forest (parent: Seq.seq SZ.t) (n: nat) : prop

(** MAKE-SET: Initialize parent[i]=i, rank[i]=0, tag[i]=0 for i ∈ [0,n) *)
fn make_set
  (tag: array SZ.t)
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      SZ.v n > 0 /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank
    )
  ensures exists* st sp sr.
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      Seq.length st == Seq.length stag /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      is_forest sp (SZ.v n) /\
      Spec.uf_inv (to_uf st sp sr (SZ.v n)) /\
      (forall (idx: nat). idx < SZ.v n ==> is_root_at sp idx) /\
      (forall (idx: nat). idx < SZ.v n /\ idx < Seq.length sr ==> SZ.v (Seq.index sr idx) == 0) /\
      (forall (idx: nat). idx < SZ.v n /\ idx < Seq.length st ==> SZ.v (Seq.index st idx) == 0)
    )

(** FIND-SET: Two-pass path compression.
    Pass 1: find root (read-only). Pass 2: compress path.
    Only modifies the parent array. *)
fn find_set
  (parent: A.array SZ.t) (x: SZ.t) (n: SZ.t)
  (#sparent: erased (Seq.seq SZ.t))
  (#stag: erased (Seq.seq SZ.t))
  (#srank: erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sparent **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v n <= Seq.length sparent /\
      Spec.uf_inv (to_uf stag sparent srank (SZ.v n))
    )
  returns root: SZ.t
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      SZ.v root < SZ.v n /\
      SZ.v x < SZ.v n /\
      Seq.length sp == Seq.length sparent /\
      SZ.v n <= Seq.length sp /\
      is_forest sp (SZ.v n) /\
      SZ.v (Seq.index sp (SZ.v x)) == SZ.v root /\
      SZ.v (Seq.index sp (SZ.v root)) == SZ.v root /\
      Spec.uf_inv (to_uf stag sparent srank (SZ.v n)) /\
      Spec.uf_inv (to_uf stag sp srank (SZ.v n)) /\
      SZ.v root == Spec.pure_find (to_uf stag sparent srank (SZ.v n)) (SZ.v x) /\
      (forall (z: nat). z < SZ.v n ==>
        Spec.pure_find (to_uf stag sp srank (SZ.v n)) z ==
        Spec.pure_find (to_uf stag sparent srank (SZ.v n)) z)
    )

(** UNION: Union by rank.
    Modifies parent and rank arrays. Does NOT modify tag array.
    After union, find(x) == find(y), and disjoint elements unchanged. *)
fn union_set
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (x: SZ.t)
  (y: SZ.t)
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v y < SZ.v n /\
      Seq.length srank == Seq.length sparent /\
      SZ.v n <= Seq.length sparent /\
      Spec.uf_inv (to_uf stag sparent srank (SZ.v n)) /\
      (forall (i: nat). i < SZ.v n ==> SZ.v (Seq.index srank i) < SZ.v n)
    )
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      is_forest sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      SZ.v n <= Seq.length sp /\
      Spec.uf_inv (to_uf stag sparent srank (SZ.v n)) /\
      Spec.uf_inv (to_uf stag sp sr (SZ.v n)) /\
      SZ.v x < SZ.v n /\ SZ.v y < SZ.v n /\
      Spec.pure_find (to_uf stag sp sr (SZ.v n)) (SZ.v x) ==
        Spec.pure_find (to_uf stag sp sr (SZ.v n)) (SZ.v y) /\
      (forall (z: nat). z < SZ.v n ==>
        Spec.pure_find (to_uf stag sparent srank (SZ.v n)) z <>
          Spec.pure_find (to_uf stag sparent srank (SZ.v n)) (SZ.v x) ==>
        Spec.pure_find (to_uf stag sparent srank (SZ.v n)) z <>
          Spec.pure_find (to_uf stag sparent srank (SZ.v n)) (SZ.v y) ==>
        Spec.pure_find (to_uf stag sp sr (SZ.v n)) z ==
          Spec.pure_find (to_uf stag sparent srank (SZ.v n)) z)
    )
