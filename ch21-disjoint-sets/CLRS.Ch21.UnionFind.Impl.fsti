(*
   Public Interface: Union-Find Imperative Implementation (CLRS §21.3)

   Exposes the three core operations:
   - make_set: Initialize an n-element forest
   - find_set: FIND-SET with full path compression (two-pass)
   - union: UNION by rank

   All postconditions reference the pure specification in Spec.fst
   via the bridge function `to_uf`.
*)

module CLRS.Ch21.UnionFind.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = CLRS.Ch21.UnionFind.Spec

// ========== Bridge: imperative arrays <-> pure spec ==========

let to_nat_seq (s: Seq.seq SZ.t) (n: nat) : Seq.seq nat =
  Seq.init n (fun (i: nat{i < n}) ->
    if i < Seq.length s then (SZ.v (Seq.index s i) <: nat) else (0 <: nat))

let to_uf (parent rank: Seq.seq SZ.t) (n: nat) : Spec.uf_forest =
  { Spec.parent = to_nat_seq parent n;
    Spec.rank = to_nat_seq rank n;
    Spec.n = n }

// ========== Imperative forest invariants ==========

val well_formed (parent: Seq.seq SZ.t) (n: nat) : prop

val is_root_at (parent: Seq.seq SZ.t) (i: nat) : prop

val is_forest (parent: Seq.seq SZ.t) (n: nat) : prop

(** MAKE-SET: Initialize parent[i]=i, rank[i]=0 for i ∈ [0,n) *)
fn make_set
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      SZ.v n > 0 /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank
    )
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      is_forest sp (SZ.v n) /\
      Spec.uf_inv (to_uf sp sr (SZ.v n)) /\
      (forall (idx: nat). idx < SZ.v n ==> is_root_at sp idx) /\
      (forall (idx: nat). idx < SZ.v n /\ idx < Seq.length sr ==> SZ.v (Seq.index sr idx) == 0)
    )

(** FIND-SET: Two-pass path compression (CLRS §21.3)
    Pass 1: find root (read-only). Pass 2: compress path. *)
fn find_set
  (parent: A.array SZ.t) (x: SZ.t) (n: SZ.t)
  (#sparent: erased (Seq.seq SZ.t))
  (#srank: erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sparent **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v n <= Seq.length sparent /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n))
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
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      Spec.uf_inv (to_uf sp srank (SZ.v n)) /\
      SZ.v root == Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v x) /\
      (forall (z: nat). z < SZ.v n ==>
        Spec.pure_find (to_uf sp srank (SZ.v n)) z ==
        Spec.pure_find (to_uf sparent srank (SZ.v n)) z)
    )

(** UNION: Union by rank (CLRS §21.3)
    After union, find(x) == find(y) in the resulting forest. *)
fn union
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
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
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      (forall (i: nat). i < SZ.v n ==> SZ.v (Seq.index srank i) < SZ.v n)
    )
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      is_forest sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      Spec.uf_inv (to_uf sp sr (SZ.v n)) /\
      SZ.v x < SZ.v n /\ SZ.v y < SZ.v n /\
      Spec.pure_find (to_uf sp sr (SZ.v n)) (SZ.v x) ==
        Spec.pure_find (to_uf sp sr (SZ.v n)) (SZ.v y)
    )
