(*
   ISMM RefCount — Interface
   
   Pulse interface for acquire/release operations (paper §3.2).
*)
module ISMM.RefCount.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = ISMM.UnionFind.Spec
module Impl = ISMM.UnionFind.Impl
open ISMM.Status

(** ACQUIRE: Increment the reference count of the SCC containing r.
    Calls find(r) to get representative, then increments refcount[rep]. *)
fn acquire
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (refcount: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (r: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to refcount src **
    pure (
      SZ.v n > 0 /\
      SZ.v r < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      SZ.v n <= A.length refcount /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length src == A.length refcount /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
    )
  ensures exists* sp sr src'.
    A.pts_to tag stag **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to refcount src' **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp sr (SZ.v n))
    )

(** RELEASE: Decrement the RC of the SCC containing r.
    Returns true if RC reached 0 (caller should dispose).
    Calls find(r) to get representative, then decrements refcount[rep]. *)
fn release
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (refcount: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (r: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to refcount src **
    pure (
      SZ.v n > 0 /\
      SZ.v r < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      SZ.v n <= A.length refcount /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length src == A.length refcount /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
    )
  returns should_dispose: bool
  ensures exists* sp sr src'.
    A.pts_to tag stag **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to refcount src' **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp sr (SZ.v n))
    )
