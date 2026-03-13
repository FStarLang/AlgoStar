(*
   ISMM Dispose — Interface
   
   Pulse interface for the dispose algorithm (paper §3.4, Fig. 4).
   dispose(r): Deallocates all nodes in the SCC of r (whose RC hit 0),
   cascading to child SCCs whose RC also reaches 0.
*)
module ISMM.Dispose.Impl
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
module Count = ISMM.Count

(** DISPOSE: Deallocate the SCC rooted at rep, cascading to child SCCs.
    Modifies tag (marks freed nodes as UNMARKED=0) and refcount (decrements child RCs).
    Parent and rank arrays are read-only (used for find operations).
    Adjacency matrix is read-only (used to find edges). *)
fn dispose
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (refcount: A.array SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#sadj: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (rep: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src **
    pure (
      SZ.v n > 0 /\
      SZ.v rep < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      SZ.v n <= A.length refcount /\
      SZ.v n * SZ.v n <= A.length adj /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.fits (SZ.v n * (SZ.v n + 1)) /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length sadj == A.length adj /\
      Seq.length src == A.length refcount /\
      A.length parent == A.length rank /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index stag i)} i < SZ.v n /\ SZ.v (Seq.index stag i) == 3 /\ i <> SZ.v rep ==> SZ.v (Seq.index src i) > 0) /\
      Count.count_eq stag 1 (SZ.v n) == 0 /\
      SZ.v (Seq.index stag (SZ.v rep)) == 3
    )
  ensures exists* st sp sr src'.
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src' **
    pure (
      Seq.length st == Seq.length stag /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      SZ.v n <= Seq.length st /\
      SZ.v n <= Seq.length src' /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st sp sr (SZ.v n)) /\
      // RC-positive maintained
      (forall (i:nat). {:pattern (Seq.index st i)} i < SZ.v n /\ SZ.v (Seq.index st i) == 3 ==> SZ.v (Seq.index src' i) > 0)
    )
