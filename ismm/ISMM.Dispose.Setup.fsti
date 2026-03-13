(*
   ISMM Dispose Setup — Pre-loop setup for dispose.
   
   Pushes initial representative to DFS stack, marks it as PROCESSING (tag 3→2),
   and establishes the loop invariant for dispose_loop.
*)
module ISMM.Dispose.Setup
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

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
fn dispose_setup
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (refcount: A.array SZ.t)
  (dfs_stk: A.array SZ.t)
  (dfs_top: ref SZ.t)
  (scc_top: ref SZ.t)
  (n: SZ.t)
  (rep: SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (#sdfs: Ghost.erased (Seq.seq SZ.t))
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to refcount src **
    A.pts_to dfs_stk sdfs **
    R.pts_to dfs_top 0sz **
    R.pts_to scc_top 0sz **
    pure (
      SZ.v n > 0 /\
      SZ.v rep < SZ.v n /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sparent /\
      SZ.v n <= Seq.length srank /\
      SZ.v n <= Seq.length src /\
      Seq.length sdfs == SZ.v n /\
      Seq.length sparent == Seq.length srank /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index stag i)} i < SZ.v n /\ SZ.v (Seq.index stag i) == 3 /\ i <> SZ.v rep ==> SZ.v (Seq.index src i) > 0) /\
      Count.count_eq stag 1 (SZ.v n) == 0 /\
      SZ.v (Seq.index stag (SZ.v rep)) == 3
    )
  ensures exists* st_out sdfs_out.
    A.pts_to tag st_out **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to refcount src **
    A.pts_to dfs_stk sdfs_out **
    R.pts_to dfs_top 1sz **
    R.pts_to scc_top 0sz **
    pure (
      SZ.v n > 0 /\
      SZ.v n <= Seq.length st_out /\
      SZ.v n <= Seq.length sparent /\
      SZ.v n <= Seq.length srank /\
      SZ.v n <= Seq.length src /\
      Seq.length st_out == Seq.length stag /\
      Seq.length sdfs_out == SZ.v n /\
      Seq.length sparent == Seq.length srank /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st_out sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sdfs_out i)} i < 1 ==> SZ.v (Seq.index sdfs_out i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index st_out i)} i < SZ.v n /\ SZ.v (Seq.index st_out i) == 3 ==> SZ.v (Seq.index src i) > 0) /\
      Count.count_eq st_out 1 (SZ.v n) == 0 /\
      1 + Count.count_eq st_out 3 (SZ.v n) <= SZ.v n
    )
#pop-options
