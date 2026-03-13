(*
   ISMM Dispose Loop — Interface for the main DFS loop of dispose.
   
   Pops SCC reps from the dfs stack and calls dispose_process_scc
   until the dfs stack is empty.
*)
module ISMM.Dispose.Loop
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

fn dispose_loop
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (refcount: A.array SZ.t)
  (dfs_stk: A.array SZ.t) (dfs_top: ref SZ.t)
  (scc_stk: A.array SZ.t) (scc_top: ref SZ.t)
  (n: SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#sadj: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (#sdfs: Ghost.erased (Seq.seq SZ.t))
  (#sscc: Ghost.erased (Seq.seq SZ.t))
  (#vdt: Ghost.erased SZ.t)
  (#vst: Ghost.erased SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src **
    A.pts_to dfs_stk sdfs **
    R.pts_to dfs_top vdt **
    A.pts_to scc_stk sscc **
    R.pts_to scc_top vst **
    pure (
      SZ.v n > 0 /\
      SZ.v vdt <= SZ.v n /\
      SZ.v vst <= SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length sadj == A.length adj /\
      Seq.length src == A.length refcount /\
      A.length parent == A.length rank /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sparent /\
      SZ.v n <= Seq.length srank /\
      SZ.v n <= Seq.length src /\
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdfs == SZ.v n /\
      Seq.length sscc == SZ.v n /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sdfs i)} i < SZ.v vdt ==> SZ.v (Seq.index sdfs i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index stag i)} i < SZ.v n /\ SZ.v (Seq.index stag i) == 3 ==> SZ.v (Seq.index src i) > 0) /\
      Count.count_eq stag 1 (SZ.v n) == 0 /\
      SZ.v vdt + Count.count_eq stag 3 (SZ.v n) <= SZ.v n
    )
  ensures exists* st sp sr src' sdfs' sscc' vdt' vst'.
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src' **
    A.pts_to dfs_stk sdfs' **
    R.pts_to dfs_top vdt' **
    A.pts_to scc_stk sscc' **
    R.pts_to scc_top vst' **
    pure (
      Seq.length st == Seq.length stag /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      SZ.v n <= Seq.length st /\
      SZ.v n <= Seq.length src' /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st sp sr (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index st i)} i < SZ.v n /\ SZ.v (Seq.index st i) == 3 ==> SZ.v (Seq.index src' i) > 0)
    )
