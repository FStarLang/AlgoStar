(*
   ISMM Dispose Inner — Interface for field-iteration helper
   
   Iterates over all fields of a node during SCC collection,
   calling dispose_process_field for each edge. Factored out of
   dispose_process_scc to isolate the inner loop VC.
*)
module ISMM.Dispose.Inner
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

(** Process all fields of node x: for each edge x→fi, call dispose_process_field.
    Maintains all invariants and guarantees scc_top/dfs_top are non-decreasing. *)
fn dispose_process_node_fields
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (refcount: A.array SZ.t)
  (dfs_stk: A.array SZ.t) (dfs_top: ref SZ.t)
  (scc_stk: A.array SZ.t) (scc_top: ref SZ.t)
  (x: SZ.t) (n: SZ.t)
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
      SZ.v x < SZ.v n /\
      SZ.v n > 0 /\
      SZ.v vdt <= SZ.v n /\
      SZ.v vst <= SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sparent /\
      SZ.v n <= Seq.length srank /\
      SZ.v n <= Seq.length src /\
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdfs == SZ.v n /\
      Seq.length sscc == SZ.v n /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sscc i)} i < SZ.v vst ==> SZ.v (Seq.index sscc i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sdfs i)} i < SZ.v vdt ==> SZ.v (Seq.index sdfs i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index stag i)} i < SZ.v n /\ SZ.v (Seq.index stag i) == 3 ==> SZ.v (Seq.index src i) > 0) /\
      SZ.v vst == Count.count_eq stag 1 (SZ.v n) /\
      SZ.v vdt + Count.count_eq stag 3 (SZ.v n) <= SZ.v n
    )
  ensures exists* st' sp' sr' sdfs' sscc' vdt' vst' src'.
    A.pts_to tag st' **
    A.pts_to parent sp' **
    A.pts_to rank sr' **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src' **
    A.pts_to dfs_stk sdfs' **
    R.pts_to dfs_top vdt' **
    A.pts_to scc_stk sscc' **
    R.pts_to scc_top vst' **
    pure (
      SZ.v vdt' <= SZ.v n /\
      SZ.v vst' <= SZ.v n /\
      SZ.v vst' >= SZ.v vst /\
      SZ.v vdt' >= SZ.v vdt /\
      Seq.length st' == Seq.length stag /\
      Seq.length sp' == Seq.length sparent /\
      Seq.length sr' == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      SZ.v n <= Seq.length st' /\
      SZ.v n <= Seq.length sp' /\
      SZ.v n <= Seq.length sr' /\
      SZ.v n <= Seq.length src' /\
      Seq.length sdfs' == SZ.v n /\
      Seq.length sscc' == SZ.v n /\
      Impl.is_forest sp' (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st' sp' sr' (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sscc' i)} i < SZ.v vst' ==> SZ.v (Seq.index sscc' i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sdfs' i)} i < SZ.v vdt' ==> SZ.v (Seq.index sdfs' i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index st' i)} i < SZ.v n /\ SZ.v (Seq.index st' i) == 3 ==> SZ.v (Seq.index src' i) > 0) /\
      SZ.v vst' == Count.count_eq st' 1 (SZ.v n) /\
      SZ.v vdt' + Count.count_eq st' 3 (SZ.v n) <= SZ.v n
    )
