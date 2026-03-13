(*
   ISMM Dispose ProcessSCC — Implementation of SCC processing.
   
   Push rep to scc stack, mark as tag-1, walk all SCC members
   via dispose_process_node_fields, then scan-cleanup tag-1→tag-0.
*)
module ISMM.Dispose.ProcessSCC
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
module UFL = ISMM.UF.Lemmas
module Arith = ISMM.Arith.Lemmas
open ISMM.Status
open ISMM.Dispose.Helpers
open ISMM.Dispose.Inner

module Count = ISMM.Count


#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
```pulse
fn dispose_process_scc
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (refcount: A.array SZ.t)
  (dfs_stk: A.array SZ.t) (dfs_top: ref SZ.t)
  (scc_stk: A.array SZ.t) (scc_top: ref SZ.t)
  (rep: SZ.t) (n: SZ.t)
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
      SZ.v rep < SZ.v n /\
      SZ.v n > 0 /\
      SZ.v vdt <= SZ.v n /\
      SZ.v vst == 0 /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sparent /\
      SZ.v n <= Seq.length srank /\
      Seq.length sparent == Seq.length srank /\
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
      Seq.length st' == Seq.length stag /\
      Seq.length sp' == Seq.length sparent /\
      Seq.length sr' == Seq.length srank /\
      Seq.length sp' == Seq.length sr' /\
      Seq.length src' == Seq.length src /\
      SZ.v n <= Seq.length st' /\
      SZ.v n <= Seq.length sp' /\
      SZ.v n <= Seq.length sr' /\
      SZ.v n <= Seq.length src' /\
      Seq.length sdfs' == SZ.v n /\
      Seq.length sscc' == SZ.v n /\
      Impl.is_forest sp' (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st' sp' sr' (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sdfs' i)} i < SZ.v vdt' ==> SZ.v (Seq.index sdfs' i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index st' i)} i < SZ.v n /\ SZ.v (Seq.index st' i) == 3 ==> SZ.v (Seq.index src' i) > 0) /\
      Count.count_eq st' 1 (SZ.v n) == 0 /\
      SZ.v vdt' + Count.count_eq st' 3 (SZ.v n) <= SZ.v n
    )
{
  // Push rep to scc stack and mark as VISITED (tag 1)
  let st0 = !scc_top;
  Arith.seq_upd_content_bound sscc (SZ.v st0) (SZ.v n) rep;
  scc_stk.(st0) <- rep;
  tag.(rep) <- 1sz;
  scc_top := SZ.(st0 +^ 1sz);
  
  // Tag update to 1: preserves uf_inv
  Count.count_eq_zero_implies_none stag 1 (SZ.v n);
  UFL.tag_update_preserves_uf_inv stag sparent srank (SZ.v n) (SZ.v rep) 1sz;
  Arith.tag_upd_preserves_rc_positive stag src (SZ.v n) (SZ.v rep) 1sz;
  Count.count_eq_mark stag 1 (SZ.v n) (SZ.v rep) 1sz;
  Count.count_eq_nonincreasing_on_update stag 3 (SZ.v n) (SZ.v rep) 1sz;
  
  with st1. assert (A.pts_to tag st1);
  with sp1. assert (A.pts_to parent sp1);
  with sr1. assert (A.pts_to rank sr1);
  
  // Process all nodes in SCC: walk scc stack, examine each node's fields
  let mut scc_idx: SZ.t = st0;
  while (!scc_idx <^ !scc_top)
  invariant exists* vidx vst2 vdt2 st sp sr sdfs2 sscc2 src2.
    R.pts_to scc_idx vidx **
    R.pts_to scc_top vst2 **
    R.pts_to dfs_top vdt2 **
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src2 **
    A.pts_to dfs_stk sdfs2 **
    A.pts_to scc_stk sscc2 **
    pure (
      SZ.v n > 0 /\
      SZ.v vidx <= SZ.v vst2 /\
      SZ.v vst2 <= SZ.v n /\
      SZ.v vdt2 <= SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length st == Seq.length stag /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Seq.length sp == Seq.length sr /\
      Seq.length src2 == Seq.length src /\
      SZ.v n <= Seq.length st /\
      SZ.v n <= Seq.length sp /\
      SZ.v n <= Seq.length sr /\
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdfs2 == SZ.v n /\
      Seq.length sscc2 == SZ.v n /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st sp sr (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sscc2 i)} i < SZ.v vst2 ==> SZ.v (Seq.index sscc2 i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sdfs2 i)} i < SZ.v vdt2 ==> SZ.v (Seq.index sdfs2 i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index st i)} i < SZ.v n /\ SZ.v (Seq.index st i) == 3 ==> SZ.v (Seq.index src2 i) > 0) /\
      SZ.v vst2 == Count.count_eq st 1 (SZ.v n) /\
      SZ.v vdt2 + Count.count_eq st 3 (SZ.v n) <= SZ.v n
    )
  {
    let idx = !scc_idx;
    let x = scc_stk.(idx);
    
    // Process all fields of x via extracted helper
    dispose_process_node_fields tag parent rank adj refcount dfs_stk dfs_top scc_stk scc_top x n;
    
    // Advance scc_idx
    scc_idx := SZ.(idx +^ 1sz);
    ()
  };
  
  // --- Second pass: scan cleanup of tag-1 entries ---
  with st_exit. assert (A.pts_to tag st_exit);
  with sp_exit. assert (A.pts_to parent sp_exit);
  with sr_exit. assert (A.pts_to rank sr_exit);
  with src_exit. assert (A.pts_to refcount src_exit);
  assert (pure (Seq.length sp_exit == Seq.length sr_exit));
  dispose_scan_cleanup tag parent rank refcount n;
  ()
}
```
#pop-options
