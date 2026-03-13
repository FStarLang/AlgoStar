(*
   ISMM Dispose Inner — Implementation of field-iteration helper
   
   Iterates over all fields of node x during SCC collection.
   For each edge x→fi (adj[x*n+fi] != 0), calls dispose_process_field.
   Factored out of dispose_process_scc to reduce VC complexity.
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
module Arith = ISMM.Arith.Lemmas
open ISMM.Status
open ISMM.Dispose.Helpers

module Count = ISMM.Count


#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
```pulse
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
{
  let mut field_idx: SZ.t = 0sz;
  while (!field_idx <^ n)
  invariant exists* vfi st2 sp2 sr2 sdfs3 sscc3 vdt3 vst3 src3.
    R.pts_to field_idx vfi **
    A.pts_to tag st2 **
    A.pts_to parent sp2 **
    A.pts_to rank sr2 **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src3 **
    A.pts_to dfs_stk sdfs3 **
    R.pts_to dfs_top vdt3 **
    A.pts_to scc_stk sscc3 **
    R.pts_to scc_top vst3 **
    pure (
      SZ.v n > 0 /\
      SZ.v x < SZ.v n /\
      SZ.v vfi <= SZ.v n /\
      SZ.v vdt3 <= SZ.v n /\
      SZ.v vst3 <= SZ.v n /\
      SZ.v vst3 >= SZ.v vst /\
      SZ.v vdt3 >= SZ.v vdt /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length st2 == Seq.length stag /\
      Seq.length sp2 == Seq.length sparent /\
      Seq.length sr2 == Seq.length srank /\
      Seq.length src3 == Seq.length src /\
      SZ.v n <= Seq.length st2 /\
      SZ.v n <= Seq.length sp2 /\
      SZ.v n <= Seq.length sr2 /\
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdfs3 == SZ.v n /\
      Seq.length sscc3 == SZ.v n /\
      Impl.is_forest sp2 (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st2 sp2 sr2 (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sscc3 i)} i < SZ.v vst3 ==> SZ.v (Seq.index sscc3 i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sdfs3 i)} i < SZ.v vdt3 ==> SZ.v (Seq.index sdfs3 i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index st2 i)} i < SZ.v n /\ SZ.v (Seq.index st2 i) == 3 ==> SZ.v (Seq.index src3 i) > 0) /\
      SZ.v vst3 == Count.count_eq st2 1 (SZ.v n) /\
      SZ.v vdt3 + Count.count_eq st2 3 (SZ.v n) <= SZ.v n
    )
  decreases (SZ.v n - SZ.v !field_idx)
  {
    let fi = !field_idx;
    Arith.adj_index_fits (SZ.v n) (SZ.v x) (SZ.v fi);
    let edge_idx = SZ.(x *^ n +^ fi);
    let has_edge = adj.(edge_idx);
    
    if (has_edge <>^ 0sz) {
      dispose_process_field tag parent rank adj refcount dfs_stk dfs_top scc_stk scc_top fi n;
      field_idx := SZ.(fi +^ 1sz);
      ()
    } else {
      field_idx := SZ.(fi +^ 1sz);
      ()
    }
  }
}
```
#pop-options
