(*
   ISMM Dispose Helpers — Helper functions for the dispose algorithm
   
   Factored out to keep VCs small and enable parallel verification.
   - dispose_process_field: Process one edge during SCC collection
   - dispose_scan_cleanup: Zero all tag-1 entries after SCC processing
*)
module ISMM.Dispose.Helpers
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

module Count = ISMM.Count


(* ---------- Helper: Process one field of a node during SCC collection ---------- *)

#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"
```pulse
fn dispose_process_field
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (refcount: A.array SZ.t)
  (dfs_stk: A.array SZ.t) (dfs_top: ref SZ.t)
  (scc_stk: A.array SZ.t) (scc_top: ref SZ.t)
  (field_node: SZ.t) (n: SZ.t)
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
      SZ.v field_node < SZ.v n /\
      SZ.v n > 0 /\
      SZ.v vdt <= SZ.v n /\
      SZ.v vst <= SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sparent /\
      SZ.v n <= Seq.length srank /\
      SZ.v n <= Seq.length src /\
      Seq.length sdfs == SZ.v n /\
      Seq.length sscc == SZ.v n /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sscc i)} i < SZ.v vst ==> SZ.v (Seq.index sscc i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sdfs i)} i < SZ.v vdt ==> SZ.v (Seq.index sdfs i) < SZ.v n) /\
      // RC-positive: all RC-tagged nodes have positive refcount
      (forall (i:nat). {:pattern (Seq.index stag i)} i < SZ.v n /\ SZ.v (Seq.index stag i) == 3 ==> SZ.v (Seq.index src i) > 0) /\
      // Count invariants for stack overflow bounds
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
      SZ.v vst' >= SZ.v vst /\
      SZ.v vdt' >= SZ.v vdt /\
      (forall (i:nat). {:pattern (Seq.index sscc' i)} i < SZ.v vst' ==> SZ.v (Seq.index sscc' i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sdfs' i)} i < SZ.v vdt' ==> SZ.v (Seq.index sdfs' i) < SZ.v n) /\
      // RC-positive maintained
      (forall (i:nat). {:pattern (Seq.index st' i)} i < SZ.v n /\ SZ.v (Seq.index st' i) == 3 ==> SZ.v (Seq.index src' i) > 0) /\
      // Count invariants maintained
      SZ.v vst' == Count.count_eq st' 1 (SZ.v n) /\
      SZ.v vdt' + Count.count_eq st' 3 (SZ.v n) <= SZ.v n
    )
{
  // Find representative of the field target
  let rep_f = Impl.find_set parent field_node n #sparent #stag #srank;
  with sp1. assert (A.pts_to parent sp1);
  
  let tag_f = tag.(rep_f);
  
  if (tag_f = 1sz) {
    // PROCESSING: same SCC — add field_node to scc if not already visited
    let tag_fn = tag.(field_node);
    if (tag_fn = 2sz) {
      // field_node has tag 2 (REP, not yet visited): push to scc
      let st = !scc_top;
      // Prove scc_top < n from count invariant:
      // tag[field_node] = 2 != 1, so count_eq(stag,1,n) < n
      // scc_top <= count_eq(stag,1,n) < n, so scc_top < n
      Count.count_eq_gap stag 1 (SZ.v n) (SZ.v field_node);
      // Prove content invariant after push
      Arith.seq_upd_content_bound sscc (SZ.v st) (SZ.v n) field_node;
      scc_stk.(st) <- field_node;
      tag.(field_node) <- 1sz;
      scc_top := SZ.(st +^ 1sz);
      // Tag-only update (→visited/tag 1): preserves uf_inv
      with st1. assert (A.pts_to tag st1);
      UFL.tag_update_preserves_uf_inv stag sp1 srank (SZ.v n) (SZ.v field_node) 1sz;
      Arith.tag_upd_preserves_rc_positive stag src (SZ.v n) (SZ.v field_node) 1sz;
      // Count invariant for tag 1: mark increases count by 1
      Count.count_eq_mark stag 1 (SZ.v n) (SZ.v field_node) 1sz;
      // Count invariant for tag 3: tag 2→1 preserves count_tag3
      Count.count_eq_preserve stag 3 (SZ.v n) (SZ.v field_node) 1sz;
      ()
    } else { () }
  } else {
    if (tag_f = 3sz) {
      // RC node in different SCC: decref
      let rc = refcount.(rep_f);
      if (rc = 1sz) {
        // RC hits 0 — mark as PROCESSING and push to dfs for cascade
        refcount.(rep_f) <- 0sz;
        with src1. assert (A.pts_to refcount src1);
        tag.(rep_f) <- 2sz;
        let dt = !dfs_top;
        // Prove dfs_top < n from count invariant:
        // tag[rep_f] = 3, so count_eq(stag,3,n) >= 1
        // dfs_top + count_eq(stag,3,n) <= n, so dfs_top <= n-1 < n
        Count.count_eq_pos stag 3 (SZ.v n) (SZ.v rep_f);
        // Prove content invariant after push
        Arith.seq_upd_content_bound sdfs (SZ.v dt) (SZ.v n) rep_f;
        dfs_stk.(dt) <- rep_f;
        dfs_top := SZ.(dt +^ 1sz);
        with st1. assert (A.pts_to tag st1);
        UFL.tag_update_preserves_uf_inv stag sp1 srank (SZ.v n) (SZ.v rep_f) 2sz;
        Arith.tag_rc_upd_preserves_rc_positive stag src (SZ.v n) (SZ.v rep_f) 2sz 0sz;
        // Count invariant for tag 3: unmark decreases count by 1
        Count.count_eq_unmark stag 3 (SZ.v n) (SZ.v rep_f) 2sz;
        // Count invariant for tag 1: tag 3→2 preserves count_tag1
        Count.count_eq_preserve stag 1 (SZ.v n) (SZ.v rep_f) 2sz;
        ()
      } else {
        // RC > 1: just decrement
        // From RC-positive invariant: tag[rep_f]=3 ∧ rep_f < n ⟹ rc[rep_f] > 0
        // rc != 1 ∧ rc > 0 ⟹ rc ≥ 2 ⟹ fits(rc - 1)
        assert (pure (SZ.v rc > 0));
        Arith.rc_dec_fits (SZ.v rc);
        Arith.rc_upd_preserves_rc_positive stag src (SZ.v n) (SZ.v rep_f) SZ.(rc -^ 1sz);
        refcount.(rep_f) <- SZ.(rc -^ 1sz);
        with src1. assert (A.pts_to refcount src1);
        ()
      }
    } else { () }
  }
}
```
#pop-options


(* ---------- Helper: Scan cleanup of tag-1 entries ----------
   After SCC processing, scan all n entries and zero any tag-1 nodes.
   This restores count_eq st 1 n == 0 without needing to track which
   scc_stk entries correspond to tag-1 nodes. *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
```pulse
fn dispose_scan_cleanup
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (refcount: A.array SZ.t)
  (n: SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to refcount src **
    pure (
      SZ.v n > 0 /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sparent /\
      SZ.v n <= Seq.length srank /\
      SZ.v n <= Seq.length src /\
      Seq.length sparent == Seq.length srank /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index stag i)} i < SZ.v n /\ SZ.v (Seq.index stag i) == 3 ==> SZ.v (Seq.index src i) > 0)
    )
  ensures exists* st' src'.
    A.pts_to tag st' **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to refcount src' **
    pure (
      Seq.length st' == Seq.length stag /\
      Seq.length src' == Seq.length src /\
      SZ.v n <= Seq.length st' /\
      SZ.v n <= Seq.length src' /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st' sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index st' i)} i < SZ.v n /\ SZ.v (Seq.index st' i) == 3 ==> SZ.v (Seq.index src' i) > 0) /\
      Count.count_eq st' 1 (SZ.v n) == 0 /\
      Count.count_eq st' 3 (SZ.v n) == Count.count_eq stag 3 (SZ.v n)
    )
{
  let mut scan: SZ.t = 0sz;
  while (!scan <^ n)
  invariant exists* vscan st_s src_s.
    R.pts_to scan vscan **
    A.pts_to tag st_s **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to refcount src_s **
    pure (
      SZ.v vscan <= SZ.v n /\
      Seq.length st_s == Seq.length stag /\
      Seq.length src_s == Seq.length src /\
      SZ.v n <= Seq.length st_s /\
      SZ.v n <= Seq.length src_s /\
      Seq.length sparent == Seq.length srank /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st_s sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index st_s i)} i < SZ.v n /\ SZ.v (Seq.index st_s i) == 3 ==> SZ.v (Seq.index src_s i) > 0) /\
      (forall (i:nat). {:pattern (Seq.index st_s i)} i < SZ.v vscan ==> SZ.v (Seq.index st_s i) <> 1) /\
      Count.count_eq st_s 3 (SZ.v n) == Count.count_eq stag 3 (SZ.v n)
    )
  decreases (SZ.v n - SZ.v !scan)
  {
    let sc = !scan;
    let t = tag.(sc);
    
    if (t = 1sz) {
      with st_pre. assert (A.pts_to tag st_pre);
      with src_pre. assert (A.pts_to refcount src_pre);
      
      UFL.tag_update_preserves_uf_inv st_pre sparent srank (SZ.v n) (SZ.v sc) 0sz;
      Arith.tag_upd_preserves_rc_positive st_pre src_pre (SZ.v n) (SZ.v sc) 0sz;
      Arith.all_ne_after_upd st_pre 1 (SZ.v sc) (SZ.v n) 0sz;
      // tag 1→0: neither 1 nor 0 is 3, so count_tag3 preserved
      Count.count_eq_preserve st_pre 3 (SZ.v n) (SZ.v sc) 0sz;
      
      tag.(sc) <- 0sz;
      scan := SZ.(sc +^ 1sz);
      ()
    } else {
      with st_pre. assert (A.pts_to tag st_pre);
      Arith.all_ne_extend st_pre 1 (SZ.v sc);
      scan := SZ.(sc +^ 1sz);
      ()
    }
  };
  
  with st_final. assert (A.pts_to tag st_final);
  Count.count_eq_zero_from_all_ne st_final 1 (SZ.v n);
  ()
}
```
#pop-options
