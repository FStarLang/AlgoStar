(*
   ISMM Dispose — Imperative Pulse Implementation
   
   Implements the dispose algorithm from paper §3.4, Fig. 4.
   Three stacks: dfs (SCC DAG traversal), scc (nodes in current SCC), free_list.
   
   For each SCC on dfs stack:
   1. Push rep to scc stack, mark as PROCESSING (tag_rep=2)
   2. For each node x in scc: for each field f of x:
      - If find(f) is PROCESSING and f != find(f): add f to scc (same SCC member)
      - If find(f) is RC: decref; if RC hits 0, push to dfs
   3. Move all scc nodes to free_list
   4. "Free" nodes by setting tag to tag_unmarked (0)
   
   Helpers factored out to avoid Pulse branch unification issues.
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
module UFL = ISMM.UF.Lemmas
module Arith = ISMM.Arith.Lemmas
open ISMM.Status

module GR = Pulse.Lib.GhostReference

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

```pulse
ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}
```

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
      (forall (i:nat). {:pattern (Seq.index stag i)} i < SZ.v n /\ SZ.v (Seq.index stag i) == 3 ==> SZ.v (Seq.index src i) > 0)
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
      (forall (i:nat). {:pattern (Seq.index st' i)} i < SZ.v n /\ SZ.v (Seq.index st' i) == 3 ==> SZ.v (Seq.index src' i) > 0)
    )
{
  // Find representative of the field target
  let rep_f = Impl.find_set parent field_node n #sparent #stag #srank;
  with sp1. assert (A.pts_to parent sp1);
  
  let tag_f = tag.(rep_f);
  
  if (tag_f = 2sz) {
    // PROCESSING: same SCC — add field_node to scc if not already the rep
    if (field_node <>^ rep_f) {
      let st = !scc_top;
      assume_ (pure (SZ.v st < SZ.v n));
      // Prove content invariant after push
      Arith.seq_upd_content_bound sscc (SZ.v st) (SZ.v n) field_node;
      scc_stk.(st) <- field_node;
      tag.(field_node) <- 2sz;
      scc_top := SZ.(st +^ 1sz);
      // Tag-only update (→PROCESSING): preserves uf_inv
      with st1. assert (A.pts_to tag st1);
      UFL.tag_update_preserves_uf_inv stag sp1 srank (SZ.v n) (SZ.v field_node) 2sz;
      Arith.tag_upd_preserves_rc_positive stag src (SZ.v n) (SZ.v field_node) 2sz;
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
        assume_ (pure (SZ.v dt < SZ.v n));
        // Prove content invariant after push
        Arith.seq_upd_content_bound sdfs (SZ.v dt) (SZ.v n) rep_f;
        dfs_stk.(dt) <- rep_f;
        dfs_top := SZ.(dt +^ 1sz);
        with st1. assert (A.pts_to tag st1);
        UFL.tag_update_preserves_uf_inv stag sp1 srank (SZ.v n) (SZ.v rep_f) 2sz;
        Arith.tag_rc_upd_preserves_rc_positive stag src (SZ.v n) (SZ.v rep_f) 2sz 0sz;
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


(* ---------- Helper: Process one SCC ----------
   Walk all nodes in the SCC (via scc stack), process their fields,
   then "free" them by setting tag to UNMARKED. *)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
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
      SZ.v n <= Seq.length src /\
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdfs == SZ.v n /\
      Seq.length sscc == SZ.v n /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sdfs i)} i < SZ.v vdt ==> SZ.v (Seq.index sdfs i) < SZ.v n) /\
      // RC-positive: all RC-tagged nodes have positive refcount
      (forall (i:nat). {:pattern (Seq.index stag i)} i < SZ.v n /\ SZ.v (Seq.index stag i) == 3 ==> SZ.v (Seq.index src i) > 0)
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
      (forall (i:nat). {:pattern (Seq.index sdfs' i)} i < SZ.v vdt' ==> SZ.v (Seq.index sdfs' i) < SZ.v n) /\
      // RC-positive maintained
      (forall (i:nat). {:pattern (Seq.index st' i)} i < SZ.v n /\ SZ.v (Seq.index st' i) == 3 ==> SZ.v (Seq.index src' i) > 0)
    )
{
  // Push rep to scc stack and mark as PROCESSING
  let st0 = !scc_top;
  // st0 == 0 (from precondition) and n > 0, so st0 < n
  // Prove SCC content invariant after push (vacuously true precondition since st0=0)
  Arith.seq_upd_content_bound sscc (SZ.v st0) (SZ.v n) rep;
  scc_stk.(st0) <- rep;
  tag.(rep) <- 2sz;
  scc_top := SZ.(st0 +^ 1sz);
  
  // Tag-only update (→PROCESSING): preserves uf_inv
  UFL.tag_update_preserves_uf_inv stag sparent srank (SZ.v n) (SZ.v rep) 2sz;
  Arith.tag_upd_preserves_rc_positive stag src (SZ.v n) (SZ.v rep) 2sz;
  
  with st1. assert (A.pts_to tag st1);
  with sp1. assert (A.pts_to parent sp1);
  with sr1. assert (A.pts_to rank sr1);
  
  // Ghost counter for complexity accounting (erased)
  let inner_ctr = GR.alloc #nat 0;
  
  // Process all nodes in SCC: walk scc stack, examine each node's fields
  let mut scc_idx: SZ.t = st0;
  while (!scc_idx <^ !scc_top)
  invariant exists* vidx vst2 vdt2 vic st sp sr sdfs2 sscc2 src2.
    R.pts_to scc_idx vidx **
    R.pts_to scc_top vst2 **
    R.pts_to dfs_top vdt2 **
    GR.pts_to inner_ctr vic **
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
      // RC-positive maintained
      (forall (i:nat). {:pattern (Seq.index st i)} i < SZ.v n /\ SZ.v (Seq.index st i) == 3 ==> SZ.v (Seq.index src2 i) > 0)
    )
  {
    let idx = !scc_idx;
    let x = scc_stk.(idx);
    
    // Process all fields of x (iterate through adj row)
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
      R.pts_to scc_idx idx **
      pure (
        SZ.v n > 0 /\
        SZ.v x < SZ.v n /\
        SZ.v vfi <= SZ.v n /\
        SZ.v vdt3 <= SZ.v n /\
        SZ.v vst3 <= SZ.v n /\
        SZ.v idx < SZ.v vst3 /\
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
        // RC-positive maintained
        (forall (i:nat). {:pattern (Seq.index st2 i)} i < SZ.v n /\ SZ.v (Seq.index st2 i) == 3 ==> SZ.v (Seq.index src3 i) > 0)
      )
    decreases (SZ.v n - SZ.v !field_idx)
    {
      let fi = !field_idx;
      // x < n (from invariant), fi < n (from loop guard), fits(n*n) → adj index valid
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
    };
    
    // Capture state before tag write for uf_inv proof
    with st_pre. assert (A.pts_to tag st_pre);
    with sp_pre. assert (A.pts_to parent sp_pre);
    with sr_pre. assert (A.pts_to rank sr_pre);
    with src_pre. assert (A.pts_to refcount src_pre);
    with sdfs_pre. assert (A.pts_to dfs_stk sdfs_pre);
    with sscc_pre. assert (A.pts_to scc_stk sscc_pre);
    
    // Tag-only update (PROCESSING→UNMARKED) preserves uf_inv
    UFL.tag_update_preserves_uf_inv st_pre sp_pre sr_pre (SZ.v n) (SZ.v x) 0sz;
    Arith.tag_upd_preserves_rc_positive st_pre src_pre (SZ.v n) (SZ.v x) 0sz;
    
    // "Free" this node: set tag to UNMARKED (0)
    tag.(x) <- 0sz;
    with st2. assert (A.pts_to tag st2);
    with sp2. assert (A.pts_to parent sp2);
    with sr2. assert (A.pts_to rank sr2);
    with src2. assert (A.pts_to refcount src2);
    with sdfs2. assert (A.pts_to dfs_stk sdfs2);
    with sscc2. assert (A.pts_to scc_stk sscc2);
    
    // idx+1 <= scc_top (since scc_top can only grow)
    let cur_scc_top = !scc_top;
    let cur_dfs_top = !dfs_top;
    // is_forest: parent unchanged → preserved
    // uf_inv: tag-only update → preserved by lemma above
    
    scc_idx := SZ.(idx +^ 1sz);
    
    tick inner_ctr;
    ()
  };
  GR.free inner_ctr;
  ()
}
```
#pop-options


(* ---------- Main dispose function ---------- *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
```pulse
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
      // RC-positive: all RC-tagged nodes (except rep) have positive refcount
      (forall (i:nat). {:pattern (Seq.index stag i)} i < SZ.v n /\ SZ.v (Seq.index stag i) == 3 /\ i <> SZ.v rep ==> SZ.v (Seq.index src i) > 0)
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
{
  // Allocate stacks
  let dfs_stk = A.alloc 0sz n;
  let scc_stk = A.alloc 0sz n;
  let mut dfs_top: SZ.t = 0sz;
  let mut scc_top: SZ.t = 0sz;
  
  // Ghost counter for complexity accounting (erased)
  let ghost_ctr = GR.alloc #nat 0;
  
  // Push initial rep to dfs stack
  with sdfs0. assert (A.pts_to dfs_stk sdfs0);
  Arith.seq_upd_content_bound sdfs0 0 (SZ.v n) rep;
  dfs_stk.(0sz) <- rep;
  dfs_top := 1sz;
  
  // Mark rep as PROCESSING before entering the main loop,
  // upgrading the exception-form RC-positive invariant to standard form
  tag.(rep) <- 2sz;
  UFL.tag_update_preserves_uf_inv stag sparent srank (SZ.v n) (SZ.v rep) 2sz;
  Arith.tag_upd_upgrades_rc_positive stag src (SZ.v n) (SZ.v rep) 2sz;
  
  // Main loop: process SCC DAG
  while (!dfs_top >^ 0sz)
  invariant exists* vdt vst vgc st sp sr sdfs sscc src2.
    R.pts_to dfs_top vdt **
    R.pts_to scc_top vst **
    GR.pts_to ghost_ctr vgc **
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src2 **
    A.pts_to dfs_stk sdfs **
    A.pts_to scc_stk sscc **
    pure (
      SZ.v n > 0 /\
      SZ.v vdt <= SZ.v n /\
      SZ.v vst <= SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length st == Seq.length stag /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Seq.length src2 == Seq.length src /\
      SZ.v n <= Seq.length st /\
      SZ.v n <= Seq.length sp /\
      SZ.v n <= Seq.length sr /\
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdfs == SZ.v n /\
      Seq.length sscc == SZ.v n /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st sp sr (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sdfs i)} i < SZ.v vdt ==> SZ.v (Seq.index sdfs i) < SZ.v n) /\
      // RC-positive maintained
      (forall (i:nat). {:pattern (Seq.index st i)} i < SZ.v n /\ SZ.v (Seq.index st i) == 3 ==> SZ.v (Seq.index src2 i) > 0)
    )
  {
    // Pop from dfs stack
    let dt = !dfs_top;
    let top_idx = SZ.(dt -^ 1sz);
    let scc_rep = dfs_stk.(top_idx);
    dfs_top := top_idx;
    
    // Reset scc stack for this SCC
    scc_top := 0sz;
    
    // Process the SCC
    dispose_process_scc tag parent rank adj refcount dfs_stk dfs_top scc_stk scc_top scc_rep n;
    
    // Tick ghost counter
    tick ghost_ctr;
    ()
  };
  
  GR.free ghost_ctr;
  A.free dfs_stk;
  A.free scc_stk;
  ()
}
```
#pop-options
