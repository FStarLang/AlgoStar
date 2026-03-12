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


(* ---------- Helper: Process one field of a node during SCC collection ---------- *)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
```pulse
fn dispose_process_field
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (dfs_stk: A.array SZ.t) (dfs_top: ref SZ.t)
  (scc_stk: A.array SZ.t) (scc_top: ref SZ.t)
  (field_node: SZ.t) (n: SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#sadj: Ghost.erased (Seq.seq SZ.t))
  (#sdfs: Ghost.erased (Seq.seq SZ.t))
  (#sscc: Ghost.erased (Seq.seq SZ.t))
  (#vdt: Ghost.erased SZ.t)
  (#vst: Ghost.erased SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
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
      Seq.length sdfs == SZ.v n /\
      Seq.length sscc == SZ.v n /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
    )
  ensures exists* st' sp' sr' sdfs' sscc' vdt' vst'.
    A.pts_to tag st' **
    A.pts_to parent sp' **
    A.pts_to rank sr' **
    A.pts_to adj #0.5R sadj **
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
      SZ.v n <= Seq.length st' /\
      SZ.v n <= Seq.length sp' /\
      SZ.v n <= Seq.length sr' /\
      Seq.length sdfs' == SZ.v n /\
      Seq.length sscc' == SZ.v n /\
      Impl.is_forest sp' (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st' sp' sr' (SZ.v n))
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
      scc_stk.(st) <- field_node;
      tag.(field_node) <- 2sz;
      scc_top := SZ.(st +^ 1sz);
      // Tag-only update (→PROCESSING): preserves uf_inv
      with st1. assert (A.pts_to tag st1);
      UFL.tag_update_preserves_uf_inv stag sp1 srank (SZ.v n) (SZ.v field_node) 2sz;
      ()
    } else { () }
  } else {
    if (tag_f = 3sz) {
      // RC node in different SCC: decref
      let rc = rank.(rep_f);
      if (rc = 1sz) {
        // RC hits 0 — mark as PROCESSING and push to dfs for cascade
        rank.(rep_f) <- 0sz;
        tag.(rep_f) <- 2sz;
        let dt = !dfs_top;
        assume_ (pure (SZ.v dt < SZ.v n));
        dfs_stk.(dt) <- rep_f;
        dfs_top := SZ.(dt +^ 1sz);
        // Proof obligation: tag+rank update preserves uf_inv
        with st1. assert (A.pts_to tag st1);
        with sr1. assert (A.pts_to rank sr1);
        assume_ (pure (
          Impl.is_forest sp1 (SZ.v n) /\
          Spec.uf_inv (Impl.to_uf st1 sp1 sr1 (SZ.v n))
        ));
        ()
      } else {
        // RC > 1: just decrement
        assume_ (pure (SZ.v rc > 0 /\ SZ.fits (SZ.v rc - 1)));
        rank.(rep_f) <- SZ.(rc -^ 1sz);
        with sr1. assert (A.pts_to rank sr1);
        assume_ (pure (
          Impl.is_forest sp1 (SZ.v n) /\
          Spec.uf_inv (Impl.to_uf stag sp1 sr1 (SZ.v n))
        ));
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
  (dfs_stk: A.array SZ.t) (dfs_top: ref SZ.t)
  (scc_stk: A.array SZ.t) (scc_top: ref SZ.t)
  (rep: SZ.t) (n: SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#sadj: Ghost.erased (Seq.seq SZ.t))
  (#sdfs: Ghost.erased (Seq.seq SZ.t))
  (#sscc: Ghost.erased (Seq.seq SZ.t))
  (#vdt: Ghost.erased SZ.t)
  (#vst: Ghost.erased SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
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
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdfs == SZ.v n /\
      Seq.length sscc == SZ.v n /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
    )
  ensures exists* st' sp' sr' sdfs' sscc' vdt' vst'.
    A.pts_to tag st' **
    A.pts_to parent sp' **
    A.pts_to rank sr' **
    A.pts_to adj #0.5R sadj **
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
      SZ.v n <= Seq.length st' /\
      SZ.v n <= Seq.length sp' /\
      SZ.v n <= Seq.length sr' /\
      Seq.length sdfs' == SZ.v n /\
      Seq.length sscc' == SZ.v n /\
      Impl.is_forest sp' (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st' sp' sr' (SZ.v n))
    )
{
  // Push rep to scc stack and mark as PROCESSING
  let st0 = !scc_top;
  // st0 == 0 (from precondition) and n > 0, so st0 < n
  scc_stk.(st0) <- rep;
  tag.(rep) <- 2sz;
  scc_top := SZ.(st0 +^ 1sz);
  
  // Tag-only update (→PROCESSING): preserves uf_inv
  UFL.tag_update_preserves_uf_inv stag sparent srank (SZ.v n) (SZ.v rep) 2sz;
  
  with st1. assert (A.pts_to tag st1);
  with sp1. assert (A.pts_to parent sp1);
  with sr1. assert (A.pts_to rank sr1);
  
  // Ghost counter for termination
  let mut inner_ctr: SZ.t = 0sz;
  
  // Process all nodes in SCC: walk scc stack, examine each node's fields
  let mut scc_idx: SZ.t = st0;
  while (!scc_idx <^ !scc_top)
  invariant exists* vidx vst2 vdt2 vic st sp sr sdfs2 sscc2.
    R.pts_to scc_idx vidx **
    R.pts_to scc_top vst2 **
    R.pts_to dfs_top vdt2 **
    R.pts_to inner_ctr vic **
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to adj #0.5R sadj **
    A.pts_to dfs_stk sdfs2 **
    A.pts_to scc_stk sscc2 **
    pure (
      SZ.v n > 0 /\
      SZ.v vidx <= SZ.v vst2 /\
      SZ.v vst2 <= SZ.v n /\
      SZ.v vdt2 <= SZ.v n /\
      SZ.v vic <= SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length st == Seq.length stag /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      SZ.v n <= Seq.length st /\
      SZ.v n <= Seq.length sp /\
      SZ.v n <= Seq.length sr /\
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdfs2 == SZ.v n /\
      Seq.length sscc2 == SZ.v n /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st sp sr (SZ.v n))
    )
  decreases (SZ.v n * SZ.v n - SZ.v !inner_ctr)
  {
    let idx = !scc_idx;
    let x = scc_stk.(idx);
    assume_ (pure (SZ.v x < SZ.v n));
    
    // Process all fields of x (iterate through adj row)
    let mut field_idx: SZ.t = 0sz;
    while (!field_idx <^ n)
    invariant exists* vfi st2 sp2 sr2 sdfs3 sscc3 vdt3 vst3.
      R.pts_to field_idx vfi **
      A.pts_to tag st2 **
      A.pts_to parent sp2 **
      A.pts_to rank sr2 **
      A.pts_to adj #0.5R sadj **
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
        SZ.fits (SZ.v n * SZ.v n) /\
        Seq.length st2 == Seq.length stag /\
        Seq.length sp2 == Seq.length sparent /\
        Seq.length sr2 == Seq.length srank /\
        SZ.v n <= Seq.length st2 /\
        SZ.v n <= Seq.length sp2 /\
        SZ.v n <= Seq.length sr2 /\
        SZ.v n * SZ.v n <= Seq.length sadj /\
        Seq.length sdfs3 == SZ.v n /\
        Seq.length sscc3 == SZ.v n /\
        Impl.is_forest sp2 (SZ.v n) /\
        Spec.uf_inv (Impl.to_uf st2 sp2 sr2 (SZ.v n))
      )
    decreases (SZ.v n - SZ.v !field_idx)
    {
      let fi = !field_idx;
      // x < n (from invariant), fi < n (from loop guard), fits(n*n) → adj index valid
      Arith.adj_index_fits (SZ.v n) (SZ.v x) (SZ.v fi);
      let edge_idx = SZ.(x *^ n +^ fi);
      let has_edge = adj.(edge_idx);
      
      if (has_edge <>^ 0sz) {
        dispose_process_field tag parent rank adj dfs_stk dfs_top scc_stk scc_top fi n;
        field_idx := SZ.(fi +^ 1sz);
        ()
      } else {
        field_idx := SZ.(fi +^ 1sz);
        ()
      }
    };
    
    // "Free" this node: set tag to UNMARKED (0)
    tag.(x) <- 0sz;
    with st2. assert (A.pts_to tag st2);
    with sp2. assert (A.pts_to parent sp2);
    with sr2. assert (A.pts_to rank sr2);
    with sdfs2. assert (A.pts_to dfs_stk sdfs2);
    with sscc2. assert (A.pts_to scc_stk sscc2);
    
    // idx+1 <= scc_top (since scc_top can only grow)
    let cur_scc_top = !scc_top;
    let cur_dfs_top = !dfs_top;
    assume_ (pure (
      SZ.v idx < SZ.v cur_scc_top /\
      SZ.fits (SZ.v idx + 1) /\
      Impl.is_forest sp2 (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st2 sp2 sr2 (SZ.v n))
    ));
    
    scc_idx := SZ.(idx +^ 1sz);
    
    let ic = !inner_ctr;
    assume_ (pure (SZ.v ic < SZ.v n * SZ.v n /\ SZ.fits (SZ.v ic + 1)));
    inner_ctr := SZ.(ic +^ 1sz);
    ()
  };
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
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#sadj: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (rep: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
    pure (
      SZ.v n > 0 /\
      SZ.v rep < SZ.v n /\
      SZ.v n <= A.length tag /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      SZ.v n * SZ.v n <= A.length adj /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SZ.fits (SZ.v n * (SZ.v n + 1)) /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length sadj == A.length adj /\
      A.length parent == A.length rank /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
    )
  ensures exists* st sp sr.
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to adj #0.5R sadj **
    pure (
      Seq.length st == Seq.length stag /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st sp sr (SZ.v n))
    )
{
  // Allocate stacks
  let dfs_stk = A.alloc 0sz n;
  let scc_stk = A.alloc 0sz n;
  let mut dfs_top: SZ.t = 0sz;
  let mut scc_top: SZ.t = 0sz;
  
  // Ghost counter for termination
  let mut ghost_ctr: SZ.t = 0sz;
  
  // Push initial rep to dfs stack
  dfs_stk.(0sz) <- rep;
  dfs_top := 1sz;
  
  // Main loop: process SCC DAG
  while (!dfs_top >^ 0sz)
  invariant exists* vdt vst vgc st sp sr sdfs sscc.
    R.pts_to dfs_top vdt **
    R.pts_to scc_top vst **
    R.pts_to ghost_ctr vgc **
    A.pts_to tag st **
    A.pts_to parent sp **
    A.pts_to rank sr **
    A.pts_to adj #0.5R sadj **
    A.pts_to dfs_stk sdfs **
    A.pts_to scc_stk sscc **
    pure (
      SZ.v n > 0 /\
      SZ.v vdt <= SZ.v n /\
      SZ.v vst <= SZ.v n /\
      SZ.v vgc <= SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length st == Seq.length stag /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      SZ.v n <= Seq.length st /\
      SZ.v n <= Seq.length sp /\
      SZ.v n <= Seq.length sr /\
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdfs == SZ.v n /\
      Seq.length sscc == SZ.v n /\
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st sp sr (SZ.v n))
    )
  decreases (SZ.v n - SZ.v !ghost_ctr)
  {
    // Pop from dfs stack
    let dt = !dfs_top;
    let top_idx = SZ.(dt -^ 1sz);
    let scc_rep = dfs_stk.(top_idx);
    dfs_top := top_idx;
    
    assume_ (pure (SZ.v scc_rep < SZ.v n));
    
    // Reset scc stack for this SCC
    scc_top := 0sz;
    
    // Process the SCC
    dispose_process_scc tag parent rank adj dfs_stk dfs_top scc_stk scc_top scc_rep n;
    
    // Tick ghost counter
    let gc = !ghost_ctr;
    assume_ (pure (SZ.v gc < SZ.v n /\ SZ.fits (SZ.v gc + 1)));
    ghost_ctr := SZ.(gc +^ 1sz);
    ()
  };
  
  A.free dfs_stk;
  A.free scc_stk;
  ()
}
```
#pop-options
