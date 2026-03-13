(*
   ISMM Freeze — Imperative Pulse Implementation
   
   Implements the freeze algorithm from paper §3.1, Fig. 2.
   Uses iterative DFS with pending stack for SCC detection, fused with union-find.
   
   Helpers factored out to avoid Pulse unification issues with conditional branches
   (same pattern as CLRS.Ch22.DFS.Impl — see line 402 there).
   
   Proof obligations marked with assume_ are delegated to ISMM.Freeze.Lemmas.
*)
module ISMM.Freeze.Impl
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


(* ---------- Helper: Post-order SCC check ----------
   After all edges of x explored, check if x is an SCC root.
   If find(x) == top of pending, finalize SCC with RC(1). *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
```pulse
fn handle_post_order
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (refcount: A.array SZ.t)
  (pending_stk: A.array SZ.t)
  (pending_top: ref SZ.t)
  (x: SZ.t) (n: SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (#spd: Ghost.erased (Seq.seq SZ.t))
  (#vpt: Ghost.erased SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to refcount src **
    A.pts_to pending_stk spd **
    R.pts_to pending_top vpt **
    pure (
      SZ.v x < SZ.v n /\
      SZ.v n > 0 /\
      SZ.v vpt <= SZ.v n /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sparent /\
      SZ.v n <= Seq.length srank /\
      SZ.v n <= Seq.length src /\
      Seq.length sparent == Seq.length srank /\
      Seq.length spd == SZ.v n /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      SZ.v vpt <= Arith.count_nonzero stag (SZ.v n)
    )
  ensures exists* st' sp' sr' src' vpt'.
    A.pts_to tag st' **
    A.pts_to parent sp' **
    A.pts_to rank sr' **
    A.pts_to refcount src' **
    A.pts_to pending_stk spd **
    R.pts_to pending_top vpt' **
    pure (
      SZ.v vpt' <= SZ.v n /\
      Seq.length st' == Seq.length stag /\
      Seq.length sp' == Seq.length sparent /\
      Seq.length sr' == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      Seq.length sp' == Seq.length sr' /\
      SZ.v n <= Seq.length st' /\
      SZ.v n <= Seq.length sp' /\
      SZ.v n <= Seq.length sr' /\
      Impl.is_forest sp' (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st' sp' sr' (SZ.v n)) /\
      SZ.v vpt' <= Arith.count_nonzero st' (SZ.v n) /\
      Arith.count_nonzero st' (SZ.v n) >= Arith.count_nonzero stag (SZ.v n)
    )
{
  let pt = !pending_top;
  if (pt >^ 0sz) {
    let rep_x = Impl.find_set parent x n #sparent #stag #srank;
    with sp1. assert (A.pts_to parent sp1);
    
    let top_p = pending_stk.(SZ.(pt -^ 1sz));
    
    // Read current values
    let cur_tag = tag.(rep_x);
    let cur_rc = refcount.(rep_x);
    
    // Compute new values (conditionally, avoiding branching resource mismatch)
    let is_scc_root = (top_p = rep_x);
    let new_tag = (if is_scc_root then 3sz else cur_tag);
    let new_rc = (if is_scc_root then 1sz else cur_rc);
    let new_pt = (if is_scc_root then SZ.(pt -^ 1sz) else pt);
    
    // Always write
    tag.(rep_x) <- new_tag;
    refcount.(rep_x) <- new_rc;
    pending_top := new_pt;
    
    // Tag-only update preserves uf_inv (rank unchanged)
    with st1. assert (A.pts_to tag st1);
    with src1. assert (A.pts_to refcount src1);
    UFL.tag_update_preserves_uf_inv stag sp1 srank (SZ.v n) (SZ.v rep_x) new_tag;
    // count_nonzero doesn't decrease: new_tag is either 3sz (nonzero) or cur_tag
    Arith.count_nonzero_write_nondec stag (SZ.v n) (SZ.v rep_x) new_tag;
    ()
  } else { () }
}
```
#pop-options


(* ---------- Helper: Process a tree edge ----------
   Mark y as RANK, push to pending and DFS stacks. *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
```pulse
fn handle_tree_edge
  (tag: A.array SZ.t)
  (dfs_node: A.array SZ.t) (dfs_edge: A.array SZ.t)
  (dfs_top: ref SZ.t)
  (pending_stk: A.array SZ.t)
  (pending_top: ref SZ.t)
  (y: SZ.t) (n: SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sdn: Ghost.erased (Seq.seq SZ.t))
  (#sde: Ghost.erased (Seq.seq SZ.t))
  (#spd: Ghost.erased (Seq.seq SZ.t))
  (#vdt: Ghost.erased SZ.t)
  (#vpt: Ghost.erased SZ.t)
  (sp_ghost: Ghost.erased (Seq.seq SZ.t))
  (sr_ghost: Ghost.erased (Seq.seq SZ.t))
  requires
    A.pts_to tag stag **
    A.pts_to dfs_node sdn **
    A.pts_to dfs_edge sde **
    R.pts_to dfs_top vdt **
    A.pts_to pending_stk spd **
    R.pts_to pending_top vpt **
    pure (
      SZ.v y < SZ.v n /\
      SZ.v n > 0 /\
      SZ.v vdt <= SZ.v n /\
      SZ.v vpt <= SZ.v n /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sp_ghost /\
      SZ.v n <= Seq.length sr_ghost /\
      Seq.length sdn == SZ.v n /\
      Seq.length sde == SZ.v n /\
      Seq.length spd == SZ.v n /\
      Impl.is_forest sp_ghost (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp_ghost sr_ghost (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sdn i)} i < SZ.v vdt ==> SZ.v (Seq.index sdn i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sde i)} i < SZ.v vdt ==> SZ.v (Seq.index sde i) <= SZ.v n) /\
      SZ.v (Seq.index stag (SZ.v y)) == 0 /\
      SZ.v vpt <= Arith.count_nonzero stag (SZ.v n) /\
      SZ.v vdt <= Arith.count_nonzero stag (SZ.v n)
    )
  ensures exists* st' sdn' sde' spd' vdt' vpt'.
    A.pts_to tag st' **
    A.pts_to dfs_node sdn' **
    A.pts_to dfs_edge sde' **
    R.pts_to dfs_top vdt' **
    A.pts_to pending_stk spd' **
    R.pts_to pending_top vpt' **
    pure (
      SZ.v vdt' <= SZ.v n /\
      SZ.v vpt' <= SZ.v n /\
      Seq.length st' == Seq.length stag /\
      SZ.v n <= Seq.length st' /\
      Impl.is_forest sp_ghost (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st' sp_ghost sr_ghost (SZ.v n)) /\
      Seq.length sdn' == SZ.v n /\
      Seq.length sde' == SZ.v n /\
      Seq.length spd' == SZ.v n /\
      (forall (i:nat). {:pattern (Seq.index sdn' i)} i < SZ.v vdt' ==> SZ.v (Seq.index sdn' i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sde' i)} i < SZ.v vdt' ==> SZ.v (Seq.index sde' i) <= SZ.v n) /\
      SZ.v vpt' <= Arith.count_nonzero st' (SZ.v n) /\
      SZ.v vdt' <= Arith.count_nonzero st' (SZ.v n)
    )
{
  // Derive stack bounds from count_nonzero
  Arith.count_nonzero_lt_when_zero stag (SZ.v n) (SZ.v y);
  Arith.count_nonzero_set_nz stag (SZ.v n) (SZ.v y) 1sz;
  
  tag.(y) <- 1sz;
  // Tag-only update preserves uf_inv
  UFL.tag_update_preserves_uf_inv stag sp_ghost sr_ghost (SZ.v n) (SZ.v y) 1sz;
  
  let pt2 = !pending_top;
  // pt2 = vpt <= count_nonzero(stag, n) < n  (from lemma above)
  pending_stk.(pt2) <- y;
  pending_top := SZ.(pt2 +^ 1sz);
  
  let dt2 = !dfs_top;
  // dt2 = vdt <= count_nonzero(stag, n) < n  (from lemma above)
  dfs_node.(dt2) <- y;
  dfs_edge.(dt2) <- 0sz;
  dfs_top := SZ.(dt2 +^ 1sz);
  
  // Postcondition count_nonzero:
  // count_nonzero(Seq.upd stag y 1, n) == count_nonzero(stag, n) + 1
  // vpt' = pt2 + 1 <= count_nonzero(stag, n) + 1 = count_nonzero(st', n)
  // vdt' = dt2 + 1 <= count_nonzero(stag, n) + 1 = count_nonzero(st', n)
  
  with sdn'. assert (A.pts_to dfs_node sdn');
  with sde'. assert (A.pts_to dfs_edge sde');
  Arith.seq_upd_content_bound sdn (SZ.v vdt) (SZ.v n) y;
  Arith.seq_upd_content_le_bound sde (SZ.v vdt) (SZ.v n) SZ.(0sz);
  ()
}
```
#pop-options


(* ---------- Helper: Handle back/cross/noop edge ----------
   Called when tag_rep != 0 (not a tree edge).
   Factored out to avoid Pulse conditional branch unification issues. *)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
```pulse
fn handle_non_tree_edge
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (refcount: A.array SZ.t)
  (x: SZ.t) (y: SZ.t) (tag_rep: SZ.t) (rep_y: SZ.t) (n: SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sp1: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sp1 **
    A.pts_to rank srank **
    A.pts_to refcount src **
    pure (
      SZ.v x < SZ.v n /\
      SZ.v y < SZ.v n /\
      SZ.v rep_y < SZ.v n /\
      SZ.v n > 0 /\
      SZ.v n <= Seq.length sp1 /\
      SZ.v n <= Seq.length srank /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length src /\
      Seq.length sp1 == Seq.length srank /\
      SZ.v rep_y < Seq.length srank /\
      SZ.v (Seq.index sp1 (SZ.v rep_y)) == SZ.v rep_y /\
      Impl.is_forest sp1 (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp1 srank (SZ.v n))
    )
  ensures exists* sp' sr' src'.
    A.pts_to parent sp' **
    A.pts_to rank sr' **
    A.pts_to refcount src' **
    pure (
      Seq.length sp' == Seq.length sp1 /\
      Seq.length sr' == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      Seq.length sp' == Seq.length sr' /\
      SZ.v n <= Seq.length sp' /\
      SZ.v n <= Seq.length sr' /\
      Impl.is_forest sp' (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sp' sr' (SZ.v n))
    )
{
  if (tag_rep = 1sz) {
    // BACK EDGE: union x with y
    // Seq.length sp1 == Seq.length srank (from precondition)
    Spec.rank_bounded_all (Impl.to_uf stag sp1 srank (SZ.v n));
    Impl.union_set parent rank #sp1 #srank #stag x y n;
    ()
  } else {
    if (tag_rep = 3sz) {
      // CROSS EDGE: incref (refcount, not rank)
      let rc = refcount.(rep_y);
      assume_ (pure (SZ.fits (SZ.v rc + 1)));
      refcount.(rep_y) <- SZ.(rc +^ 1sz);
      with src1. assert (A.pts_to refcount src1);
      ()
    } else { () }
  }
}
```
#pop-options


(* ---------- Helper: Process an edge (tree/back/cross) ----------
   Determines edge type and processes accordingly. *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
```pulse
fn handle_edge
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (refcount: A.array SZ.t)
  (dfs_node: A.array SZ.t) (dfs_edge: A.array SZ.t)
  (dfs_top: ref SZ.t)
  (pending_stk: A.array SZ.t)
  (pending_top: ref SZ.t)
  (x: SZ.t) (e: SZ.t) (top_idx: SZ.t) (n: SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#sadj: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (#sdn: Ghost.erased (Seq.seq SZ.t))
  (#sde: Ghost.erased (Seq.seq SZ.t))
  (#spd: Ghost.erased (Seq.seq SZ.t))
  (#vdt: Ghost.erased SZ.t)
  (#vpt: Ghost.erased SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src **
    A.pts_to dfs_node sdn **
    A.pts_to dfs_edge sde **
    R.pts_to dfs_top vdt **
    A.pts_to pending_stk spd **
    R.pts_to pending_top vpt **
    pure (
      SZ.v x < SZ.v n /\
      SZ.v e < SZ.v n /\
      SZ.v top_idx < SZ.v n /\
      SZ.v n > 0 /\
      SZ.v vdt <= SZ.v n /\
      SZ.v vpt <= SZ.v n /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sparent /\
      SZ.v n <= Seq.length srank /\
      SZ.v n <= Seq.length src /\
      Seq.length sparent == Seq.length srank /\
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdn == SZ.v n /\
      Seq.length sde == SZ.v n /\
      Seq.length spd == SZ.v n /\
      SZ.v top_idx < Seq.length sde /\
      SZ.fits (SZ.v x * SZ.v n + SZ.v e) /\
      SZ.v x * SZ.v n + SZ.v e < Seq.length sadj /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sdn i)} i < SZ.v vdt ==> SZ.v (Seq.index sdn i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sde i)} i < SZ.v vdt ==> SZ.v (Seq.index sde i) <= SZ.v n) /\
      SZ.v vpt <= Arith.count_nonzero stag (SZ.v n) /\
      SZ.v vdt <= Arith.count_nonzero stag (SZ.v n)
    )
  ensures exists* st' sp' sr' src' sdn' sde' spd' vdt' vpt'.
    A.pts_to tag st' **
    A.pts_to parent sp' **
    A.pts_to rank sr' **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src' **
    A.pts_to dfs_node sdn' **
    A.pts_to dfs_edge sde' **
    R.pts_to dfs_top vdt' **
    A.pts_to pending_stk spd' **
    R.pts_to pending_top vpt' **
    pure (
      SZ.v vdt' <= SZ.v n /\
      SZ.v vpt' <= SZ.v n /\
      Seq.length st' == Seq.length stag /\
      Seq.length sp' == Seq.length sparent /\
      Seq.length sr' == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      Seq.length sp' == Seq.length sr' /\
      SZ.v n <= Seq.length st' /\
      SZ.v n <= Seq.length sp' /\
      SZ.v n <= Seq.length sr' /\
      Seq.length sdn' == SZ.v n /\
      Seq.length sde' == SZ.v n /\
      Seq.length spd' == SZ.v n /\
      Impl.is_forest sp' (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st' sp' sr' (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sdn' i)} i < SZ.v vdt' ==> SZ.v (Seq.index sdn' i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sde' i)} i < SZ.v vdt' ==> SZ.v (Seq.index sde' i) <= SZ.v n) /\
      SZ.v vpt' <= Arith.count_nonzero st' (SZ.v n) /\
      SZ.v vdt' <= Arith.count_nonzero st' (SZ.v n)
    )
{
  // Advance edge pointer
  dfs_edge.(top_idx) <- SZ.(e +^ 1sz);
  with sde1. assert (A.pts_to dfs_edge sde1);
  
  let idx = SZ.(x *^ n +^ e);
  let has_edge = adj.(idx);
  
  if (has_edge <>^ 0sz) {
    let y = e;
    
    let rep_y = Impl.find_set parent y n #sparent #stag #srank;
    with sp1. assert (A.pts_to parent sp1);
    
    let tag_rep = tag.(rep_y);
    
    if (tag_rep = 0sz) {
      // TREE EDGE: mark rep_y as RANK, push to stacks
      // tag[rep_y] == 0 from the check above
      handle_tree_edge tag dfs_node dfs_edge dfs_top pending_stk pending_top rep_y n
        #stag #sdn #sde1 #spd #vdt #vpt sp1 srank;
      ()
    } else {
      // Not a tree edge — delegate to helper (avoids branch unification issues)
      handle_non_tree_edge parent rank refcount x y tag_rep rep_y n #stag #sp1 #srank #src;
      ()
    }
  } else { () }
}
```
#pop-options


(* ---------- Helper: One step of the DFS loop ----------
   Factored out to avoid Pulse branch unification issues between
   post-order (handle_post_order) and edge processing (handle_edge). *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
```pulse
fn freeze_step
  (tag: A.array SZ.t)
  (parent: A.array SZ.t)
  (rank: A.array SZ.t)
  (adj: A.array SZ.t)
  (refcount: A.array SZ.t)
  (dfs_node: A.array SZ.t) (dfs_edge: A.array SZ.t)
  (dfs_top: ref SZ.t)
  (pending_stk: A.array SZ.t)
  (pending_top: ref SZ.t)
  (n: SZ.t)
  (#stag: Ghost.erased (Seq.seq SZ.t))
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (#sadj: Ghost.erased (Seq.seq SZ.t))
  (#src: Ghost.erased (Seq.seq SZ.t))
  (#sdn: Ghost.erased (Seq.seq SZ.t))
  (#sde: Ghost.erased (Seq.seq SZ.t))
  (#spd: Ghost.erased (Seq.seq SZ.t))
  (#vdt: Ghost.erased SZ.t)
  (#vpt: Ghost.erased SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src **
    A.pts_to dfs_node sdn **
    A.pts_to dfs_edge sde **
    R.pts_to dfs_top vdt **
    A.pts_to pending_stk spd **
    R.pts_to pending_top vpt **
    pure (
      SZ.v vdt > 0 /\
      SZ.v vdt <= SZ.v n /\
      SZ.v vpt <= SZ.v n /\
      SZ.v n > 0 /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length stag == A.length tag /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank /\
      Seq.length src == A.length refcount /\
      Seq.length sparent == Seq.length srank /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sparent /\
      SZ.v n <= Seq.length srank /\
      SZ.v n <= Seq.length src /\
      SZ.v n * SZ.v n <= Seq.length sadj /\
      Seq.length sdn == SZ.v n /\
      Seq.length sde == SZ.v n /\
      Seq.length spd == SZ.v n /\
      Impl.is_forest sparent (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sdn i)} i < SZ.v vdt ==> SZ.v (Seq.index sdn i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sde i)} i < SZ.v vdt ==> SZ.v (Seq.index sde i) <= SZ.v n) /\
      SZ.v vpt <= Arith.count_nonzero stag (SZ.v n) /\
      SZ.v vdt <= Arith.count_nonzero stag (SZ.v n)
    )
  ensures exists* st' sp' sr' src' sdn' sde' spd' vdt' vpt'.
    A.pts_to tag st' **
    A.pts_to parent sp' **
    A.pts_to rank sr' **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src' **
    A.pts_to dfs_node sdn' **
    A.pts_to dfs_edge sde' **
    R.pts_to dfs_top vdt' **
    A.pts_to pending_stk spd' **
    R.pts_to pending_top vpt' **
    pure (
      SZ.v vdt' <= SZ.v n /\
      SZ.v vpt' <= SZ.v n /\
      Seq.length st' == Seq.length stag /\
      Seq.length sp' == Seq.length sparent /\
      Seq.length sr' == Seq.length srank /\
      Seq.length src' == Seq.length src /\
      Seq.length sp' == Seq.length sr' /\
      SZ.v n <= Seq.length st' /\
      SZ.v n <= Seq.length sp' /\
      SZ.v n <= Seq.length sr' /\
      Seq.length sdn' == SZ.v n /\
      Seq.length sde' == SZ.v n /\
      Seq.length spd' == SZ.v n /\
      Impl.is_forest sp' (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st' sp' sr' (SZ.v n)) /\
      (forall (i:nat). {:pattern (Seq.index sdn' i)} i < SZ.v vdt' ==> SZ.v (Seq.index sdn' i) < SZ.v n) /\
      (forall (i:nat). {:pattern (Seq.index sde' i)} i < SZ.v vdt' ==> SZ.v (Seq.index sde' i) <= SZ.v n) /\
      SZ.v vpt' <= Arith.count_nonzero st' (SZ.v n) /\
      SZ.v vdt' <= Arith.count_nonzero st' (SZ.v n)
    )
{
  let dt = !dfs_top;
  let top_idx = SZ.(dt -^ 1sz);
  let x = dfs_node.(top_idx);
  let e = dfs_edge.(top_idx);
  
  // DFS stack content: x < n and e <= n from invariants; top_idx < n from dt > 0 /\ dt <= n
  // fits(x*n + n) follows from x < n and fits(n*n)
  // When e < n: fits(x*n + e) and x*n + e < n*n from adj_index_fits
  
  if (e >=^ n) {
    // POST-ORDER: pop DFS stack, check pending
    dfs_top := top_idx;
    handle_post_order tag parent rank refcount pending_stk pending_top x n;
    ()
  } else {
    // PROCESS EDGE
    handle_edge tag parent rank adj refcount dfs_node dfs_edge dfs_top
      pending_stk pending_top x e top_idx n;
    ()
  }
}
```
#pop-options


(* ---------- Main freeze function ---------- *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
```pulse
fn freeze
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
  (root: SZ.t)
  requires
    A.pts_to tag stag **
    A.pts_to parent sparent **
    A.pts_to rank srank **
    A.pts_to adj #0.5R sadj **
    A.pts_to refcount src **
    pure (
      SZ.v n > 0 /\
      SZ.v root < SZ.v n /\
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
      Spec.uf_inv (Impl.to_uf stag sparent srank (SZ.v n))
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
      Impl.is_forest sp (SZ.v n) /\
      Spec.uf_inv (Impl.to_uf st sp sr (SZ.v n))
    )
{
  // Allocate DFS work stack
  let dfs_node = A.alloc 0sz n;
  let dfs_edge = A.alloc 0sz n;
  let mut dfs_top: SZ.t = 0sz;
  
  // Allocate pending stack  
  let pending_stk = A.alloc 0sz n;
  let mut pending_top: SZ.t = 0sz;
  
  let root_tag = tag.(root);
  
  if (root_tag = 0sz) {
    // Root is UNMARKED — perform freeze DFS
    tag.(root) <- 1sz;
    pending_stk.(0sz) <- root;
    pending_top := 1sz;
    dfs_node.(0sz) <- root;
    dfs_edge.(0sz) <- 0sz;
    dfs_top := 1sz;
    
    // Tag-only update (UNMARKED→RANK): preserves uf_inv
    UFL.tag_update_preserves_uf_inv stag sparent srank (SZ.v n) (SZ.v root) 1sz;
    // count_nonzero(st0, n) >= 1 since root was 0 and is now 1
    Arith.count_nonzero_set_nz stag (SZ.v n) (SZ.v root) 1sz;
    with st0. assert (A.pts_to tag st0);
    with sp0. assert (A.pts_to parent sp0);
    with sr0. assert (A.pts_to rank sr0);
    
    // Main DFS loop
    while (!dfs_top >^ 0sz)
    invariant exists* vdt vpt st sp sr src_i sdn sde spd.
      R.pts_to dfs_top vdt **
      R.pts_to pending_top vpt **
      A.pts_to tag st **
      A.pts_to parent sp **
      A.pts_to rank sr **
      A.pts_to adj #0.5R sadj **
      A.pts_to refcount src_i **
      A.pts_to dfs_node sdn **
      A.pts_to dfs_edge sde **
      A.pts_to pending_stk spd **
      pure (
        SZ.v vdt <= SZ.v n /\
        SZ.v vpt <= SZ.v n /\
        SZ.fits (SZ.v n * SZ.v n) /\
        Seq.length st == Seq.length stag /\
        Seq.length sp == Seq.length sparent /\
        Seq.length sr == Seq.length srank /\
        Seq.length src_i == Seq.length src /\
        Seq.length sp == Seq.length sr /\
        SZ.v n <= Seq.length st /\
        SZ.v n <= Seq.length sp /\
        SZ.v n <= Seq.length sr /\
        SZ.v n <= Seq.length src_i /\
        Seq.length sdn == SZ.v n /\
        Seq.length sde == SZ.v n /\
        Seq.length spd == SZ.v n /\
        Impl.is_forest sp (SZ.v n) /\
        Spec.uf_inv (Impl.to_uf st sp sr (SZ.v n)) /\
        (forall (i:nat). {:pattern (Seq.index sdn i)} i < SZ.v vdt ==> SZ.v (Seq.index sdn i) < SZ.v n) /\
        (forall (i:nat). {:pattern (Seq.index sde i)} i < SZ.v vdt ==> SZ.v (Seq.index sde i) <= SZ.v n) /\
        SZ.v vpt <= Arith.count_nonzero st (SZ.v n) /\
        SZ.v vdt <= Arith.count_nonzero st (SZ.v n)
      )
    {
      freeze_step tag parent rank adj refcount dfs_node dfs_edge dfs_top
        pending_stk pending_top n;
      ()
    };
    A.free dfs_node;
    A.free dfs_edge;
    A.free pending_stk;
    ()
  } else {
    if (root_tag = 3sz) {
      // Already RC: incref (refcount, not rank)
      let rep = Impl.find_set parent root n #sparent #stag #srank;
      with sp1. assert (A.pts_to parent sp1);
      let rc = refcount.(rep);
      assume_ (pure (SZ.fits (SZ.v rc + 1)));
      refcount.(rep) <- SZ.(rc +^ 1sz);
      with src1. assert (A.pts_to refcount src1);
      A.free dfs_node;
      A.free dfs_edge;
      A.free pending_stk;
      ()
    } else {
      A.free dfs_node;
      A.free dfs_edge;
      A.free pending_stk;
      ()
    }
  }
}
```
#pop-options
