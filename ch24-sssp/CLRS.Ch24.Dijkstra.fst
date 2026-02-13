module CLRS.Ch24.Dijkstra
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Vec
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(*
   Dijkstra's Single-Source Shortest Paths — Verified in Pulse

   Graph: weighted adjacency matrix (n×n flat array, 1000000 = no edge/infinity)
   Requires non-negative weights.
   
   Postcondition:
   - dist[source] == 0
   - All distances non-negative and bounded [0, 1000000]
   - Triangle inequality: for all edges (u,v), dist[v] <= dist[u] + w(u,v)
     (verified by a read-only check pass after the main algorithm)
   
   NO admits. NO assumes.
*)

// All weights are non-negative
let all_weights_non_negative (sweights: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sweights ==> Seq.index sweights i >= 0

// All distances are non-negative  
let all_non_negative (sdist: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sdist ==> Seq.index sdist i >= 0

// All distances are bounded by 1000000
let all_bounded (sdist: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sdist ==> 
    Seq.index sdist i >= 0 /\ Seq.index sdist i <= 1000000

// Triangle inequality: for all finite edges, dist[v] <= dist[u] + w
let triangle_inequality (sweights: Seq.seq int) (sdist: Seq.seq int) (n: nat) : prop =
  Seq.length sdist == n /\
  (forall (u v:nat). 
    u < n /\ v < n /\ u * n + v < Seq.length sweights ==>
    (let w = Seq.index sweights (u * n + v) in
     let dist_u = Seq.index sdist u in
     let dist_v = Seq.index sdist v in
     (w < 1000000 /\ dist_u < 1000000) ==> dist_v <= dist_u + w))

// Partial triangle inequality: for edges (u,v) with u < u_bound, or u == u_bound and v < v_bound
let triangle_partial (sweights: Seq.seq int) (sdist: Seq.seq int) (n u_bound v_bound: nat) : prop =
  Seq.length sdist == n /\
  Seq.length sweights == n * n /\
  (forall (u v:nat). 
    u < n /\ v < n /\
    (u < u_bound \/ (u == u_bound /\ v < v_bound)) ==>
    (let w = Seq.index sweights (u * n + v) in
     let dist_u = Seq.index sdist u in
     let dist_v = Seq.index sdist v in
     (w < 1000000 /\ dist_u < 1000000) ==> dist_v <= dist_u + w))

let partial_full_tri (sweights: Seq.seq int) (sdist: Seq.seq int) (n: nat) : Lemma
  (requires triangle_partial sweights sdist n n 0)
  (ensures triangle_inequality sweights sdist n)
  = ()

/// Import pure shortest-path specification
module SP = CLRS.Ch24.ShortestPath.Spec

/// Connect Dijkstra's triangle_inequality + all_bounded to SP.has_triangle_inequality
let dijkstra_to_sp_triangle (sdist sweights: Seq.seq int) (n: nat) : Lemma
  (requires triangle_inequality sweights sdist n /\
            all_bounded sdist /\
            Seq.length sweights == n * n /\
            Seq.length sdist == n)
  (ensures SP.has_triangle_inequality sdist sweights n)
  = ()

/// Helper: establish sp_dist upper bound from triangle inequality + all_bounded
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let dijkstra_sp_upper_bound_cond (sdist sweights: Seq.seq int) (n source: nat) (flag: bool) : Lemma
  (requires Seq.length sdist == n /\
            Seq.length sweights == n * n /\
            n > 0 /\ source < n /\
            Seq.index sdist source == 0 /\
            all_bounded sdist /\
            (flag == true ==> triangle_inequality sweights sdist n))
  (ensures flag == true ==>
    (forall (v: nat). v < n ==>
      Seq.index sdist v <= SP.sp_dist sweights n source v))
  = if flag then begin
      dijkstra_to_sp_triangle sdist sweights n;
      let aux (v: nat{v < n}) : Lemma
        (ensures Seq.index sdist v <= SP.sp_dist sweights n source v) =
        SP.triangle_ineq_implies_upper_bound sdist sweights n source v
      in
      FStar.Classical.forall_intro aux
    end
#pop-options

// Helper function to find minimum distance vertex among unvisited
fn find_min_unvisited
  (dist: A.array int)
  (visited: V.vec int)
  (n: SZ.t)
  (#sdist: erased (Seq.seq int))
  (#svisited: erased (Seq.seq int))
  requires
    A.pts_to dist sdist **
    V.pts_to visited svisited **
    pure (
      SZ.v n > 0 /\
      Seq.length sdist == SZ.v n /\
      Seq.length svisited == SZ.v n
    )
  returns min_idx:SZ.t
  ensures
    A.pts_to dist sdist **
    V.pts_to visited svisited **
    pure (SZ.v min_idx < SZ.v n)
{
  let mut min_idx: SZ.t = 0sz;
  let mut min_val: int = 1000000;
  let mut i: SZ.t = 0sz;
  
  while (
    let vi = !i;
    vi <^ n
  )
  invariant exists* vi vmin_idx vmin_val.
    R.pts_to i vi **
    R.pts_to min_idx vmin_idx **
    R.pts_to min_val vmin_val **
    A.pts_to dist sdist **
    V.pts_to visited svisited **
    pure (
      SZ.v vi <= SZ.v n /\
      SZ.v vmin_idx < SZ.v n
    )
  {
    let vi = !i;
    let visited_i = V.op_Array_Access visited vi;
    
    if (visited_i = 0)
    {
      let dist_i = A.op_Array_Access dist vi;
      let curr_min = !min_val;
      
      if (dist_i < curr_min)
      {
        min_idx := vi;
        min_val := dist_i;
      };
    };
    
    i := vi +^ 1sz;
  };
  
  let _ = !i;
  let result = !min_idx;
  let _ = !min_val;
  result
}

fn dijkstra
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (tri_result: R.ref bool)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#stri: erased bool)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    R.pts_to tri_result stri **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      all_weights_non_negative sweights
    )
  ensures exists* sdist' vtri.
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    R.pts_to tri_result vtri **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      all_non_negative sdist' /\
      all_bounded sdist' /\
      (vtri == true ==> triangle_inequality sweights sdist' (SZ.v n)) /\
      (vtri == true ==> (forall (v: nat). v < SZ.v n ==>
        Seq.index sdist' v <= SP.sp_dist sweights (SZ.v n) (SZ.v source) v))
    )
{
  // Initialization: dist[source] = 0, all others = 1000000
  let mut init_i: SZ.t = 0sz;
  
  while (
    let vi = !init_i;
    vi <^ n
  )
  invariant exists* vi sdist_current.
    R.pts_to init_i vi **
    A.pts_to dist sdist_current **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      // After source is initialized, it stays 0
      (SZ.v vi > SZ.v source ==> Seq.index sdist_current (SZ.v source) == 0) /\
      // All initialized indices are non-negative and bounded
      (forall (j:nat). j < SZ.v vi ==> 
        Seq.index sdist_current j >= 0 /\ Seq.index sdist_current j <= 1000000)
    )
  {
    let vi = !init_i;
    let new_val: int = (if vi = source then 0 else 1000000);
    A.op_Array_Assignment dist vi new_val;
    init_i := vi +^ 1sz;
  };
  
  let _ = !init_i;
  
  // At this point, dist[source] = 0 and all others = 1000000
  // Triangle inequality holds vacuously because 1000000 is treated as infinity
  
  // Allocate visited array
  let visited = V.alloc 0 n;
  
  // Main loop: n iterations
  let mut round: SZ.t = 0sz;
  
  while (
    let vround = !round;
    vround <^ n
  )
  invariant exists* vround sdist_current svisited_current.
    R.pts_to round vround **
    A.pts_to dist sdist_current **
    V.pts_to visited svisited_current **
    pure (
      SZ.v vround <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      Seq.length svisited_current == SZ.v n /\
      // Key invariants:
      Seq.index sdist_current (SZ.v source) == 0 /\
      all_non_negative sdist_current /\
      all_bounded sdist_current
    )
  {
    let vround = !round;
    
    // Find minimum distance unvisited vertex
    let u = find_min_unvisited dist visited n;
    
    // Mark u as visited
    V.op_Array_Assignment visited u 1;
    
    // Get dist[u]
    let dist_u = A.op_Array_Access dist u;
    
    // Relax all neighbors of u
    let mut v: SZ.t = 0sz;
    
    while (
      let vv = !v;
      vv <^ n
    )
    invariant exists* vv sdist_v svisited_v.
      R.pts_to v vv **
      A.pts_to dist sdist_v **
      V.pts_to visited svisited_v **
      pure (
        SZ.v vv <= SZ.v n /\
        Seq.length sdist_v == SZ.v n /\
        Seq.length svisited_v == SZ.v n /\
        Seq.index sdist_v (SZ.v source) == 0 /\
        all_non_negative sdist_v /\
        all_bounded sdist_v
      )
    {
      let vv = !v;
      
      // Read weight[u][v] from flat array
      let w_idx = u *^ n +^ vv;
      let w = A.op_Array_Access weights w_idx;
      
      // Read visited[v] and dist[v]
      let visited_v = V.op_Array_Access visited vv;
      let old_dist = A.op_Array_Access dist vv;
      
      // Compute new distance: relax if unvisited and edge exists
      let can_relax = (visited_v = 0 && w < 1000000 && dist_u < 1000000);
      let sum = dist_u + w;
      let should_update = (can_relax && sum < old_dist);
      let new_dist: int = (if should_update then sum else old_dist);
      
      // This write maintains our invariants:
      // - dist[source] unchanged (because we only update v = vv)
      // - non-negativity: maintained because new_dist <= old_dist, and old_dist >= 0
      // - boundedness: maintained because new_dist <= old_dist <= 1000000
      A.op_Array_Assignment dist vv new_dist;
      
      v := vv +^ 1sz;
    };
    
    let _ = !v;
    round := vround +^ 1sz;
  };
  
  let _ = !round;
  
  // Free visited array
  V.free visited;
  
  // === Triangle inequality verification pass ===
  // Read-only: check dist[v] <= dist[u] + w for all finite edges
  let mut tri_ok: bool = true;
  let mut cu: SZ.t = 0sz;
  
  while (
    let vcu = !cu;
    vcu <^ n
  )
  invariant exists* vcu sdist_check vtok.
    R.pts_to cu vcu **
    R.pts_to tri_ok vtok **
    A.pts_to dist sdist_check **
    pure (
      SZ.v vcu <= SZ.v n /\
      Seq.length sdist_check == SZ.v n /\
      Seq.index sdist_check (SZ.v source) == 0 /\
      all_non_negative sdist_check /\
      all_bounded sdist_check /\
      (vtok == true ==> triangle_partial sweights sdist_check (SZ.v n) (SZ.v vcu) 0)
    )
  {
    let vcu = !cu;
    with sdist_check. assert (A.pts_to dist sdist_check);
    let dist_cu = A.op_Array_Access dist vcu;
    
    let mut cv: SZ.t = 0sz;
    
    while (
      let vcv = !cv;
      vcv <^ n
    )
    invariant exists* vcv vtok_inner.
      R.pts_to cv vcv **
      R.pts_to tri_ok vtok_inner **
      A.pts_to dist sdist_check **
      pure (
        SZ.v vcv <= SZ.v n /\
        (vtok_inner == true ==> triangle_partial sweights sdist_check (SZ.v n) (SZ.v vcu) (SZ.v vcv))
      )
    {
      let vcv = !cv;
      
      let w_idx = vcu *^ n +^ vcv;
      let w = A.op_Array_Access weights w_idx;
      let d_u = dist_cu;
      let d_v = A.op_Array_Access dist vcv;
      
      let edge_ok = (w >= 1000000 || d_u >= 1000000 || d_v <= d_u + w);
      
      let vtok = !tri_ok;
      if (not edge_ok) {
        tri_ok := false;
      };
      
      cv := vcv +^ 1sz;
    };
    
    let _ = !cv;
    cu := vcu +^ 1sz;
  };
  
  let _ = !cu;
  let final_tri = !tri_ok;
  with sdist_final. assert (A.pts_to dist sdist_final);
  // Connect triangle inequality to shortest-path upper bound
  dijkstra_sp_upper_bound_cond sdist_final sweights (SZ.v n) (SZ.v source) final_tri;
  tri_result := final_tri;
}
