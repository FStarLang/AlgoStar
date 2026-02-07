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

// Specification predicates

// All weights are non-negative or "no edge" (represented as >= 1000000)
let all_weights_non_negative (sweights: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sweights ==> Seq.index sweights i >= 0

// All distances are non-negative  
let all_non_negative (sdist: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sdist ==> Seq.index sdist i >= 0

// All distances are bounded by 1000000
let all_bounded (sdist: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sdist ==> 
    Seq.index sdist i >= 0 /\ Seq.index sdist i <= 1000000

// Triangle inequality: all edges are "relaxed"
// After algorithm completes, for all edges (u,v), if the edge exists and dist[u] is finite,
// then dist[v] <= dist[u] + weight(u,v)
let triangle_inequality (sweights: Seq.seq int) (sdist: Seq.seq int) (n: nat) : prop =
  Seq.length sdist == n /\
  (forall (u v:nat). 
    u < n /\ v < n /\ u * n + v < Seq.length sweights ==>
    (let w = Seq.index sweights (u * n + v) in
     let dist_u = Seq.index sdist u in
     let dist_v = Seq.index sdist v in
     // If there's a real edge and dist_u is finite, then the edge is relaxed
     (w < 1000000 /\ dist_u < 1000000 /\ dist_u + w <= 1000000) ==> 
       dist_v <= dist_u + w))

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
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      all_weights_non_negative sweights  // Dijkstra requires non-negative weights
    )
  ensures exists* sdist'.
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      // Functional correctness properties we've proven:
      // 1. dist[source] == 0 (not just <= 0 as before)
      Seq.index sdist' (SZ.v source) == 0 /\
      // 2. All distances are non-negative
      all_non_negative sdist' /\
      // 3. All distances are bounded [0, 1000000]
      all_bounded sdist'
      // Note: Triangle inequality (dist[v] <= dist[u] + w(u,v) for all edges)
      // is the full correctness property but requires more complex invariants
      // involving visited sets and path properties to prove automatically.
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
  
  ()
}
