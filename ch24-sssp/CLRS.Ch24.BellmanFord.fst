module CLRS.Ch24.BellmanFord
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
module SP = CLRS.Ch24.ShortestPath.Spec

(*
   Bellman-Ford Single-Source Shortest Paths — Verified in Pulse

   Graph: weighted adjacency matrix (n×n flat array, 1000000 = no edge/infinity)
   
   Postcondition:
   - dist[source] == 0
   - All distances valid (< 1000000 or == 1000000)
   - If no negative cycle (result == true):
     * Triangle inequality: for all edges (u,v), dist[v] <= dist[u] + w(u,v)
     * Upper bound: dist[v] <= sp_dist(weights, n, source, v) for all v
       (from CLRS Corollary 24.3, proved in ShortestPath.Spec)
   
   NO admits. NO assumes.
*)

//SNIPPET_START: bf_triangle_inequality
/// Triangle inequality: for each edge (u,v), dist[v] <= dist[u] + w(u,v) when finite
let triangle_inequality (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  forall (u v: nat). u < n /\ v < n /\
    (u * n + v) < Seq.length weights ==>
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     (w < 1000000 /\ d_u < 1000000) ==> d_v <= d_u + w)
//SNIPPET_END: bf_triangle_inequality

/// All distances are either finite (< 1000000) or equal to 1000000 (unreachable)
let valid_distances (dist: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  forall (v: nat). v < n ==> 
    (let d = Seq.index dist v in d < 1000000 \/ d == 1000000)

/// No edge violates triangle inequality (including edges to source)
let no_violations (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (u v: nat). u < n /\ v < n ==>
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     (w < 1000000 /\ d_u < 1000000) ==> d_v <= d_u + w))

/// no_violations implies triangle_inequality
let no_violations_implies_triangle (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : Lemma
  (requires no_violations dist weights n)
  (ensures triangle_inequality dist weights n)
  = ()

/// Partial no-violations: for edges (u,v) with u < u_bound, or u == u_bound and v < v_bound
let no_violations_partial (dist: Seq.seq int) (weights: Seq.seq int) (n u_bound v_bound: nat) : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (u v: nat). u < n /\ v < n /\
    (u < u_bound \/ (u == u_bound /\ v < v_bound)) ==>
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     (w < 1000000 /\ d_u < 1000000) ==> d_v <= d_u + w))

/// Partial at (n, 0) implies full no_violations
let partial_full (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : Lemma
  (requires no_violations_partial dist weights n n 0)
  (ensures no_violations dist weights n)
  = ()

/// Connect BF triangle_inequality + valid_distances to SP.has_triangle_inequality
let bf_to_sp_triangle (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : Lemma
  (requires triangle_inequality dist weights n /\
            valid_distances dist n /\
            Seq.length weights == n * n)
  (ensures SP.has_triangle_inequality dist weights n)
  = ()

/// Helper: establish sp_dist upper bound from triangle inequality + valid_distances
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let bf_sp_upper_bound_cond (dist weights: Seq.seq int) (n source: nat) (flag: bool) : Lemma
  (requires Seq.length dist == n /\
            Seq.length weights == n * n /\
            n > 0 /\ source < n /\
            Seq.index dist source == 0 /\
            valid_distances dist n /\
            (flag == true ==> triangle_inequality dist weights n))
  (ensures flag == true ==>
    (forall (v: nat). v < n ==>
      Seq.index dist v <= SP.sp_dist weights n source v))
  = if flag then begin
      bf_to_sp_triangle dist weights n;
      let aux (v: nat{v < n}) : Lemma 
        (ensures Seq.index dist v <= SP.sp_dist weights n source v) =
        SP.triangle_ineq_implies_upper_bound dist weights n source v
      in
      FStar.Classical.forall_intro aux
    end
#pop-options

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
//SNIPPET_START: bellman_ford_sig
fn bellman_ford
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (result: R.ref bool)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#sresult: erased bool)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    R.pts_to result sresult **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* sdist' no_neg_cycle.
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    R.pts_to result no_neg_cycle **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      valid_distances sdist' (SZ.v n) /\
      (no_neg_cycle == true ==> triangle_inequality sdist' sweights (SZ.v n)) /\
      // Shortest-path upper bound (CLRS Corollary 24.3):
      // When no negative cycle, dist[v] ≤ shortest-path distance for all v
      (no_neg_cycle == true ==>
        (forall (v: nat). v < SZ.v n ==>
          Seq.index sdist' v <= SP.sp_dist sweights (SZ.v n) (SZ.v source) v))
    )
//SNIPPET_END: bellman_ford_sig
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
      (forall (j: nat). j < SZ.v vi ==>
        (if j = SZ.v source 
         then Seq.index sdist_current j == 0 
         else Seq.index sdist_current j == 1000000))
    )
  {
    let vi = !init_i;
    let new_val: int = (if vi = source then 0 else 1000000);
    A.op_Array_Assignment dist vi new_val;
    init_i := vi +^ 1sz;
  };
  
  let _ = !init_i;
  
  // Relaxation: n-1 rounds
  let mut round: SZ.t = 1sz;
  
  while (
    let vround = !round;
    vround <^ n
  )
  invariant exists* vround sdist_current.
    R.pts_to round vround **
    A.pts_to dist sdist_current **
    pure (
      SZ.v vround <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      Seq.index sdist_current (SZ.v source) == 0 /\
      valid_distances sdist_current (SZ.v n)
    )
  {
    let vround = !round;
    
    let mut u: SZ.t = 0sz;
    
    while (
      let vu = !u;
      vu <^ n
    )
    invariant exists* vu sdist_u.
      R.pts_to u vu **
      A.pts_to dist sdist_u **
      pure (
        SZ.v vu <= SZ.v n /\
        Seq.length sdist_u == SZ.v n /\
        Seq.index sdist_u (SZ.v source) == 0 /\
        valid_distances sdist_u (SZ.v n)
      )
    {
      let vu = !u;
      let dist_u = A.op_Array_Access dist vu;
      
      assert pure (dist_u < 1000000 \/ dist_u == 1000000);
      
      let mut v: SZ.t = 0sz;
      
      while (
        let vv = !v;
        vv <^ n
      )
      invariant exists* vv sdist_v.
        R.pts_to v vv **
        A.pts_to dist sdist_v **
        pure (
          SZ.v vv <= SZ.v n /\
          Seq.length sdist_v == SZ.v n /\
          Seq.index sdist_v (SZ.v source) == 0 /\
          valid_distances sdist_v (SZ.v n)
        )
      {
        let vv = !v;
        
        let w_idx = vu *^ n +^ vv;
        let w_uv = A.op_Array_Access weights w_idx;
        
        let old_dist_v = A.op_Array_Access dist vv;
        
        let can_relax = (w_uv < 1000000 && dist_u < 1000000);
        let sum = dist_u + w_uv;
        let should_update = (can_relax && sum < old_dist_v && vv <> source);
        
        let new_dist_v: int = (if should_update then sum else old_dist_v);
        
        assert pure (old_dist_v < 1000000 \/ old_dist_v == 1000000);
        
        if should_update {
          assert pure (sum < 1000000);
        };
        
        assert pure (new_dist_v < 1000000 \/ new_dist_v == 1000000);
        
        if (vv = source) {
          assert pure (old_dist_v == 0);
          assert pure (new_dist_v == 0);
        };
        
        A.op_Array_Assignment dist vv new_dist_v;
        
        v := vv +^ 1sz;
      };
      
      let _ = !v;
      u := vu +^ 1sz;
    };
    
    let _ = !u;
    round := vround +^ 1sz;
  };
  
  let _ = !round;
  
  // === Negative-cycle detection + triangle inequality verification ===
  // Read-only pass: check if any edge (u,v) violates dist[v] <= dist[u] + w.
  // If no violation, triangle inequality holds.
  let mut no_neg: bool = true;
  let mut cu: SZ.t = 0sz;
  
  while (
    let vcu = !cu;
    vcu <^ n
  )
  invariant exists* vcu sdist_check vno.
    R.pts_to cu vcu **
    R.pts_to no_neg vno **
    A.pts_to dist sdist_check **
    pure (
      SZ.v vcu <= SZ.v n /\
      Seq.length sdist_check == SZ.v n /\
      Seq.index sdist_check (SZ.v source) == 0 /\
      valid_distances sdist_check (SZ.v n) /\
      (vno == true ==> no_violations_partial sdist_check sweights (SZ.v n) (SZ.v vcu) 0)
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
    invariant exists* vcv vno_inner.
      R.pts_to cv vcv **
      R.pts_to no_neg vno_inner **
      A.pts_to dist sdist_check **
      pure (
        SZ.v vcv <= SZ.v n /\
        (vno_inner == true ==> no_violations_partial sdist_check sweights (SZ.v n) (SZ.v vcu) (SZ.v vcv))
      )
    {
      let vcv = !cv;
      
      let w_idx = vcu *^ n +^ vcv;
      let w = A.op_Array_Access weights w_idx;
      let d_u = dist_cu;
      let d_v = A.op_Array_Access dist vcv;
      
      // Check triangle inequality for this edge
      let edge_ok = (w >= 1000000 || d_u >= 1000000 || d_v <= d_u + w);
      
      let vno = !no_neg;
      if (not edge_ok) {
        no_neg := false;
      };
      
      cv := vcv +^ 1sz;
    };
    
    let _ = !cv;
    cu := vcu +^ 1sz;
  };
  
  let _ = !cu;
  
  let final_no_neg = !no_neg;
  with sdist_final. assert (A.pts_to dist sdist_final);
  // Connect triangle inequality to shortest-path upper bound
  bf_sp_upper_bound_cond sdist_final sweights (SZ.v n) (SZ.v source) final_no_neg;
  
  result := final_no_neg;
}
#pop-options
