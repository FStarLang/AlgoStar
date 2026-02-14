(*
   Bellman-Ford with Complexity Bound — CLRS §24.1

   Proves O(V³) complexity for Bellman-Ford with adjacency-matrix representation.
   
   CLRS Analysis (§24.1):
   - With adjacency list: O(VE) time
   - With adjacency matrix: each "relax all edges" pass is O(V²)
   - Repeated V-1 times: O(V³) total
   
   Our Implementation Structure:
   - Initialization: n ticks (set dist[i] for each vertex)
   - Main relaxation: (n-1) rounds × n² edge checks = (n-1)n² ticks
   - Negative cycle detection: n² edge checks = n² ticks
   - Total: n + (n-1)n² + n² = n + n³ ticks
   - Bound: n + n³ ≤ 2n³ for n ≥ 1 (proven in bellman_ford_cubic_bound)

   Ghost Tick Counter:
   - Uses Pulse.Lib.GhostReference.ref nat — fully erased at runtime
   - Each vertex initialization, edge check, or edge relaxation = 1 ghost tick
   - Postcondition: cf - c0 == n + n³

   Functional Correctness:
   - dist[source] == 0
   - All distances valid (< 1000000 or == 1000000)
   - If no negative cycle: triangle inequality holds
   - Shortest-path upper bound (CLRS Corollary 24.3)

   NO admits. NO assumes.
*)

module CLRS.Ch24.BellmanFord.Complexity.Instrumented
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Definitions (from BellmanFord.fst) ==========

let triangle_inequality (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  forall (u v: nat). u < n /\ v < n /\
    (u * n + v) < Seq.length weights ==>
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     (w < 1000000 /\ d_u < 1000000) ==> d_v <= d_u + w)

let valid_distances (dist: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  forall (v: nat). v < n ==> 
    (let d = Seq.index dist v in d < 1000000 \/ d == 1000000)

let no_violations (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (u v: nat). u < n /\ v < n ==>
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     (w < 1000000 /\ d_u < 1000000) ==> d_v <= d_u + w))

let no_violations_partial (dist: Seq.seq int) (weights: Seq.seq int) (n u_bound v_bound: nat) : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (u v: nat). u < n /\ v < n /\
    (u < u_bound \/ (u == u_bound /\ v < v_bound)) ==>
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     (w < 1000000 /\ d_u < 1000000) ==> d_v <= d_u + w))

let no_violations_implies_triangle (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : Lemma
  (requires no_violations dist weights n)
  (ensures triangle_inequality dist weights n)
  = ()

let partial_full (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : Lemma
  (requires no_violations_partial dist weights n n 0)
  (ensures no_violations dist weights n)
  = ()

let bf_to_sp_triangle (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : Lemma
  (requires triangle_inequality dist weights n /\
            valid_distances dist n /\
            Seq.length weights == n * n)
  (ensures SP.has_triangle_inequality dist weights n)
  = ()

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

// ========== Pure Complexity Bounds ==========

(**
 * Total iterations count for Bellman-Ford with adjacency matrix:
 * - Initialization: n iterations
 * - Main relaxation: (n-1) rounds of n² edge checks each
 * - Negative cycle detection: n² edge checks
 * Total: n + (n-1)n² + n²
 *)
let bellman_ford_iterations (n: nat) : nat =
  n + (if n >= 1 then (n - 1) * n * n else 0) + n * n

(**
 * Simplify: n + (n-1)n² + n² = n + n³ - n² + n² = n + n³
 *)
let bellman_ford_simplified (n: nat) : Lemma
  (requires n >= 1)
  (ensures bellman_ford_iterations n == n + n * n * n)
  =
  assert ((n - 1) * n * n + n * n == n * n * n)

(**
 * Main complexity bound: prove the total is at most 2n³ for n ≥ 1
 * This establishes O(n³) asymptotic complexity.
 *)
let bellman_ford_cubic_bound (n: nat) : Lemma
  (requires n >= 1)
  (ensures bellman_ford_iterations n <= 2 * n * n * n)
  =
  bellman_ford_simplified n;
  // n + n³ ≤ 2n³ ⟺ n ≤ n³
  // For n ≥ 1: n ≤ n² ≤ n³
  assert (n >= 1);
  assert (n <= n * n);
  assert (n * n <= n * n * n);
  assert (n + n * n * n <= 2 * n * n * n)

(**
 * Lower bound: for n ≥ 2, we do at least n³ operations
 *)
let bellman_ford_lower_bound (n: nat) : Lemma
  (requires n >= 2)
  (ensures bellman_ford_iterations n >= n * n * n)
  =
  bellman_ford_simplified n;
  assert (n + n * n * n >= n * n * n)

// ========== Complexity bound predicate for runtime verification ==========

let bellman_ford_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ (n >= 1 ==> cf - c0 == n + n * n * n)

let bellman_ford_complexity_is_cubic (cf c0 n: nat) : Lemma
  (requires bellman_ford_complexity_bounded cf c0 n /\ n >= 1)
  (ensures cf - c0 <= 2 * n * n * n)
  =
  bellman_ford_cubic_bound n

// ========== Main Algorithm with Complexity ==========

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
fn bellman_ford_complexity
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (result: R.ref bool)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#sresult: erased bool)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    R.pts_to result sresult **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* sdist' no_neg_cycle (cf: nat).
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    R.pts_to result no_neg_cycle **
    GR.pts_to ctr cf **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      valid_distances sdist' (SZ.v n) /\
      (no_neg_cycle == true ==> triangle_inequality sdist' sweights (SZ.v n)) /\
      (no_neg_cycle == true ==>
        (forall (v: nat). v < SZ.v n ==>
          Seq.index sdist' v <= SP.sp_dist sweights (SZ.v n) (SZ.v source) v)) /\
      bellman_ford_complexity_bounded cf (reveal c0) (SZ.v n)
    )
{
  // Initialization: dist[source] = 0, all others = 1000000 — n ticks
  let mut init_i: SZ.t = 0sz;
  
  while (
    let vi = !init_i;
    vi <^ n
  )
  invariant exists* vi sdist_current (vc: nat).
    R.pts_to init_i vi **
    A.pts_to dist sdist_current **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==>
        (if j = SZ.v source 
         then Seq.index sdist_current j == 0 
         else Seq.index sdist_current j == 1000000)) /\
      // Complexity: vc == c0 + vi
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi
    )
  {
    let vi = !init_i;
    let new_val: int = (if vi = source then 0 else 1000000);
    A.op_Array_Assignment dist vi new_val;
    tick ctr;
    init_i := vi +^ 1sz;
  };
  
  let _ = !init_i;
  
  // Relaxation: (n-1) rounds, each checking all n² edges
  let mut round: SZ.t = 1sz;
  
  while (
    let vround = !round;
    vround <^ n
  )
  invariant exists* vround sdist_current (vc: nat).
    R.pts_to round vround **
    A.pts_to dist sdist_current **
    GR.pts_to ctr vc **
    pure (
      SZ.v vround <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      Seq.index sdist_current (SZ.v source) == 0 /\
      valid_distances sdist_current (SZ.v n) /\
      // Complexity: vc == c0 + n + (vround - 1) * n * n
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v n + (SZ.v vround - 1) * SZ.v n * SZ.v n
    )
  {
    let vround = !round;
    
    let mut u: SZ.t = 0sz;
    
    while (
      let vu = !u;
      vu <^ n
    )
    invariant exists* vu sdist_u (vc_u: nat).
      R.pts_to u vu **
      A.pts_to dist sdist_u **
      GR.pts_to ctr vc_u **
      pure (
        SZ.v vu <= SZ.v n /\
        Seq.length sdist_u == SZ.v n /\
        Seq.index sdist_u (SZ.v source) == 0 /\
        valid_distances sdist_u (SZ.v n) /\
        // Complexity: vc_u == c0 + n + (vround - 1) * n * n + vu * n
        vc_u >= reveal c0 /\
        vc_u - reveal c0 == SZ.v n + (SZ.v vround - 1) * SZ.v n * SZ.v n + SZ.v vu * SZ.v n
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
      invariant exists* vv sdist_v (vc_v: nat).
        R.pts_to v vv **
        A.pts_to dist sdist_v **
        GR.pts_to ctr vc_v **
        pure (
          SZ.v vv <= SZ.v n /\
          Seq.length sdist_v == SZ.v n /\
          Seq.index sdist_v (SZ.v source) == 0 /\
          valid_distances sdist_v (SZ.v n) /\
          // Complexity: vc_v == c0 + n + (vround - 1) * n * n + vu * n + vv
          vc_v >= reveal c0 /\
          vc_v - reveal c0 == SZ.v n + (SZ.v vround - 1) * SZ.v n * SZ.v n + SZ.v vu * SZ.v n + SZ.v vv
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
        tick ctr;
        
        v := vv +^ 1sz;
      };
      
      let _ = !v;
      u := vu +^ 1sz;
    };
    
    let _ = !u;
    round := vround +^ 1sz;
  };
  
  let _ = !round;
  
  // Negative-cycle detection + triangle inequality verification — n² ticks
  let mut no_neg: bool = true;
  let mut cu: SZ.t = 0sz;
  
  while (
    let vcu = !cu;
    vcu <^ n
  )
  invariant exists* vcu sdist_check vno (vc_c: nat).
    R.pts_to cu vcu **
    R.pts_to no_neg vno **
    A.pts_to dist sdist_check **
    GR.pts_to ctr vc_c **
    pure (
      SZ.v vcu <= SZ.v n /\
      Seq.length sdist_check == SZ.v n /\
      Seq.index sdist_check (SZ.v source) == 0 /\
      valid_distances sdist_check (SZ.v n) /\
      (vno == true ==> no_violations_partial sdist_check sweights (SZ.v n) (SZ.v vcu) 0) /\
      // Complexity: vc_c == c0 + n + (n - 1) * n * n + vcu * n
      vc_c >= reveal c0 /\
      vc_c - reveal c0 == SZ.v n + (SZ.v n - 1) * SZ.v n * SZ.v n + SZ.v vcu * SZ.v n
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
    invariant exists* vcv vno_inner (vc_cv: nat).
      R.pts_to cv vcv **
      R.pts_to no_neg vno_inner **
      A.pts_to dist sdist_check **
      GR.pts_to ctr vc_cv **
      pure (
        SZ.v vcv <= SZ.v n /\
        (vno_inner == true ==> no_violations_partial sdist_check sweights (SZ.v n) (SZ.v vcu) (SZ.v vcv)) /\
        // Complexity: vc_cv == c0 + n + (n - 1) * n * n + vcu * n + vcv
        vc_cv >= reveal c0 /\
        vc_cv - reveal c0 == SZ.v n + (SZ.v n - 1) * SZ.v n * SZ.v n + SZ.v vcu * SZ.v n + SZ.v vcv
      )
    {
      let vcv = !cv;
      
      let w_idx = vcu *^ n +^ vcv;
      let w = A.op_Array_Access weights w_idx;
      let d_u = dist_cu;
      let d_v = A.op_Array_Access dist vcv;
      
      let edge_ok = (w >= 1000000 || d_u >= 1000000 || d_v <= d_u + w);
      
      let vno = !no_neg;
      if (not edge_ok) {
        no_neg := false;
      };
      
      tick ctr;
      
      cv := vcv +^ 1sz;
    };
    
    let _ = !cv;
    cu := vcu +^ 1sz;
  };
  
  let _ = !cu;
  
  let final_no_neg = !no_neg;
  with sdist_final. assert (A.pts_to dist sdist_final);
  
  // At this point: cf - c0 == n + (n-1)n² + n² == n + n³
  // Prove the bound
  assert pure (SZ.v n >= 1);
  bellman_ford_simplified (SZ.v n);
  
  bf_sp_upper_bound_cond sdist_final sweights (SZ.v n) (SZ.v source) final_no_neg;
  
  result := final_no_neg;
}
#pop-options
