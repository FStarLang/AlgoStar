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
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec
module SPT = CLRS.Ch24.ShortestPath.Triangle

(*
   Dijkstra's Single-Source Shortest Paths — Verified in Pulse

   Graph: weighted adjacency matrix (n×n flat array, SP.inf = no edge/infinity)
   Requires non-negative weights.
   
   Sentinel constraint: The constant SP.inf encodes infinity. Edge weights and
   all valid shortest-path distances must be strictly less than SP.inf. If any
   true shortest-path distance reaches SP.inf, it becomes indistinguishable
   from "unreachable." F*'s int is mathematical (unbounded), so arithmetic
   overflow is not a concern—only the sentinel comparison matters.
   
   Postcondition:
   - dist[source] == 0
   - All distances non-negative and bounded [0, SP.inf]
   - Triangle inequality: for all edges (u,v), dist[v] <= dist[u] + w(u,v)
     (proven from edge relaxation — no separate verification pass needed)
   - Equality: dist[v] == sp_dist(source, v) for all v
     (proven via upper bound from triangle inequality + lower bound from sp_dist triangle ineq)
   
   All dependencies fully proven, including sp_dist_k_stabilize in ShortestPath.Triangle.fst
   (stabilization of sp_dist_k at n-1 via pigeonhole/path contraction argument).
   
   NO admits. NO assumes.
*)

// All weights are non-negative
let all_weights_non_negative (sweights: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sweights ==> Seq.index sweights i >= 0

// All distances are non-negative  
let all_non_negative (sdist: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sdist ==> Seq.index sdist i >= 0

// All distances are bounded by inf
let all_bounded (sdist: Seq.seq int) : prop =
  forall (i:nat). i < Seq.length sdist ==> 
    Seq.index sdist i >= 0 /\ Seq.index sdist i <= SP.inf

//SNIPPET_START: triangle_inequality
// Triangle inequality: for all finite edges, dist[v] <= dist[u] + w
let triangle_inequality (sweights: Seq.seq int) (sdist: Seq.seq int) (n: nat) : prop =
  Seq.length sdist == n /\
  (forall (u v:nat). 
    u < n /\ v < n /\ u * n + v < Seq.length sweights ==>
    (let w = Seq.index sweights (u * n + v) in
     let dist_u = Seq.index sdist u in
     let dist_v = Seq.index sdist v in
     (w < SP.inf /\ dist_u < SP.inf) ==> dist_v <= dist_u + w))
//SNIPPET_END: triangle_inequality

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
let dijkstra_sp_upper_bound (sdist sweights: Seq.seq int) (n source: nat) : Lemma
  (requires Seq.length sdist == n /\
            Seq.length sweights == n * n /\
            n > 0 /\ source < n /\
            Seq.index sdist source == 0 /\
            all_bounded sdist /\
            triangle_inequality sweights sdist n)
  (ensures 
    (forall (v: nat). v < n ==>
      Seq.index sdist v <= SP.sp_dist sweights n source v))
  = dijkstra_to_sp_triangle sdist sweights n;
    let aux (v: nat{v < n}) : Lemma
      (ensures Seq.index sdist v <= SP.sp_dist sweights n source v) =
      SP.triangle_ineq_implies_upper_bound sdist sweights n source v
    in
    FStar.Classical.forall_intro aux
#pop-options

//SNIPPET_START: pred_consistent
/// Predecessor consistency: pred encodes a shortest-path tree.
/// For every reachable vertex v ≠ source, pred[v] is the predecessor on a shortest path:
///   dist[v] = dist[pred[v]] + w(pred[v], v)
let pred_consistent (spred: Seq.seq SZ.t) (sdist sweights: Seq.seq int) (n source: nat) : prop =
  Seq.length spred == n /\
  Seq.length sdist == n /\
  Seq.length sweights >= n * n /\
  (source < n ==> SZ.v (Seq.index spred source) == source) /\
  (forall (v: nat). v < n /\ v <> source /\ Seq.index sdist v < SP.inf ==>
    (let p = SZ.v (Seq.index spred v) in
     p < n /\
     p * n + v < Seq.length sweights /\
     Seq.index sweights (p * n + v) < SP.inf /\
     Seq.index sdist p < SP.inf /\
     Seq.index sdist v == Seq.index sdist p + Seq.index sweights (p * n + v)))
//SNIPPET_END: pred_consistent

/// Internal: pred consistency + predecessors are visited vertices
let pred_ok (spred: Seq.seq SZ.t) (sdist sweights svisited: Seq.seq int) (n source: nat) : prop =
  pred_consistent spred sdist sweights n source /\
  Seq.length svisited == n /\
  (forall (v: nat). v < n /\ v <> source /\ Seq.index sdist v < SP.inf ==>
    SZ.v (Seq.index spred v) < n /\
    Seq.index svisited (SZ.v (Seq.index spred v)) = 1)

/// dist[v] >= sp_dist(source, v) for all v (no underestimate property)
let dist_ge_sp_dist (sdist sweights: Seq.seq int) (n source: nat) : prop =
  Seq.length sdist == n /\
  (forall (v: nat). v < n ==> Seq.index sdist v >= SP.sp_dist sweights n source v)

/// At initialization, dist[v] >= sp_dist(source, v) holds
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let init_dist_ge_sp_dist (sdist sweights: Seq.seq int) (n source: nat)
  : Lemma
    (requires n > 0 /\ source < n /\
             Seq.length sdist == n /\
             Seq.length sweights == n * n /\
             all_weights_non_negative sweights /\
             Seq.index sdist source == 0 /\
             (forall (v: nat). v < n /\ v <> source ==> Seq.index sdist v == SP.inf))
    (ensures dist_ge_sp_dist sdist sweights n source)
  = let aux (v: nat{v < n}) : Lemma
      (ensures Seq.index sdist v >= SP.sp_dist sweights n source v) =
      SP.sp_dist_k_bounded sweights n source v (n - 1);
      if v = source then SPT.sp_dist_self_zero sweights n source
      else assert (Seq.index sdist v == SP.inf)
    in
    FStar.Classical.forall_intro aux
#pop-options

/// After a full relaxation round from u, re-establish dist >= sp_dist.
/// Each sdist_after[v] is either unchanged or relaxed to dist[u] + w(u,v).
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let relax_round_lb_post
  (sdist_pre sdist_after sweights: Seq.seq int) (n source u: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ u < n /\
      Seq.length sdist_pre == n /\ Seq.length sdist_after == n /\
      Seq.length sweights == n * n /\
      all_weights_non_negative sweights /\
      dist_ge_sp_dist sdist_pre sweights n source /\
      (forall (v: nat). v < n ==>
        Seq.index sdist_after v == Seq.index sdist_pre v \/
        (Seq.index sdist_after v == Seq.index sdist_pre u + Seq.index sweights (u * n + v) /\
         Seq.index sweights (u * n + v) < SP.inf /\
         Seq.index sdist_pre u < SP.inf)))
    (ensures dist_ge_sp_dist sdist_after sweights n source)
  = let aux (v: nat{v < n}) : Lemma
      (ensures Seq.index sdist_after v >= SP.sp_dist sweights n source v) =
      if Seq.index sdist_after v = Seq.index sdist_pre v then ()
      else SPT.sp_dist_triangle_ineq sweights n source u v
    in
    FStar.Classical.forall_intro aux
#pop-options

/// Bridge lemma: pred_ok is preserved by the relaxation round
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let relax_round_pred_ok
  (sweights sdist_pre sdist_after: Seq.seq int)
  (spred_pre spred_after: Seq.seq SZ.t)
  (svisited_pre: Seq.seq int)
  (n source u: nat)
  : Lemma
    (requires
      n > 0 /\ source < n /\ u < n /\
      Seq.length sweights == n * n /\
      Seq.length sdist_pre == n /\ Seq.length sdist_after == n /\
      Seq.length spred_pre == n /\ Seq.length spred_after == n /\
      Seq.length svisited_pre == n /\
      Seq.index svisited_pre u = 0 /\
      Seq.index sdist_pre source == 0 /\
      all_non_negative sdist_pre /\
      all_weights_non_negative sweights /\
      (forall (j: nat). j < n ==>
        (Seq.index svisited_pre j = 0 \/ Seq.index svisited_pre j = 1)) /\
      pred_ok spred_pre sdist_pre sweights svisited_pre n source /\
      (* Visited vertices' distances don't change *)
      (forall (x: nat). x < n /\ (Seq.index svisited_pre x = 1 \/ x = u) ==>
        Seq.index sdist_after x == Seq.index sdist_pre x) /\
      (* Relax effect: for each v, either unchanged or STRICTLY improved through u *)
      (forall (v: nat). v < n ==>
        (Seq.index sdist_after v == Seq.index sdist_pre v /\
         Seq.index spred_after v == Seq.index spred_pre v) \/
        (Seq.index sdist_after v == Seq.index sdist_pre u + Seq.index sweights (u * n + v) /\
         Seq.index sdist_after v < Seq.index sdist_pre v /\
         Seq.index sweights (u * n + v) < SP.inf /\
         Seq.index sdist_pre u < SP.inf /\
         SZ.v (Seq.index spred_after v) == u))
    )
    (ensures pred_ok spred_after sdist_after sweights (Seq.upd svisited_pre u 1) n source)
  = let svisited_now = Seq.upd svisited_pre u 1 in
    Seq.lemma_index_upd1 svisited_pre u 1;
    assert (Seq.index svisited_now u = 1);
    // Source is never "updated" since dist[source] = 0 and the update requires strict decrease
    // (dist_u + w >= 0 = dist_pre[source], so no strict decrease is possible)
    assert (Seq.index sdist_after source == Seq.index sdist_pre source);
    assert (Seq.index spred_after source == Seq.index spred_pre source);
    let aux (v: nat{v < n /\ v <> source /\ Seq.index sdist_after v < SP.inf}) : Lemma
      (ensures (let p = SZ.v (Seq.index spred_after v) in
                p < n /\
                p * n + v < Seq.length sweights /\
                Seq.index sweights (p * n + v) < SP.inf /\
                Seq.index sdist_after p < SP.inf /\
                Seq.index sdist_after v == Seq.index sdist_after p + Seq.index sweights (p * n + v) /\
                Seq.index svisited_now p = 1))
      = if Seq.index sdist_after v = Seq.index sdist_pre v &&
           Seq.index spred_after v = Seq.index spred_pre v
        then begin
          let p = SZ.v (Seq.index spred_pre v) in
          assert (Seq.index svisited_pre p = 1);
          assert (Seq.index sdist_after p == Seq.index sdist_pre p);
          assert (Seq.index svisited_now p = 1)
        end else begin
          assert (SZ.v (Seq.index spred_after v) == u);
          assert (Seq.index sdist_after u == Seq.index sdist_pre u)
        end
    in
    FStar.Classical.forall_intro aux
#pop-options

(* ===== Ghost invariants for triangle inequality proof ===== *)

// Triangle inequality restricted to edges from visited vertices
let tri_from_visited (sweights sdist svisited: Seq.seq int) (n: nat) : prop =
  Seq.length sdist == n /\
  Seq.length sweights >= n * n /\
  Seq.length svisited == n /\
  (forall (u v: nat).
    u < n /\ v < n /\ u * n + v < Seq.length sweights /\
    Seq.index svisited u = 1 ==>
    (let w = Seq.index sweights (u * n + v) in
     let d_u = Seq.index sdist u in
     let d_v = Seq.index sdist v in
     (w < SP.inf /\ d_u < SP.inf) ==> d_v <= d_u + w))

// Ordering: visited distances <= unvisited distances
let visited_le_unvisited (sdist svisited: Seq.seq int) (n: nat) : prop =
  Seq.length sdist == n /\
  Seq.length svisited == n /\
  (forall (x u: nat). x < n /\ u < n /\
    Seq.index svisited x = 1 /\ Seq.index svisited u = 0 ==>
    Seq.index sdist x <= Seq.index sdist u)

// When all vertices are visited, tri_from_visited implies full triangle_inequality
let all_visited_tri_is_full
  (sweights sdist svisited: Seq.seq int) (n: nat)
  : Lemma
    (requires
      tri_from_visited sweights sdist svisited n /\
      Seq.length sweights == n * n /\
      (forall (u: nat). u < n ==> Seq.index svisited u = 1))
    (ensures triangle_inequality sweights sdist n)
  = ()

// After relaxation from u: triangle inequality extends and ordering is preserved
// Preconditions: old invariants hold, u is min unvisited, relaxation properties hold
#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let extend_tri_after_relax
  (sweights sdist_old sdist_new svisited_old: Seq.seq int) (n u: nat)
  : Lemma
    (requires
      // Basic sizes
      Seq.length sdist_old == n /\ Seq.length sdist_new == n /\
      Seq.length sweights == n * n /\ Seq.length svisited_old == n /\
      n > 0 /\ u < n /\
      all_weights_non_negative sweights /\
      // Old invariants
      tri_from_visited sweights sdist_old svisited_old n /\
      visited_le_unvisited sdist_old svisited_old n /\
      // u was unvisited
      Seq.index svisited_old u = 0 /\
      // u has minimum dist among unvisited
      (forall (j: nat). j < n /\ Seq.index svisited_old j = 0 ==>
        Seq.index sdist_old u <= Seq.index sdist_old j) /\
      // Visited distances unchanged
      (forall (x: nat). x < n /\ Seq.index svisited_old x = 1 ==>
        Seq.index sdist_new x == Seq.index sdist_old x) /\
      // dist[u] unchanged
      Seq.index sdist_new u == Seq.index sdist_old u /\
      // All distances only decrease
      (forall (v: nat). v < n ==> Seq.index sdist_new v <= Seq.index sdist_old v) /\
      // For unvisited v: new dist[v] >= dist[u] (relaxation can't go below dist[u])
      (forall (v: nat). v < n /\ Seq.index svisited_old v = 0 ==>
        Seq.index sdist_new v >= Seq.index sdist_old u) /\
      // Triangle from u: relaxation established it
      (forall (v: nat). v < n /\ u * n + v < Seq.length sweights ==>
        (let w = Seq.index sweights (u * n + v) in
         let d_u = Seq.index sdist_new u in
         (w < SP.inf /\ d_u < SP.inf) ==> Seq.index sdist_new v <= d_u + w)))
    (ensures
      (let svisited_new = Seq.upd svisited_old u 1 in
       tri_from_visited sweights sdist_new svisited_new n /\
       visited_le_unvisited sdist_new svisited_new n))
  = ()
#pop-options

// Count of entries equal to 1 in s[0..n)
// Note: These general-purpose utilities are also available in CLRS.Common.CountOnes.
let rec count_ones (s: Seq.seq int) (n: nat) : Tot nat (decreases n) =
  if n = 0 || n > Seq.length s then 0
  else (if Seq.index s (n-1) = 1 then 1 else 0) + count_ones s (n-1)

let rec count_ones_all_zero (s: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length s /\ (forall (j:nat). j < n ==> Seq.index s j = 0))
          (ensures count_ones s n == 0) (decreases n)
  = if n > 0 then count_ones_all_zero s (n-1)

let rec count_ones_all_one (s: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length s /\ (forall (j:nat). j < n ==> Seq.index s j = 1))
          (ensures count_ones s n == n) (decreases n)
  = if n > 0 then count_ones_all_one s (n-1)

let rec count_ones_bound (s: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length s /\
           (forall (j:nat). j < n ==> Seq.index s j = 0 \/ Seq.index s j = 1))
          (ensures count_ones s n <= n) (decreases n)
  = if n > 0 then count_ones_bound s (n-1)

let rec count_ones_upd_above (s: Seq.seq int) (n u: nat)
  : Lemma (requires n <= Seq.length s /\ u >= n /\ u < Seq.length s)
          (ensures count_ones (Seq.upd s u 1) n == count_ones s n) (decreases n)
  = if n > 0 then count_ones_upd_above s (n-1) u

let rec count_ones_mark (s: Seq.seq int) (n u: nat)
  : Lemma (requires n <= Seq.length s /\ u < n /\ Seq.index s u = 0 /\
           (forall (j:nat). j < n ==> Seq.index s j = 0 \/ Seq.index s j = 1))
          (ensures count_ones (Seq.upd s u 1) n == count_ones s n + 1) (decreases n)
  = if n - 1 > u then
      count_ones_mark s (n-1) u
    else if n - 1 = u then
      count_ones_upd_above s (n-1) u
    else () // n-1 < u, impossible since u < n

let rec count_ones_full (s: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length s /\ count_ones s n >= n /\
           (forall (j:nat). j < n ==> Seq.index s j = 0 \/ Seq.index s j = 1))
          (ensures forall (j:nat). j < n ==> Seq.index s j = 1) (decreases n)
  = if n > 0 then begin
      count_ones_bound s (n-1);
      count_ones_full s (n-1)
    end

// count_ones < n implies not all visited
let count_ones_not_all_visited (s: Seq.seq int) (n: nat)
  : Lemma (requires n <= Seq.length s /\ count_ones s n < n /\
           (forall (j:nat). j < n ==> Seq.index s j = 0 \/ Seq.index s j = 1))
          (ensures ~(forall (j:nat). j < n ==> Seq.index s j = 1))
  = Classical.move_requires (count_ones_all_one s) n

// Minimum property: idx has minimum distance among unvisited vertices,
// and is itself unvisited (or all vertices are already visited)
let has_min_dist_unvisited (sdist svisited: Seq.seq int) (n idx: nat) : prop =
  idx < n /\
  Seq.length sdist == n /\
  Seq.length svisited == n /\
  (forall (j: nat). j < n /\ Seq.index svisited j = 0 ==>
    Seq.index sdist idx <= Seq.index sdist j) /\
  // idx is unvisited, or all vertices are visited
  ((forall (j: nat). j < n ==> Seq.index svisited j = 1) \/
   Seq.index svisited idx = 0)

// ========== Ghost tick for complexity counting ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Pure Complexity Bounds ==========

let dijkstra_iterations (n: nat) : nat = n + 2 * n * n

let dijkstra_quadratic_bound (n: nat) : Lemma
  (ensures dijkstra_iterations n <= 3 * n * n) =
  if n = 0 then ()
  else (assert (n >= 1); assert (n * n >= n);
        assert (n + 2 * n * n <= n * n + 2 * n * n);
        assert (n * n + 2 * n * n == 3 * n * n))

let dijkstra_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == dijkstra_iterations n

let dijkstra_complexity_is_quadratic (cf c0 n: nat) : Lemma
  (requires dijkstra_complexity_bounded cf c0 n)
  (ensures cf - c0 <= 3 * n * n) =
  dijkstra_quadratic_bound n

// Helper function to find minimum distance vertex among unvisited
fn find_min_unvisited
  (dist: A.array int)
  (visited: V.vec int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#sdist: erased (Seq.seq int))
  (#svisited: erased (Seq.seq int))
  (#vc0: erased nat)
  requires
    A.pts_to dist sdist **
    V.pts_to visited svisited **
    GR.pts_to ctr vc0 **
    pure (
      SZ.v n > 0 /\
      Seq.length sdist == SZ.v n /\
      Seq.length svisited == SZ.v n /\
      all_bounded sdist /\
      (forall (j: nat). j < SZ.v n ==>
        (Seq.index svisited j = 0 \/ Seq.index svisited j = 1))
    )
  returns min_idx:SZ.t
  ensures
    A.pts_to dist sdist **
    V.pts_to visited svisited **
    GR.pts_to ctr (hide (reveal vc0 + SZ.v n)) **
    pure (has_min_dist_unvisited sdist svisited (SZ.v n) (SZ.v min_idx))
{
  let mut min_idx: SZ.t = 0sz;
  let mut min_val: int = SP.inf + 1;
  let mut i: SZ.t = 0sz;
  
  while (
    let vi = !i;
    vi <^ n
  )
  invariant exists* vi vmin_idx vmin_val (vc: nat).
    R.pts_to i vi **
    R.pts_to min_idx vmin_idx **
    R.pts_to min_val vmin_val **
    A.pts_to dist sdist **
    V.pts_to visited svisited **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      SZ.v vmin_idx < SZ.v n /\
      vc == reveal vc0 + SZ.v vi /\
      // min_val tracks the minimum distance seen among unvisited vertices in [0, vi)
      (forall (j: nat). j < SZ.v vi /\ Seq.index svisited j = 0 ==>
        vmin_val <= Seq.index sdist j) /\
      // If we found an unvisited vertex, min_val = dist[vmin_idx] and vmin_idx is unvisited
      (vmin_val <= SP.inf ==>
        Seq.index svisited (SZ.v vmin_idx) = 0 /\
        vmin_val == Seq.index sdist (SZ.v vmin_idx)) /\
      // If no unvisited found, all j < vi are visited
      (vmin_val > SP.inf ==>
        (forall (j: nat). j < SZ.v vi ==>
          Seq.index svisited j = 1))
    )
  decreases (SZ.v n - SZ.v !i)
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

    tick ctr;
    
    i := vi +^ 1sz;
  };
  
  let _ = !i;
  let result = !min_idx;
  let _ = !min_val;
  result
}

let lemma_2d_index_fits (u v n: nat)
  : Lemma (requires u < n /\ v < n /\ SZ.fits (n * n))
          (ensures SZ.fits (u * n + v) /\ SZ.fits (u * n) /\ u * n + v < n * n)
  = assert (u * n <= (n - 1) * n);
    assert ((n - 1) * n + v < n * n)

// Helper: extend the "relaxed edges from u" quantifier by one step
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let extend_relaxed_from_u
  (sdist sweights: Seq.seq int) (n u vv: nat)
  (new_dist_val dist_u: int) : Lemma
  (requires
    u < n /\ vv < n /\
    Seq.length sdist == n /\ Seq.length sweights == n * n /\
    dist_u == Seq.index sdist u /\
    Seq.index (Seq.upd sdist vv new_dist_val) u == dist_u /\
    (forall (v': nat). v' < vv /\ v' < n /\
      u * n + v' < Seq.length sweights ==>
      (let w = Seq.index sweights (u * n + v') in
       let d_u = Seq.index sdist u in
       (w < SP.inf /\ d_u < SP.inf) ==> Seq.index sdist v' <= d_u + w)) /\
    (let w = Seq.index sweights (u * n + vv) in
     (w < SP.inf /\ dist_u < SP.inf) ==> new_dist_val <= dist_u + w))
  (ensures
    (let sdist' = Seq.upd sdist vv new_dist_val in
    forall (v': nat). v' < vv + 1 /\ v' < n /\
      u * n + v' < Seq.length sweights ==>
      (let w = Seq.index sweights (u * n + v') in
       let d_u = Seq.index sdist' u in
       (w < SP.inf /\ d_u < SP.inf) ==> Seq.index sdist' v' <= d_u + w)))
  =
  let sdist' = Seq.upd sdist vv new_dist_val in
  assert (Seq.index sdist' vv == new_dist_val);
  assert (Seq.index sdist' u == dist_u)
#pop-options

// Relax loop + bridge lemmas, extracted to its own scope for SMT tractability
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --split_queries always"
fn dijkstra_relax_round
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (pred: A.array SZ.t)
  (visited: V.vec int)
  (u: SZ.t)
  (dist_u: int)
  (ctr: GR.ref nat)
  (#sweights: erased (Seq.seq int))
  (#sdist_pre: erased (Seq.seq int))
  (#spred_pre: erased (Seq.seq SZ.t))
  (#svisited_pre: erased (Seq.seq int))
  (#svisited_now: erased (Seq.seq int))
  (#vc0: erased nat)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist_pre **
    A.pts_to pred spred_pre **
    V.pts_to visited svisited_now **
    GR.pts_to ctr vc0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      all_weights_non_negative sweights /\
      Seq.length sdist_pre == SZ.v n /\
      Seq.length spred_pre == SZ.v n /\
      Seq.length svisited_pre == SZ.v n /\
      svisited_now == Seq.upd svisited_pre (SZ.v u) 1 /\
      Seq.index sdist_pre (SZ.v source) == 0 /\
      all_non_negative sdist_pre /\
      all_bounded sdist_pre /\
      dist_u == Seq.index sdist_pre (SZ.v u) /\
      (forall (j: nat). j < SZ.v n ==>
        (Seq.index svisited_pre j = 0 \/ Seq.index svisited_pre j = 1)) /\
      Seq.index svisited_pre (SZ.v u) = 0 /\
      tri_from_visited sweights sdist_pre svisited_pre (SZ.v n) /\
      visited_le_unvisited sdist_pre svisited_pre (SZ.v n) /\
      (forall (j: nat). j < SZ.v n /\ Seq.index svisited_pre j = 0 ==>
        Seq.index sdist_pre (SZ.v u) <= Seq.index sdist_pre j) /\
      dist_ge_sp_dist sdist_pre sweights (SZ.v n) (SZ.v source) /\
      pred_ok spred_pre sdist_pre sweights svisited_pre (SZ.v n) (SZ.v source)
    )
  ensures exists* sdist_after spred_after (vc1: nat).
    A.pts_to weights sweights **
    A.pts_to dist sdist_after **
    A.pts_to pred spred_after **
    V.pts_to visited svisited_now **
    GR.pts_to ctr vc1 **
    pure (
      Seq.length sdist_after == SZ.v n /\
      Seq.length spred_after == SZ.v n /\
      Seq.length svisited_now == SZ.v n /\
      Seq.length sdist_pre == SZ.v n /\
      Seq.length spred_pre == SZ.v n /\
      SZ.v source < SZ.v n /\
      SZ.v source < Seq.length sdist_after /\
      Seq.index sdist_after (SZ.v source) == 0 /\
      all_non_negative sdist_after /\
      all_bounded sdist_after /\
      (forall (j: nat). j < SZ.v n ==>
        Seq.index sdist_after j <= Seq.index sdist_pre j) /\
      tri_from_visited sweights sdist_after svisited_now (SZ.v n) /\
      visited_le_unvisited sdist_after svisited_now (SZ.v n) /\
      dist_ge_sp_dist sdist_after sweights (SZ.v n) (SZ.v source) /\
      pred_ok spred_after sdist_after sweights svisited_now (SZ.v n) (SZ.v source) /\
      vc1 >= reveal vc0 /\ vc1 - reveal vc0 == SZ.v n
    )
{
  let mut v: SZ.t = 0sz;

  while (
    let vv = !v;
    vv <^ n
  )
  invariant exists* vv sdist_v spred_v (vc_v: nat).
    R.pts_to v vv **
    A.pts_to dist sdist_v **
    A.pts_to pred spred_v **
    V.pts_to visited svisited_now **
    A.pts_to weights sweights **
    GR.pts_to ctr vc_v **
    pure (
      SZ.v vv <= SZ.v n /\
      SZ.v n > 0 /\
      SZ.v u < SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      all_weights_non_negative sweights /\
      Seq.length sdist_v == SZ.v n /\
      Seq.length spred_v == SZ.v n /\
      Seq.length sdist_pre == SZ.v n /\
      Seq.length spred_pre == SZ.v n /\
      Seq.length svisited_pre == SZ.v n /\
      Seq.index svisited_pre (SZ.v u) = 0 /\
      tri_from_visited sweights sdist_pre svisited_pre (SZ.v n) /\
      visited_le_unvisited sdist_pre svisited_pre (SZ.v n) /\
      (forall (j: nat). j < SZ.v n /\ Seq.index svisited_pre j = 0 ==>
        Seq.index sdist_pre (SZ.v u) <= Seq.index sdist_pre j) /\
      Seq.index sdist_v (SZ.v source) == 0 /\
      all_non_negative sdist_v /\
      all_bounded sdist_v /\
      (forall (j: nat). j < SZ.v n ==>
        (Seq.index svisited_now j = 0 \/
         Seq.index svisited_now j = 1)) /\
      svisited_now == Seq.upd svisited_pre (SZ.v u) 1 /\
      (forall (x: nat). x < SZ.v n /\ (Seq.index svisited_pre x = 1 \/ x = SZ.v u) ==>
        Seq.index sdist_v x == Seq.index sdist_pre x) /\
      (forall (j: nat). j < SZ.v n ==>
        Seq.index sdist_v j <= Seq.index sdist_pre j) /\
      (forall (v': nat). v' < SZ.v vv /\ v' < SZ.v n /\
        SZ.v u * SZ.v n + v' < Seq.length sweights ==>
        (let w = Seq.index sweights (SZ.v u * SZ.v n + v') in
         let d_u = Seq.index sdist_v (SZ.v u) in
         (w < SP.inf /\ d_u < SP.inf) ==> Seq.index sdist_v v' <= d_u + w)) /\
      (forall (j: nat). j < SZ.v n /\ Seq.index svisited_pre j = 0 ==>
        Seq.index sdist_v j >= Seq.index sdist_pre (SZ.v u)) /\
      (forall (v': nat). v' < SZ.v vv /\ v' < SZ.v n ==>
        (Seq.index sdist_v v' == Seq.index sdist_pre v' /\
         Seq.index spred_v v' == Seq.index spred_pre v') \/
        (Seq.index sdist_v v' == Seq.index sdist_pre (SZ.v u) + Seq.index sweights (SZ.v u * SZ.v n + v') /\
         Seq.index sdist_v v' < Seq.index sdist_pre v' /\
         Seq.index sweights (SZ.v u * SZ.v n + v') < SP.inf /\
         Seq.index sdist_pre (SZ.v u) < SP.inf /\
         SZ.v (Seq.index spred_v v') == SZ.v u)) /\
      (forall (v': nat). v' >= SZ.v vv /\ v' < SZ.v n ==>
        Seq.index sdist_v v' == Seq.index sdist_pre v' /\
        Seq.index spred_v v' == Seq.index spred_pre v') /\
      vc_v == reveal vc0 + SZ.v vv /\
      dist_ge_sp_dist sdist_pre sweights (SZ.v n) (SZ.v source) /\
      pred_ok spred_pre sdist_pre sweights svisited_pre (SZ.v n) (SZ.v source)
    )
  decreases (SZ.v n - SZ.v !v)
  {
    let vv = !v;
    with sdist_v. assert (A.pts_to dist sdist_v);

    // Explicit fact about abstract inf for SMT
    assert pure (SP.inf > 0);

    lemma_2d_index_fits (SZ.v u) (SZ.v vv) (SZ.v n);
    let w_idx = u *^ n +^ vv;
    let w = A.op_Array_Access weights w_idx;

    let visited_v = V.op_Array_Access visited vv;
    let old_dist = A.op_Array_Access dist vv;
    let old_pred = A.op_Array_Access pred vv;

    let can_relax = (visited_v = 0 && w < SP.inf && dist_u < SP.inf);
    let sum = dist_u + w;
    let should_update = (can_relax && sum < old_dist);
    let new_dist: int = (if should_update then sum else old_dist);
    let new_pred: SZ.t = (if should_update then u else old_pred);

    // Help SMT: u's dist is preserved and relaxation holds for edge (u,vv)
    assert pure (Seq.index sdist_v (SZ.v u) == dist_u);
    assert pure ((w < SP.inf /\ dist_u < SP.inf) ==> new_dist <= dist_u + w);
    assert pure (Seq.index (Seq.upd sdist_v (SZ.v vv) new_dist) (SZ.v u) == dist_u);
    extend_relaxed_from_u sdist_v sweights (SZ.v n) (SZ.v u) (SZ.v vv) new_dist dist_u;

    A.op_Array_Assignment dist vv new_dist;
    A.op_Array_Assignment pred vv new_pred;

    tick ctr;

    v := vv +^ 1sz;
  };

  let _ = !v;

  // Apply bridge lemma to establish ghost invariants
  with sdist_after. assert (A.pts_to dist sdist_after);
  with spred_after. assert (A.pts_to pred spred_after);

  assert (pure (Seq.index svisited_pre (SZ.v u) = 0));
  assert (pure (tri_from_visited sweights sdist_pre svisited_pre (SZ.v n)));
  assert (pure (visited_le_unvisited sdist_pre svisited_pre (SZ.v n)));
  assert (pure (forall (j: nat). j < SZ.v n /\ Seq.index svisited_pre j = 0 ==>
    Seq.index sdist_pre (SZ.v u) <= Seq.index sdist_pre j));
  assert (pure (forall (x: nat). x < SZ.v n /\ Seq.index svisited_pre x = 1 ==>
    Seq.index sdist_after x == Seq.index sdist_pre x));
  assert (pure (Seq.index sdist_after (SZ.v u) == Seq.index sdist_pre (SZ.v u)));

  extend_tri_after_relax sweights sdist_pre sdist_after svisited_pre (SZ.v n) (SZ.v u);

  relax_round_lb_post sdist_pre sdist_after sweights (SZ.v n) (SZ.v source) (SZ.v u);

  relax_round_pred_ok sweights sdist_pre sdist_after spred_pre spred_after svisited_pre (SZ.v n) (SZ.v source) (SZ.v u);

  // Help SMT connect svisited_now with Seq.upd svisited_pre
  assert (pure (svisited_now == Seq.upd svisited_pre (SZ.v u) 1));
  assert (pure (tri_from_visited sweights sdist_after svisited_now (SZ.v n)));
  assert (pure (visited_le_unvisited sdist_after svisited_now (SZ.v n)));
}
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
//SNIPPET_START: dijkstra_sig
fn dijkstra
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (pred: A.array SZ.t)
  (ctr: GR.ref nat)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#spred: erased (Seq.seq SZ.t))
  (#c0: erased nat)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    A.pts_to pred spred **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length spred == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      all_weights_non_negative sweights
    )
  ensures exists* sdist' spred' (cf: nat).
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    A.pts_to pred spred' **
    GR.pts_to ctr cf **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      all_non_negative sdist' /\
      all_bounded sdist' /\
      triangle_inequality sweights sdist' (SZ.v n) /\
      (forall (v: nat). v < SZ.v n ==>
        Seq.index sdist' v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v) /\
      pred_consistent spred' sdist' sweights (SZ.v n) (SZ.v source) /\
      dijkstra_complexity_bounded cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: dijkstra_sig
{
  // Initialization: dist[source] = 0, all others = inf; pred[v] = v
  let mut init_i: SZ.t = 0sz;
  
  while (
    let vi = !init_i;
    vi <^ n
  )
  invariant exists* vi sdist_current spred_current (vc: nat).
    R.pts_to init_i vi **
    A.pts_to dist sdist_current **
    A.pts_to pred spred_current **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      Seq.length spred_current == SZ.v n /\
      (SZ.v vi > SZ.v source ==> Seq.index sdist_current (SZ.v source) == 0) /\
      (forall (j:nat). j < SZ.v vi ==> 
        Seq.index sdist_current j >= 0 /\ Seq.index sdist_current j <= SP.inf) /\
      (forall (j:nat). j < SZ.v vi /\ j <> SZ.v source ==>
        Seq.index sdist_current j == SP.inf) /\
      (forall (j:nat). j < SZ.v vi ==> SZ.v (Seq.index spred_current j) == j) /\
      vc == reveal c0 + SZ.v vi
    )
  decreases (SZ.v n - SZ.v !init_i)
  {
    let vi = !init_i;
    let new_val: int = (if vi = source then 0 else SP.inf);
    A.op_Array_Assignment dist vi new_val;
    A.op_Array_Assignment pred vi vi;
    tick ctr;
    init_i := vi +^ 1sz;
  };
  
  let _ = !init_i;
  
  // Establish dist >= sp_dist after initialization
  with sdist_init. assert (A.pts_to dist sdist_init);
  init_dist_ge_sp_dist sdist_init sweights (SZ.v n) (SZ.v source);
  
  // Capture pred state after init
  with spred_init. assert (A.pts_to pred spred_init);
  
  // Allocate visited array (all 0 initially)
  let visited = V.alloc 0 n;
  
  // Establish count_ones for initial visited array
  with svisited_init. assert (V.pts_to visited svisited_init);
  count_ones_all_zero svisited_init (SZ.v n);
  
  // Main loop: n iterations
  let mut round: SZ.t = 0sz;
  
  while (
    let vround = !round;
    vround <^ n
  )
  invariant exists* vround sdist_current spred_current svisited_current (vc: nat).
    R.pts_to round vround **
    A.pts_to dist sdist_current **
    A.pts_to pred spred_current **
    V.pts_to visited svisited_current **
    GR.pts_to ctr vc **
    pure (
      SZ.v vround <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      Seq.length spred_current == SZ.v n /\
      Seq.length svisited_current == SZ.v n /\
      Seq.index sdist_current (SZ.v source) == 0 /\
      all_non_negative sdist_current /\
      all_bounded sdist_current /\
      all_weights_non_negative sweights /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      (forall (j: nat). j < SZ.v n ==>
        (Seq.index svisited_current j = 0 \/ Seq.index svisited_current j = 1)) /\
      tri_from_visited sweights sdist_current svisited_current (SZ.v n) /\
      visited_le_unvisited sdist_current svisited_current (SZ.v n) /\
      count_ones svisited_current (SZ.v n) == SZ.v vround /\
      dist_ge_sp_dist sdist_current sweights (SZ.v n) (SZ.v source) /\
      pred_ok spred_current sdist_current sweights svisited_current (SZ.v n) (SZ.v source) /\
      vc == reveal c0 + SZ.v n + 2 * SZ.v vround * SZ.v n
    )
  decreases (SZ.v n - SZ.v !round)
  {
    let vround = !round;
    
    // Find minimum distance unvisited vertex — n ticks
    let u = find_min_unvisited dist visited n ctr;
    
    // Ghost: capture state before marking
    with sdist_pre. assert (A.pts_to dist sdist_pre);
    with spred_pre. assert (A.pts_to pred spred_pre);
    with svisited_pre. assert (V.pts_to visited svisited_pre);
    
    // Resolve has_min_dist_unvisited disjunction: u must be unvisited
    count_ones_not_all_visited svisited_pre (SZ.v n);
    
    // Mark u as visited
    V.op_Array_Assignment visited u 1;
    
    // Update count_ones after marking
    count_ones_mark svisited_pre (SZ.v n) (SZ.v u);
    
    // Get dist[u] — cached, won't change during relaxation
    let dist_u = A.op_Array_Access dist u;
    
    // Relax all neighbors of u — n ticks (also updates pred)
    dijkstra_relax_round weights n source dist pred visited u dist_u ctr
      #sweights #sdist_pre #spred_pre #svisited_pre;
    
    // Help SMT connect postcondition to loop invariant
    with sdist_after. assert (A.pts_to dist sdist_after);
    with spred_after. assert (A.pts_to pred spred_after);
    with svisited_after. assert (V.pts_to visited svisited_after);
    assert (pure (pred_ok spred_after sdist_after sweights svisited_after (SZ.v n) (SZ.v source)));
    
    round := vround +^ 1sz;
  };
  
  let _ = !round;
  
  // After main loop: all vertices visited → full triangle inequality
  with sdist_final. assert (A.pts_to dist sdist_final);
  with spred_final. assert (A.pts_to pred spred_final);
  with svisited_final. assert (V.pts_to visited svisited_final);
  count_ones_full svisited_final (SZ.v n);
  all_visited_tri_is_full sweights sdist_final svisited_final (SZ.v n);
  assert (pure (triangle_inequality sweights sdist_final (SZ.v n)));
  assert (pure (dist_ge_sp_dist sdist_final sweights (SZ.v n) (SZ.v source)));
  assert (pure (pred_ok spred_final sdist_final sweights svisited_final (SZ.v n) (SZ.v source)));
  
  // Free visited array
  V.free visited;
  
  // Derive upper bound from triangle inequality
  dijkstra_sp_upper_bound sdist_final sweights (SZ.v n) (SZ.v source);
  assert (pure (forall (v: nat). v < SZ.v n ==>
    Seq.index sdist_final v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v));
  // pred_consistent follows from pred_ok
  assert (pure (pred_consistent spred_final sdist_final sweights (SZ.v n) (SZ.v source)));
}
#pop-options

