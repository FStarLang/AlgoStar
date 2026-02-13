module CLRS.Ch35.VertexCover
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// 2-approximation vertex cover algorithm from CLRS Chapter 35
// Given an adjacency matrix for an undirected graph with n vertices,
// returns a cover array where cover[i] = 1 if vertex i is in the cover

// Cover property: every edge (u,v) with u < v is covered by the cover array
// (at least one endpoint is in the cover)
let is_cover (s_adj s_cover: Seq.seq int) (n: nat) (bound_u bound_v: nat) : prop =
  Seq.length s_adj == n * n /\
  Seq.length s_cover == n /\
  (forall (u v: nat). (u < bound_u \/ (u == bound_u /\ v < bound_v)) ==>
    u < n ==> v < n ==> u < v ==>
    Seq.index s_adj (u * n + v) <> 0 ==>
    (Seq.index s_cover u <> 0 \/ Seq.index s_cover v <> 0))

// Lemma: is_cover with bound_v <= bound_u implies is_cover at next value
// since no edges (u,v) with u=bound_u, v < bound_v satisfy u < v when bound_v <= bound_u
let is_cover_skip_to (s_adj s_cover: Seq.seq int) (n: nat) (u v: nat)
  : Lemma 
    (requires is_cover s_adj s_cover n u 0 /\ v <= u + 1)
    (ensures is_cover s_adj s_cover n u v)
  = ()

// Lemma: is_cover with bound_v >= n is equivalent to advancing to next row
let is_cover_next_row (s_adj s_cover: Seq.seq int) (n: nat) (u: nat)
  : Lemma 
    (requires is_cover s_adj s_cover n u n /\ u < n)
    (ensures is_cover s_adj s_cover n (u + 1) 0)
  = ()

// Lemma: updating cover preserves is_cover when the update only sets values to non-zero
// After writing cover[vu] := new_cu and cover[vv] := new_cv,
// the cover property is preserved for previously covered edges,
// and the current edge (vu, vv) becomes covered
#push-options "--z3rlimit 30"
let is_cover_step (s_adj s_cover: Seq.seq int) (n vu vv: nat) 
  (cu cv has_edge: int) (new_cu new_cv: int)
  : Lemma
    (requires
      is_cover s_adj s_cover n vu vv /\
      vu < n /\ vv < n /\ vu < vv /\
      cu == Seq.index s_cover vu /\
      cv == Seq.index s_cover vv /\
      has_edge == Seq.index s_adj (vu * n + vv) /\
      new_cu == (if has_edge <> 0 && cu = 0 && cv = 0 then 1 else cu) /\
      new_cv == (if has_edge <> 0 && cu = 0 && cv = 0 then 1 else cv))
    (ensures (
      let s1 = Seq.upd s_cover vu new_cu in
      let s2 = Seq.upd s1 vv new_cv in
      is_cover s_adj s2 n vu (vv + 1)))
  = let s1 = Seq.upd s_cover vu new_cu in
    let s2 = Seq.upd s1 vv new_cv in
    assert (forall (u v: nat). ((u < vu \/ (u == vu /\ v < vv + 1)) /\ u < n /\ v < n /\ u < v /\
      Seq.index s_adj (u * n + v) <> 0) ==>
      (Seq.index s2 u <> 0 \/ Seq.index s2 v <> 0))
#pop-options

fn approx_vertex_cover
  (#p: perm)
  (adj: array int)
  (#s_adj: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires 
    A.pts_to adj #p s_adj ** 
    pure (
      SZ.v n > 0 /\ 
      SZ.v n < 256 /\  // Much smaller bound to ensure n*n fits
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length s_adj == SZ.v n * SZ.v n
    )
  returns cover: V.vec int
  ensures exists* s_cover.
    A.pts_to adj #p s_adj **
    V.pts_to cover s_cover **
    pure (
      Seq.length s_cover == SZ.v n /\
      is_cover s_adj s_cover (SZ.v n) (SZ.v n) 0
    )
{
  // Initialize cover array with all zeros
  let cover = V.alloc 0 n;
  V.to_array_pts_to cover;
  let cover_a = V.vec_to_array cover;
  rewrite (A.pts_to (V.vec_to_array cover) (Seq.create (SZ.v n) 0))
       as (A.pts_to cover_a (Seq.create (SZ.v n) 0));
  
  // Outer loop: u from 0 to n-1
  let mut u: SZ.t = 0sz;
  
  while (!u <^ n)
  invariant exists* vu s_cover.
    R.pts_to u vu **
    A.pts_to adj #p s_adj **
    A.pts_to cover_a s_cover **
    pure (
      SZ.v vu <= SZ.v n /\
      SZ.v n < 256 /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length s_cover == SZ.v n /\
      is_cover s_adj s_cover (SZ.v n) (SZ.v vu) 0
    )
  {
    let vu = !u;
    
    // Skip from (vu, 0) to (vu, vu+1)
    with s_cov0. assert (A.pts_to cover_a s_cov0);
    is_cover_skip_to s_adj s_cov0 (SZ.v n) (SZ.v vu) (SZ.v vu + 1);
    
    // Inner loop: v from u+1 to n-1
    let mut v: SZ.t = vu +^ 1sz;
    
    while (!v <^ n)
    invariant exists* vv s_cover_inner.
      R.pts_to u vu **
      R.pts_to v vv **
      A.pts_to adj #p s_adj **
      A.pts_to cover_a s_cover_inner **
      pure (
        SZ.v vv >= SZ.v vu + 1 /\
        SZ.v vv <= SZ.v n /\
        SZ.v vu < SZ.v n /\
        SZ.v n < 256 /\
        SZ.fits (SZ.v vu * SZ.v n) /\
        SZ.fits (SZ.v vu * SZ.v n + SZ.v n) /\
        Seq.length s_cover_inner == SZ.v n /\
        is_cover s_adj s_cover_inner (SZ.v n) (SZ.v vu) (SZ.v vv)
      )
    {
      let vv = !v;
      
      with s_cov_before. assert (A.pts_to cover_a s_cov_before);
      
      // Calculate adjacency matrix index: u*n + v
      let u_times_n = vu *^ n;
      let idx = u_times_n +^ vv;
      
      // Read values
      let cu = A.op_Array_Access cover_a vu;
      let cv = A.op_Array_Access cover_a vv;
      let has_edge = A.op_Array_Access adj idx;
      
      // Compute new values (unconditionally)
      let new_cu = (if has_edge <> 0 && cu = 0 && cv = 0 then 1 else cu);
      let new_cv = (if has_edge <> 0 && cu = 0 && cv = 0 then 1 else cv);
      
      // Prove the step preserves the cover property
      is_cover_step s_adj s_cov_before (SZ.v n) (SZ.v vu) (SZ.v vv) cu cv has_edge new_cu new_cv;
      
      // Write unconditionally
      A.op_Array_Assignment cover_a vu new_cu;
      A.op_Array_Assignment cover_a vv new_cv;
      
      // Increment v
      v := vv +^ 1sz;
    };
    
    // After inner loop: advance from (vu, n) to (vu+1, 0)
    with s_cov_row. assert (A.pts_to cover_a s_cov_row);
    is_cover_next_row s_adj s_cov_row (SZ.v n) (SZ.v vu);
    
    // Increment u
    u := vu +^ 1sz;
  };
  
  // Convert back to vec for return
  with s_final. assert (A.pts_to cover_a s_final);
  rewrite (A.pts_to cover_a s_final) as (A.pts_to (V.vec_to_array cover) s_final);
  V.to_vec_pts_to cover;
  cover
}

(* 
 * 2-APPROXIMATION ANALYSIS (CLRS Theorem 35.1)
 *
 * The algorithm implements APPROX-VERTEX-COVER from CLRS:
 * It scans all edges (u,v) with u < v. When an edge is found where
 * neither endpoint is covered (cover[u]=0, cover[v]=0), it adds BOTH
 * endpoints to the cover.
 *
 * PROVEN: The output is a valid vertex cover (is_cover).
 *
 * NOT YET PROVEN (but true): The output has size ≤ 2 × |OPT|.
 * 
 * The 2-approximation argument:
 * 1. The edges (u,v) where the algorithm adds both endpoints form a MATCHING:
 *    no two such edges share an endpoint (because after adding u and v,
 *    neither will be 0 again, so no future edge involving u or v triggers
 *    the addition).
 * 2. |cover| = 2 × |matching| (each matching edge contributes exactly 2 vertices).
 * 3. Any vertex cover must include ≥ 1 endpoint of each matching edge.
 * 4. Since matching edges have disjoint endpoints, these cover vertices are
 *    distinct: |OPT| ≥ |matching|.
 * 5. Therefore: |cover| = 2|matching| ≤ 2|OPT|.
 *
 * To mechanize this proof, one would need:
 * - A ghost counter for matching edges (GhostReference.ref nat)
 * - A ghost predicate tracking that matching edges have disjoint endpoints
 * - A pure lemma connecting matching size to cover size
 * - The pigeonhole argument for step 4
 *)
