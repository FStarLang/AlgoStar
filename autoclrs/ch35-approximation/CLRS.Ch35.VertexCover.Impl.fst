module CLRS.Ch35.VertexCover.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open FStar.List.Tot
open CLRS.Ch35.VertexCover.Spec
open CLRS.Ch35.VertexCover.Lemmas

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = CLRS.Ch35.VertexCover.Spec
module Lemmas = CLRS.Ch35.VertexCover.Lemmas
module GR = Pulse.Lib.GhostReference

// 2-approximation vertex cover algorithm from CLRS Chapter 35.
// Given an adjacency matrix for an undirected graph with n vertices,
// returns a cover array where cover[i] = 1 if vertex i is in the cover.
//
// NOTE: The algorithm scans only upper-triangular entries (u < v),
// which is correct for undirected graphs where adj[u*n+v] = adj[v*n+u].

// Lemma: is_cover with bound_v <= bound_u implies is_cover at next value
let is_cover_skip_to (s_adj s_cover: Seq.seq int) (n: nat) (u v: nat)
  : Lemma 
    (requires Spec.is_cover s_adj s_cover n u 0 /\ v <= u + 1)
    (ensures Spec.is_cover s_adj s_cover n u v)
  = ()

// Lemma: is_cover with bound_v >= n is equivalent to advancing to next row
let is_cover_next_row (s_adj s_cover: Seq.seq int) (n: nat) (u: nat)
  : Lemma 
    (requires Spec.is_cover s_adj s_cover n u n /\ u < n)
    (ensures Spec.is_cover s_adj s_cover n (u + 1) 0)
  = ()

// Lemma: updating cover preserves is_cover when the update only sets values to non-zero
#push-options "--z3rlimit 30"
let is_cover_step (s_adj s_cover: Seq.seq int) (n vu vv: nat) 
  (cu cv has_edge: int) (new_cu new_cv: int)
  : Lemma
    (requires
      Spec.is_cover s_adj s_cover n vu vv /\
      vu < n /\ vv < n /\ vu < vv /\
      cu == Seq.index s_cover vu /\
      cv == Seq.index s_cover vv /\
      has_edge == Seq.index s_adj (vu * n + vv) /\
      new_cu == (if has_edge <> 0 && cu = 0 && cv = 0 then 1 else cu) /\
      new_cv == (if has_edge <> 0 && cu = 0 && cv = 0 then 1 else cv))
    (ensures (
      let s1 = Seq.upd s_cover vu new_cu in
      let s2 = Seq.upd s1 vv new_cv in
      Spec.is_cover s_adj s2 n vu (vv + 1)))
  = let s1 = Seq.upd s_cover vu new_cu in
    let s2 = Seq.upd s1 vv new_cv in
    assert (forall (u v: nat). ((u < vu \/ (u == vu /\ v < vv + 1)) /\ u < n /\ v < n /\ u < v /\
      Seq.index s_adj (u * n + v) <> 0) ==>
      (Seq.index s2 u <> 0 \/ Seq.index s2 v <> 0))
#pop-options

// Lemma: updating cover with 0/1 values preserves binary property
let is_cover_binary_step (s_cover: Seq.seq int) (n vu vv: nat) 
  (cu cv: int) (new_cu new_cv: int)
  : Lemma
    (requires
      vu < n /\ vv < n /\
      Seq.length s_cover == n /\
      (forall (i: nat). i < n ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
      cu == Seq.index s_cover vu /\
      cv == Seq.index s_cover vv /\
      (new_cu = 0 \/ new_cu = 1) /\
      (new_cv = 0 \/ new_cv = 1))
    (ensures (
      let s1 = Seq.upd s_cover vu new_cu in
      let s2 = Seq.upd s1 vv new_cv in
      forall (i: nat). i < n ==> (Seq.index s2 i = 0 \/ Seq.index s2 i = 1)))
  = let s1 = Seq.upd s_cover vu new_cu in
    let s2 = Seq.upd s1 vv new_cv in
    assert (forall (i: nat). (i < n /\ i <> vu /\ i <> vv) ==> Seq.index s2 i == Seq.index s_cover i)

// Matching invariant: the ghost matching explains the cover
let matching_inv (s_adj s_cover: Seq.seq int) (n: nat) (m: list Spec.edge) : prop =
  Seq.length s_adj = n * n /\
  Seq.length s_cover = n /\
  Spec.pairwise_disjoint m /\
  (forall (e: Spec.edge). memP e m ==>
    (let (u, v) = e in u < n /\ v < n /\ u <> v /\ u < v /\ Seq.index s_adj (u * n + v) <> 0)) /\
  (forall (x: nat). x < n ==>
    ((Seq.index s_cover x <> 0) == existsb (fun (e: Spec.edge) -> Spec.edge_uses_vertex e x) m))

// Helper: existsb returning false means f is false for all elements
let rec existsb_false_means_all_false (#a: Type) (f: a -> bool) (l: list a)
  : Lemma (requires existsb f l == false)
          (ensures forall (x: a). memP x l ==> f x == false)
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> existsb_false_means_all_false f tl

// Step lemma: matching_inv is maintained after processing edge (vu, vv)
#push-options "--z3rlimit 40"
let matching_inv_step (s_adj s_cover: Seq.seq int) (n vu vv: nat) (m: list Spec.edge)
  (cu cv has_edge: int) (new_cu new_cv: int)
  : Lemma
    (requires
      matching_inv s_adj s_cover n m /\
      Seq.length s_adj = n * n /\
      Seq.length s_cover = n /\
      vu < n /\ vv < n /\ vu < vv /\
      cu == Seq.index s_cover vu /\
      cv == Seq.index s_cover vv /\
      has_edge == Seq.index s_adj (vu * n + vv) /\
      new_cu == (if has_edge <> 0 && cu = 0 && cv = 0 then 1 else cu) /\
      new_cv == (if has_edge <> 0 && cu = 0 && cv = 0 then 1 else cv))
    (ensures (
      let s1 = Seq.upd s_cover vu new_cu in
      let s2 = Seq.upd s1 vv new_cv in
      let new_m = if has_edge <> 0 && cu = 0 && cv = 0 then (vu, vv) :: m else m in
      matching_inv s_adj s2 n new_m))
  = let s1 = Seq.upd s_cover vu new_cu in
    let s2 = Seq.upd s1 vv new_cv in
    if has_edge <> 0 && cu = 0 && cv = 0 then (
      existsb_false_means_all_false (fun (e: Spec.edge) -> Spec.edge_uses_vertex e vu) m;
      existsb_false_means_all_false (fun (e: Spec.edge) -> Spec.edge_uses_vertex e vv) m
    ) else ()
#pop-options

// Lemma: Apply the approximation bound for all possible opt values
let apply_approximation_bound (s_adj s_cover: Seq.seq int) (n: nat) (m: list Spec.edge)
  : Lemma (requires 
            Spec.is_cover s_adj s_cover n n 0 /\
            Seq.length s_cover = n /\
            Seq.length s_adj = n * n /\
            (forall (i: nat). i < n ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
            matching_inv s_adj s_cover n m)
          (ensures 
            forall (opt: nat). Spec.min_vertex_cover_size s_adj n opt ==>
              Spec.count_cover (Spec.seq_to_cover_fn s_cover n) n <= 2 * opt)
  = let bound (c_opt: Spec.cover_fn)
      : Lemma (requires Spec.is_valid_graph_cover s_adj n c_opt)
              (ensures Spec.count_cover (Spec.seq_to_cover_fn s_cover n) n <= 2 * Spec.count_cover c_opt n) =
      Lemmas.approximation_ratio_theorem s_adj s_cover n m c_opt
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires bound)

//SNIPPET_START: approx_vertex_cover
fn approx_vertex_cover
  (#p: perm)
  (adj: array int)
  (#s_adj: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires 
    A.pts_to adj #p s_adj ** 
    pure (
      SZ.v n > 0 /\ 
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length s_adj == SZ.v n * SZ.v n
    )
  returns cover: V.vec int
  ensures exists* s_cover.
    A.pts_to adj #p s_adj **
    V.pts_to cover s_cover **
    pure (
      Seq.length s_cover == SZ.v n /\
      Spec.is_cover s_adj s_cover (SZ.v n) (SZ.v n) 0 /\
      (forall (i: nat). i < SZ.v n ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
      (exists (opt: nat). Spec.min_vertex_cover_size s_adj (SZ.v n) opt) /\
      (forall (opt: nat). Spec.min_vertex_cover_size s_adj (SZ.v n) opt ==>
        Spec.count_cover (Spec.seq_to_cover_fn s_cover (SZ.v n)) (SZ.v n) <= 2 * opt)
    )
//SNIPPET_END: approx_vertex_cover
{
  // Initialize cover array with all zeros
  let cover = V.alloc 0 n;
  V.to_array_pts_to cover;
  let cover_a = V.vec_to_array cover;
  rewrite (A.pts_to (V.vec_to_array cover) (Seq.create (SZ.v n) 0))
       as (A.pts_to cover_a (Seq.create (SZ.v n) 0));
  
  // Ghost matching: tracks edges selected by the algorithm
  let matching_ref = GR.alloc #(list Spec.edge) [];
  
  // Outer loop: u from 0 to n-1
  let mut u: SZ.t = 0sz;
  
  while (!u <^ n)
  invariant exists* vu s_cover vm.
    R.pts_to u vu **
    A.pts_to adj #p s_adj **
    A.pts_to cover_a s_cover **
    GR.pts_to matching_ref vm **
    pure (
      SZ.v vu <= SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length s_cover == SZ.v n /\
      Spec.is_cover s_adj s_cover (SZ.v n) (SZ.v vu) 0 /\
      (forall (i: nat). i < SZ.v n ==> (Seq.index s_cover i = 0 \/ Seq.index s_cover i = 1)) /\
      matching_inv s_adj s_cover (SZ.v n) vm
    )
  decreases (SZ.v n - SZ.v !u)
  {
    let vu = !u;
    
    // Skip from (vu, 0) to (vu, vu+1)
    with s_cov0. assert (A.pts_to cover_a s_cov0);
    is_cover_skip_to s_adj s_cov0 (SZ.v n) (SZ.v vu) (SZ.v vu + 1);
    
    // Inner loop: v from u+1 to n-1
    let mut v: SZ.t = vu +^ 1sz;
    
    while (!v <^ n)
    invariant exists* vv s_cover_inner vm_inner.
      R.pts_to u vu **
      R.pts_to v vv **
      A.pts_to adj #p s_adj **
      A.pts_to cover_a s_cover_inner **
      GR.pts_to matching_ref vm_inner **
      pure (
        SZ.v vv >= SZ.v vu + 1 /\
        SZ.v vv <= SZ.v n /\
        SZ.v vu < SZ.v n /\
        SZ.fits (SZ.v vu * SZ.v n) /\
        SZ.fits (SZ.v vu * SZ.v n + SZ.v n) /\
        Seq.length s_cover_inner == SZ.v n /\
        Spec.is_cover s_adj s_cover_inner (SZ.v n) (SZ.v vu) (SZ.v vv) /\
        (forall (i: nat). i < SZ.v n ==> (Seq.index s_cover_inner i = 0 \/ Seq.index s_cover_inner i = 1)) /\
        matching_inv s_adj s_cover_inner (SZ.v n) vm_inner
      )
    decreases (SZ.v n - SZ.v !v)
    {
      let vv = !v;
      
      with s_cov_before. assert (A.pts_to cover_a s_cov_before);
      with vm_cur. assert (GR.pts_to matching_ref vm_cur);
      
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
      
      // Prove the binary property is preserved
      is_cover_binary_step s_cov_before (SZ.v n) (SZ.v vu) (SZ.v vv) cu cv new_cu new_cv;
      
      // Prove the matching invariant is preserved
      matching_inv_step s_adj s_cov_before (SZ.v n) (SZ.v vu) (SZ.v vv) vm_cur cu cv has_edge new_cu new_cv;
      
      // Write unconditionally
      A.op_Array_Assignment cover_a vu new_cu;
      A.op_Array_Assignment cover_a vv new_cv;
      
      // Ghost: update matching
      let new_vm : Ghost.erased (list Spec.edge) =
        Ghost.hide (if has_edge <> 0 && cu = 0 && cv = 0
                    then ((SZ.v vu, SZ.v vv) :: Ghost.reveal vm_cur)
                    else Ghost.reveal vm_cur);
      GR.op_Colon_Equals matching_ref new_vm;
      
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
  with vm_final. assert (GR.pts_to matching_ref vm_final);
  
  // Binary property is maintained by loop invariant
  assert pure (forall (i: nat). i < SZ.v n ==> (Seq.index s_final i = 0 \/ Seq.index s_final i = 1));
  
  // Apply 2-approximation theorem using ghost matching
  apply_approximation_bound s_adj s_final (SZ.v n) vm_final;
  
  // Prove existence of minimum vertex cover (makes 2-approx non-vacuous)
  Lemmas.min_cover_exists s_adj (SZ.v n);
  
  // Free ghost matching reference
  GR.free matching_ref;
  
  assert pure (Spec.is_cover s_adj s_final (SZ.v n) (SZ.v n) 0);
  assert pure (Seq.length s_final == SZ.v n);
  assert pure (forall (i: nat). i < SZ.v n ==> (Seq.index s_final i = 0 \/ Seq.index s_final i = 1));
  
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
 * FULLY PROVEN (0 admits):
 * - The output is a valid vertex cover (is_cover).
 * - The output cover consists only of 0/1 values.
 * - The postcondition includes the 2-approximation bound:
 *     count_cover(cover) <= 2 * OPT
 *   where OPT is the size of the minimum vertex cover.
 *
 * PROOF TECHNIQUE:
 * A ghost reference tracks the "matching" — the set of edges that triggered
 * vertex additions during execution. The loop invariants ensure:
 * 1. The matching is pairwise disjoint (no shared vertices)
 * 2. The cover consists exactly of the matching endpoints
 * 3. Each matching edge is a valid graph edge
 * Then Lemmas.approximation_ratio_theorem applies CLRS Theorem 35.1:
 *   |cover| = 2|matching| ≤ 2 * count(any valid cover) ≤ 2 * OPT
 *)
