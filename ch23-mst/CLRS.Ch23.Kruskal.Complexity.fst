(*
   Kruskal's MST Algorithm with Complexity Bound

   CLRS §23.2: Kruskal's algorithm complexity:
   - With adjacency matrix: must scan V² entries to find edges
   - For each of (V-1) rounds: find minimum weight edge among V² candidates
   - Each find-min operation: O(V²) comparisons
   - Union-find operations: O(V) per operation with simple find
   - Total: (V-1) × (V² + V) = O(V³)
   
   However, the current implementation processes V-1 rounds, and in each round:
   - Scans V² edge positions: O(V²)
   - Performs 2 finds + 1 union: O(V) each with simple find
   - Total per round: O(V²)
   - Overall: (V-1) × V² = O(V³)

   This module instruments the algorithm with ghost tick counters to prove
   the cubic complexity bound: ticks ≤ 4 × V³.

   Uses GhostReference for tick counter — fully erased at runtime.
*)

module CLRS.Ch23.Kruskal.Complexity
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
module V = Pulse.Lib.Vec

// ========== Predicates from original Kruskal ==========

[@@"opaque_to_smt"]
let valid_parents (sparent: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length sparent == n /\
  (forall (i: nat). i < n ==> SZ.v (Seq.index sparent i) < n)

[@@"opaque_to_smt"]
let valid_endpoints (seu sev: Seq.seq int) (n ec: nat) : prop =
  ec <= n /\
  Seq.length seu == n /\ Seq.length sev == n /\
  (forall (k: nat). k < ec ==>
    Seq.index seu k >= 0 /\ Seq.index seu k < n /\
    Seq.index sev k >= 0 /\ Seq.index sev k < n)

// ========== Lemmas for valid_parents ==========

let establish_valid_parents (sparent: Seq.seq SZ.t) (n: nat)
  : Lemma (requires Seq.length sparent == n /\
                    (forall (j: nat). j < n ==> SZ.v (Seq.index sparent j) < n))
          (ensures valid_parents sparent n)
  = reveal_opaque (`%valid_parents) (valid_parents sparent n)

let valid_parents_length (sparent: Seq.seq SZ.t) (n: nat)
  : Lemma (requires valid_parents sparent n)
          (ensures Seq.length sparent == n)
  = reveal_opaque (`%valid_parents) (valid_parents sparent n)

let valid_parents_index (sparent: Seq.seq SZ.t) (n: nat) (i:nat{i < Seq.length sparent})
  : Lemma (requires valid_parents sparent n /\ i < n)
          (ensures SZ.v (Seq.index sparent i) < n)
  = reveal_opaque (`%valid_parents) (valid_parents sparent n)

let valid_parents_seq_upd (sparent: Seq.seq SZ.t) (n i: nat) (v: SZ.t)
  : Lemma (requires valid_parents sparent n /\ i < n /\ SZ.v v < n /\ Seq.length sparent == n)
          (ensures valid_parents (Seq.upd sparent i v) n)
  = reveal_opaque (`%valid_parents) (valid_parents sparent n);
    reveal_opaque (`%valid_parents) (valid_parents (Seq.upd sparent i v) n)

// ========== Lemmas for valid_endpoints ==========

let establish_valid_endpoints_empty (seu sev: Seq.seq int) (n: nat)
  : Lemma (requires Seq.length seu == n /\ Seq.length sev == n)
          (ensures valid_endpoints seu sev n 0)
  = reveal_opaque (`%valid_endpoints) (valid_endpoints seu sev n 0)

let valid_endpoints_add (seu sev: Seq.seq int) (n ec: nat) (vu vv: int)
  : Lemma (requires valid_endpoints seu sev n ec /\ ec < n /\
                    vu >= 0 /\ vu < n /\ vv >= 0 /\ vv < n /\
                    Seq.length seu == n /\ Seq.length sev == n)
          (ensures valid_endpoints (Seq.upd seu ec vu) (Seq.upd sev ec vv) n (ec + 1))
  = reveal_opaque (`%valid_endpoints) (valid_endpoints seu sev n ec);
    reveal_opaque (`%valid_endpoints) (valid_endpoints (Seq.upd seu ec vu) (Seq.upd sev ec vv) n (ec + 1))

let valid_endpoints_noop (seu sev: Seq.seq int) (n ec: nat)
  : Lemma (requires valid_endpoints seu sev n ec /\ ec > 0 /\ n > 0 /\
                    Seq.length seu == n /\ Seq.length sev == n)
          (ensures valid_endpoints
                     (Seq.upd seu 0 (Seq.index seu 0))
                     (Seq.upd sev 0 (Seq.index sev 0))
                     n ec)
  = reveal_opaque (`%valid_endpoints) (valid_endpoints seu sev n ec);
    reveal_opaque (`%valid_endpoints) (valid_endpoints
      (Seq.upd seu 0 (Seq.index seu 0))
      (Seq.upd sev 0 (Seq.index sev 0)) n ec)

let valid_endpoints_len (seu sev: Seq.seq int) (n ec: nat)
  : Lemma (requires valid_endpoints seu sev n ec)
          (ensures Seq.length seu == n /\ Seq.length sev == n /\ ec <= n)
  = reveal_opaque (`%valid_endpoints) (valid_endpoints seu sev n ec)

let valid_endpoints_conditional_write
  (seu sev: Seq.seq int) (n ec: nat) (vbu vbv: nat) (should_add: bool)
  : Lemma (requires valid_endpoints seu sev n ec /\ n > 0 /\
                    Seq.length seu == n /\ Seq.length sev == n /\
                    (should_add ==> (ec < n /\ vbu < n /\ vbv < n)))
          (ensures (let pos = if should_add then ec else 0 in
                    let vu = if should_add then vbu else Seq.index seu 0 in
                    let vv = if should_add then vbv else Seq.index sev 0 in
                    let new_ec = if should_add then ec + 1 else ec in
                    valid_endpoints (Seq.upd seu pos vu) (Seq.upd sev pos vv) n new_ec))
  = reveal_opaque (`%valid_endpoints) (valid_endpoints seu sev n ec);
    let pos = if should_add then ec else 0 in
    let vu = if should_add then vbu else Seq.index seu 0 in
    let vv = if should_add then vbv else Seq.index sev 0 in
    let new_ec = if should_add then ec + 1 else ec in
    reveal_opaque (`%valid_endpoints)
      (valid_endpoints (Seq.upd seu pos vu) (Seq.upd sev pos vv) n new_ec)

let lemma_index_in_bounds (u v n: nat)
  : Lemma (requires u < n /\ v < n /\ n > 0 /\ SZ.fits (n * n))
          (ensures u * n + v < n * n /\ SZ.fits (u * n) /\ SZ.fits (u * n + v))
  = ()

module ML = FStar.Math.Lemmas

let distrib_right (a b: nat)
  : Lemma (ensures (a + 1) * b == a * b + b)
  = ()

let round_cost_lemma (n: nat)
  : Lemma (requires n >= 2)
          (ensures n * n + 2 * n + 1 <= 3 * n * n)
  = ()

// After a round: accumulated cost ≤ n + vround*3*n² + n² + 2n + 1 ≤ n + (vround+1)*3*n²
let acc_round_bound (n vround: nat)
  : Lemma (requires n >= 2)
          (ensures n + vround * 3 * n * n + n * n + 2 * n + 1 <= n + (vround + 1) * 3 * n * n)
  = round_cost_lemma n;
    ML.distributivity_add_left vround 1 3;
    ML.distributivity_add_left (vround * 3) 3 n;
    ML.distributivity_add_left (vround * 3 * n) (3 * n) n

// Final bound: n + (n-1)*3*n² ≤ 4n³
let final_bound_lemma (n vround: nat)
  : Lemma (requires n >= 1 /\ vround <= n - 1)
          (ensures n + vround * 3 * n * n <= 4 * n * n * n)
  = if n >= 2 then begin
      ML.distributivity_add_left (vround * 3 * n) (3 * n) n;
      ML.distributivity_add_left (vround * 3) 3 n;
      ML.distributivity_add_left vround 1 3
    end

// ========== Ghost tick counter ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Complexity bound predicate ==========

// For Kruskal's algorithm with V vertices:
// - Outer loop runs (V-1) times
// - Each iteration: 
//   * V² comparisons to find minimum edge
//   * V operations for union-find (2 finds + 1 union)
// - Total: (V-1) × (V² + V) ≈ V³
// - We use a bound of 4V³ to account for overhead

let complexity_bounded_kruskal (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= 4 * n * n * n

// ========== Find with tick counting ==========

#push-options "--ifuel 1 --fuel 0"
fn find_complexity
  (#p: perm)
  (parent: A.array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (v: SZ.t) (n: SZ.t)
  (ctr: GR.ref nat)
  (#c: erased nat)
  requires A.pts_to parent #p sparent ** GR.pts_to ctr c ** pure (
    SZ.v v < SZ.v n /\ SZ.v n > 0 /\ valid_parents sparent (SZ.v n)
  )
  returns root: SZ.t
  ensures exists* (cf: nat).
    A.pts_to parent #p sparent ** GR.pts_to ctr cf ** pure (
      SZ.v root < SZ.v n /\
      cf >= reveal c /\
      cf - reveal c <= SZ.v n
    )
{
  valid_parents_length sparent (SZ.v n);
  let mut curr: SZ.t = v;
  let mut steps: SZ.t = 0sz;
  while (!steps <^ n)
  invariant exists* vcurr vsteps (vc: nat).
    R.pts_to curr vcurr ** R.pts_to steps vsteps **
    A.pts_to parent #p sparent **
    GR.pts_to ctr vc **
    pure (
      SZ.v vcurr < SZ.v n /\ SZ.v vsteps <= SZ.v n /\ 
      valid_parents sparent (SZ.v n) /\
      vc >= reveal c /\
      vc - reveal c <= SZ.v vsteps
    )
  decreases (SZ.v n - SZ.v !steps)
  {
    let vcurr = !curr;
    valid_parents_index sparent (SZ.v n) (SZ.v vcurr);
    let p = A.op_Array_Access parent vcurr;
    curr := p;
    let vsteps = !steps;
    
    tick ctr;
    
    steps := vsteps +^ 1sz;
  };
  !curr
}
#pop-options

// ========== Union with tick counting ==========

#push-options "--ifuel 1 --fuel 0"
fn do_union_complexity
  (parent: A.array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (root_u root_v: SZ.t) (n: SZ.t)
  (ctr: GR.ref nat)
  (#c: erased nat)
  requires A.pts_to parent sparent ** GR.pts_to ctr c ** pure (
    SZ.v root_u < SZ.v n /\ SZ.v root_v < SZ.v n /\ SZ.v n > 0 /\ 
    valid_parents sparent (SZ.v n)
  )
  returns _: unit
  ensures exists* sparent' (cf: nat). 
    A.pts_to parent sparent' ** GR.pts_to ctr cf ** pure (
      valid_parents sparent' (SZ.v n) /\
      cf >= reveal c /\
      cf - reveal c <= 1
    )
{
  valid_parents_length sparent (SZ.v n);
  valid_parents_seq_upd sparent (SZ.v n) (SZ.v root_u) root_v;
  A.op_Array_Assignment parent root_u root_v;
  tick ctr;
}
#pop-options

// ========== Kruskal's MST with Complexity Counting ==========

#push-options "--ifuel 1 --fuel 0"
fn kruskal_complexity
  (adj: A.array int)
  (#p: perm) (#sadj: Ghost.erased (Seq.seq int))
  (edge_u edge_v: A.array int)
  (#sedge_u #sedge_v: Ghost.erased (Seq.seq int))
  (edge_count: R.ref SZ.t)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires 
    A.pts_to adj #p sadj **
    A.pts_to edge_u sedge_u **
    A.pts_to edge_v sedge_v **
    R.pts_to edge_count 0sz **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sedge_u == SZ.v n /\
      Seq.length sedge_v == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _: unit
  ensures exists* vec sedge_u' sedge_v' (cf: nat).
    A.pts_to adj #p sadj **
    A.pts_to edge_u sedge_u' **
    A.pts_to edge_v sedge_v' **
    R.pts_to edge_count vec **
    GR.pts_to ctr cf **
    pure (
      valid_endpoints sedge_u' sedge_v' (SZ.v n) (SZ.v vec) /\
      complexity_bounded_kruskal cf (reveal c0) (SZ.v n)
    )
{
  // Initialize parent[i] = i
  let parent_v = V.alloc 0sz n;
  V.to_array_pts_to parent_v;
  let parent = V.vec_to_array parent_v;
  rewrite (A.pts_to (V.vec_to_array parent_v) (Seq.create (SZ.v n) 0sz))
       as (A.pts_to parent (Seq.create (SZ.v n) 0sz));
  
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi sparent (vc: nat).
    R.pts_to i vi **
    A.pts_to adj #p sadj **
    A.pts_to parent sparent **
    A.pts_to edge_u sedge_u **
    A.pts_to edge_v sedge_v **
    R.pts_to edge_count 0sz **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sparent == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sparent j) < SZ.v n) /\
      vc >= reveal c0 /\
      vc - reveal c0 <= SZ.v vi
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    A.op_Array_Assignment parent vi vi;
    tick ctr;
    i := vi +^ 1sz;
  };
  
  // Establish valid_parents from init loop invariant
  with sparent_init. assert (A.pts_to parent sparent_init);
  establish_valid_parents sparent_init (SZ.v n);
  // Establish valid_endpoints for empty edge set
  establish_valid_endpoints_empty sedge_u sedge_v (SZ.v n);
  
  // Process n-1 rounds
  let mut round: SZ.t = 0sz;
  let max_rounds = n -^ 1sz;
  
  while (!round <^ max_rounds)
  invariant exists* vround vec sparent seu sev (vc: nat).
    R.pts_to round vround **
    R.pts_to edge_count vec **
    A.pts_to adj #p sadj **
    A.pts_to parent sparent **
    A.pts_to edge_u seu **
    A.pts_to edge_v sev **
    GR.pts_to ctr vc **
    pure (
      SZ.v vround <= SZ.v n - 1 /\
      SZ.v vec <= SZ.v vround /\
      SZ.fits (SZ.v n * SZ.v n) /\
      valid_parents sparent (SZ.v n) /\
      valid_endpoints seu sev (SZ.v n) (SZ.v vec) /\
      vc >= reveal c0 /\
      // Each round does: n*n + 2*n + 1 operations (scan + 2 finds + union)
      // Per-round budget: 3*n*n (holds for n >= 2; loop doesn't run for n=1)
      vc - reveal c0 <= SZ.v n + SZ.v vround * 3 * SZ.v n * SZ.v n
    )
  decreases (SZ.v max_rounds - SZ.v !round)
  {
    let vround = !round;
    
    // Find minimum weight edge: scan V² entries
    let mut best_u: SZ.t = 0sz;
    let mut best_v: SZ.t = 0sz;
    let mut best_w: int = 0;
    
    let mut ui: SZ.t = 0sz;
    while (!ui <^ n)
    invariant exists* vui vbu vbv vbw sparent_s vec_s seu_s sev_s (vc: nat).
      R.pts_to round vround **
      R.pts_to ui vui **
      R.pts_to best_u vbu **
      R.pts_to best_v vbv **
      R.pts_to best_w vbw **
      R.pts_to edge_count vec_s **
      A.pts_to adj #p sadj **
      A.pts_to parent sparent_s **
      A.pts_to edge_u seu_s **
      A.pts_to edge_v sev_s **
      GR.pts_to ctr vc **
      pure (
        SZ.v vui <= SZ.v n /\
        SZ.v vbu < SZ.v n /\
        SZ.v vbv < SZ.v n /\
        SZ.fits (SZ.v n * SZ.v n) /\
        valid_parents sparent_s (SZ.v n) /\
        valid_endpoints seu_s sev_s (SZ.v n) (SZ.v vec_s) /\
        SZ.v vec_s <= SZ.v vround /\
        vc >= reveal c0 /\
        // Accumulated: previous + current scan
        vc - reveal c0 <= SZ.v n + SZ.v vround * 3 * SZ.v n * SZ.v n + SZ.v vui * SZ.v n
      )
    decreases (SZ.v n - SZ.v !ui)
    {
      let vui = !ui;
      let mut vi: SZ.t = 0sz;
      while (!vi <^ n)
      invariant exists* vvi vbu vbv vbw vec_i sparent_i seu_i sev_i (vc: nat).
        R.pts_to round vround **
        R.pts_to ui vui **
        R.pts_to vi vvi **
        R.pts_to best_u vbu **
        R.pts_to best_v vbv **
        R.pts_to best_w vbw **
        R.pts_to edge_count vec_i **
        A.pts_to adj #p sadj **
        A.pts_to parent sparent_i **
        A.pts_to edge_u seu_i **
        A.pts_to edge_v sev_i **
        GR.pts_to ctr vc **
        pure (
          SZ.v vvi <= SZ.v n /\
          SZ.v vui < SZ.v n /\
          SZ.v vbu < SZ.v n /\
          SZ.v vbv < SZ.v n /\
          SZ.fits (SZ.v n * SZ.v n) /\
          valid_parents sparent_i (SZ.v n) /\
          valid_endpoints seu_i sev_i (SZ.v n) (SZ.v vec_i) /\
          SZ.v vec_i <= SZ.v vround /\
          vc >= reveal c0 /\
          // Count each comparison
          vc - reveal c0 <= SZ.v n + SZ.v vround * 3 * SZ.v n * SZ.v n + SZ.v vui * SZ.v n + SZ.v vvi
        )
      decreases (SZ.v n - SZ.v !vi)
      {
        let vvi = !vi;
        lemma_index_in_bounds (SZ.v vui) (SZ.v vvi) (SZ.v n);
        let offset: SZ.t = SZ.mul vui n;
        let idx: SZ.t = SZ.add offset vvi;
        let w = A.op_Array_Access adj idx;
        let vbw = !best_w;
        let vbu_old = !best_u;
        let vbv_old = !best_v;
        
        tick ctr;
        
        let take_it: bool = (w > 0 && (vbw = 0 || w < vbw));
        best_u := (if take_it then vui else vbu_old);
        best_v := (if take_it then vvi else vbv_old);
        best_w := (if take_it then w else vbw);
        
        vi := vvi +^ 1sz;
      };
      with _ _ _ _ _ _ _ _ (vc_inner: nat). assert (GR.pts_to ctr vc_inner);
      // Inner loop exited with vvi <= n, so bound is vui*n + n >= vui*n + vvi
      // Distributive law: (vui+1)*n = vui*n + n
      distrib_right (SZ.v vui) (SZ.v n);
      assert (pure (
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 <= SZ.v n + SZ.v vround * 3 * SZ.v n * SZ.v n + (SZ.v vui + 1) * SZ.v n
      ));
      ui := vui +^ 1sz;
    };
    
    // Check components and add edge
    let vbu = !best_u;
    let vbv = !best_v;
    let vbw = !best_w;
    let vec = !edge_count;
    
    // Two find operations: each costs at most n ticks
    let root_u = find_complexity parent vbu n ctr;
    let root_v = find_complexity parent vbv n ctr;
    
    let should_add: bool = (vbw > 0 && root_u <> root_v && vec <^ n);
    
    // Write edge endpoints and prove valid_endpoints preservation
    with seu_cur. assert (A.pts_to edge_u seu_cur);
    with sev_cur. assert (A.pts_to edge_v sev_cur);
    valid_endpoints_len seu_cur sev_cur (SZ.v n) (SZ.v vec);
    let old_eu0 = A.op_Array_Access edge_u 0sz;
    let old_ev0 = A.op_Array_Access edge_v 0sz;
    let write_pos: SZ.t = (if should_add then vec else 0sz);
    let val_eu = (if should_add then SZ.v vbu else old_eu0);
    let val_ev = (if should_add then SZ.v vbv else old_ev0);
    valid_endpoints_conditional_write seu_cur sev_cur (SZ.v n) (SZ.v vec) (SZ.v vbu) (SZ.v vbv) should_add;
    A.op_Array_Assignment edge_u write_pos val_eu;
    A.op_Array_Assignment edge_v write_pos val_ev;
    
    edge_count := (if should_add then vec +^ 1sz else vec);
    
    // Union: costs at most 1 tick
    do_union_complexity parent root_u root_v n ctr;
    
    // Name all existentials from do_union_complexity
    with sparent_new (vc: nat). 
      assert (A.pts_to parent sparent_new ** GR.pts_to ctr vc);
    
    // Prove complexity bound is maintained
    // After scan (n²) + 2 finds (2n) + union (1): cost increment = n² + 2n + 1
    // Budget per round: 3n². Need n² + 2n + 1 ≤ 3n², i.e., 2n+1 ≤ 2n² (holds for n≥2)
    // We're in the loop so vround < n-1, hence n ≥ 2
    acc_round_bound (SZ.v n) (SZ.v vround);
    
    // Help SMT connect SZ.v (vround +^ 1sz) = SZ.v vround + 1
    let vround1 = vround +^ 1sz;
    assert (pure (SZ.v vround1 == SZ.v vround + 1));
    assert (pure (SZ.v vround1 <= SZ.v n - 1));
    assert (pure (valid_parents sparent_new (SZ.v n)));
    assert (pure (vc >= reveal c0));
    assert (pure (vc - reveal c0 <= SZ.v n + (SZ.v vround + 1) * 3 * SZ.v n * SZ.v n));
    
    round := vround1;
  };
  
  // Clean up
  with vr. assert (R.pts_to round vr);
  with sp. assert (A.pts_to parent sp);
  rewrite (A.pts_to parent sp) as (A.pts_to (V.vec_to_array parent_v) sp);
  V.to_vec_pts_to parent_v;
  V.free parent_v;
  
  // Final complexity bound: after (n-1) rounds:
  // ticks ≤ n + (n-1) * 3 * n * n = n + 3n³ - 3n² ≤ 4n³
  with vc_final. assert (GR.pts_to ctr vc_final);
  final_bound_lemma (SZ.v n) (SZ.v vr);
  assert (pure (complexity_bounded_kruskal vc_final (reveal c0) (SZ.v n)));
}
#pop-options
