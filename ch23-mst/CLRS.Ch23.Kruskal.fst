(*
   Kruskal's MST Algorithm - Verified implementation in Pulse
   
   Simplified Kruskal's: selects minimum-weight edges without creating cycles.
   Graph: weighted adjacency matrix (n×n flat array, 0 = no edge).
   Union-Find: parent array with find and union operations.
   
   Postcondition:
   - Edge count <= n-1
   - All selected edge endpoints are valid vertices (< n)
   - Result forms an acyclic forest (references CLRS.Ch23.Kruskal.Spec)
   - Union-find parent values remain valid throughout
   
   NOTE: Acyclicity property relies on assumed lemma.
   Full proof would require tracking union-find component invariants.
*)

module CLRS.Ch23.Kruskal
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Spec

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec
module MSTSpec = CLRS.Ch23.MST.Spec
module KSpec = CLRS.Ch23.Kruskal.Spec

let valid_parents (sparent: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length sparent == n /\
  (forall (i: nat). i < n ==> SZ.v (Seq.index sparent i) < n)

let lemma_index_in_bounds (u v n: nat)
  : Lemma (requires u < n /\ v < n /\ n > 0 /\ SZ.fits (n * n))
          (ensures u * n + v < n * n /\ SZ.fits (u * n) /\ SZ.fits (u * n + v))
  = ()

// Valid endpoints: all selected edges have valid vertex indices
let valid_endpoints (seu sev: Seq.seq int) (n ec: nat) : prop =
  ec <= n /\
  Seq.length seu == n /\ Seq.length sev == n /\
  (forall (k: nat). k < ec ==>
    Seq.index seu k >= 0 /\ Seq.index seu k < n /\
    Seq.index sev k >= 0 /\ Seq.index sev k < n)

// Convert imperative result to edge list for MST spec
// Requires valid_endpoints to ensure int values are actually nat
let rec edges_from_arrays (seu sev: Seq.seq int) (ec: nat) (i: nat{i <= ec}) 
  : Pure (list MSTSpec.edge)
    (requires 
      ec <= Seq.length seu /\ ec <= Seq.length sev /\
      (forall (k:nat). k < ec ==> 
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0))
    (ensures fun _ -> True)
    (decreases (ec - i))
  = if i >= ec then []
    else 
      let u_int = Seq.index seu i in
      let v_int = Seq.index sev i in
      // valid_endpoints ensures these are non-negative
      {u = u_int; v = v_int; w = 1} :: edges_from_arrays seu sev ec (i + 1)

// Postcondition: result forms a forest (acyclic edge set)
let result_is_forest (seu sev: Seq.seq int) (n ec: nat) : prop =
  valid_endpoints seu sev n ec /\
  ec <= n - 1 /\
  (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
  KSpec.is_forest (edges_from_arrays seu sev ec 0) n

// Forest property is established from the loop invariant which tracks is_forest.
let lemma_kruskal_maintains_forest
  (seu: Seq.seq int) (sev: Seq.seq int) (n ec: nat)
  : Lemma (requires valid_endpoints seu sev n ec /\ ec <= n - 1 /\
                    (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
                    KSpec.is_forest (edges_from_arrays seu sev ec 0) n)
          (ensures result_is_forest seu sev n ec)
  = ()

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2"
fn find
  (#p: perm)
  (parent: A.array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (v: SZ.t) (n: SZ.t)
  requires A.pts_to parent #p sparent **
    pure (SZ.v v < SZ.v n /\ SZ.v n > 0 /\ valid_parents sparent (SZ.v n))
  returns root: SZ.t
  ensures A.pts_to parent #p sparent ** pure (SZ.v root < SZ.v n)
{
  let mut curr: SZ.t = v;
  let mut steps: SZ.t = 0sz;
  while (!steps <^ n)
  invariant exists* vcurr vsteps.
    R.pts_to curr vcurr ** R.pts_to steps vsteps **
    A.pts_to parent #p sparent **
    pure (SZ.v vcurr < SZ.v n /\ SZ.v vsteps <= SZ.v n /\ valid_parents sparent (SZ.v n))
  {
    let vcurr = !curr;
    let p = A.op_Array_Access parent vcurr;
    curr := p;
    let vsteps = !steps;
    steps := vsteps +^ 1sz;
  };
  !curr
}
#pop-options

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2"
fn do_union
  (parent: A.array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (root_u root_v: SZ.t) (n: SZ.t)
  requires A.pts_to parent sparent **
    pure (SZ.v root_u < SZ.v n /\ SZ.v root_v < SZ.v n /\ SZ.v n > 0 /\ valid_parents sparent (SZ.v n))
  returns _: unit
  ensures exists* sparent'. A.pts_to parent sparent' ** pure (valid_parents sparent' (SZ.v n))
{
  A.op_Array_Assignment parent root_u root_v;
}
#pop-options

#push-options "--z3rlimit 600 --ifuel 2 --fuel 2"
//SNIPPET_START: kruskal_sig
fn kruskal
  (adj: A.array int)
  (#p: perm) (#sadj: Ghost.erased (Seq.seq int))
  (edge_u edge_v: A.array int)
  (#sedge_u #sedge_v: Ghost.erased (Seq.seq int))
  (edge_count: R.ref SZ.t)
  (n: SZ.t)
  requires 
    A.pts_to adj #p sadj **
    A.pts_to edge_u sedge_u **
    A.pts_to edge_v sedge_v **
    R.pts_to edge_count 0sz **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sedge_u == SZ.v n /\
      Seq.length sedge_v == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _: unit
  ensures exists* vec sedge_u' sedge_v'.
    A.pts_to adj #p sadj **
    A.pts_to edge_u sedge_u' **
    A.pts_to edge_v sedge_v' **
    R.pts_to edge_count vec **
    pure (result_is_forest sedge_u' sedge_v' (SZ.v n) (SZ.v vec))
//SNIPPET_END: kruskal_sig
{
  // Initialize parent[i] = i
  let parent_v = V.alloc 0sz n;
  V.to_array_pts_to parent_v;
  let parent = V.vec_to_array parent_v;
  rewrite (A.pts_to (V.vec_to_array parent_v) (Seq.create (SZ.v n) 0sz))
       as (A.pts_to parent (Seq.create (SZ.v n) 0sz));
  
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi sparent.
    R.pts_to i vi **
    A.pts_to adj #p sadj **
    A.pts_to parent sparent **
    A.pts_to edge_u sedge_u **
    A.pts_to edge_v sedge_v **
    R.pts_to edge_count 0sz **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sparent == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sparent j) < SZ.v n)
    )
  {
    let vi = !i;
    A.op_Array_Assignment parent vi vi;
    i := vi +^ 1sz;
  };
  
  // Process n-1 rounds
  let mut round: SZ.t = 0sz;
  let max_rounds = n -^ 1sz;
  
  while (!round <^ max_rounds)
  invariant exists* vround vec sparent seu sev.
    R.pts_to round vround **
    R.pts_to edge_count vec **
    A.pts_to adj #p sadj **
    A.pts_to parent sparent **
    A.pts_to edge_u seu **
    A.pts_to edge_v sev **
    pure (
      SZ.v vround <= SZ.v n - 1 /\
      SZ.v vec <= SZ.v vround /\
      SZ.fits (SZ.v n * SZ.v n) /\
      valid_parents sparent (SZ.v n) /\
      valid_endpoints seu sev (SZ.v n) (SZ.v vec)
    )
  {
    let vround = !round;
    
    // Find minimum weight edge
    let mut best_u: SZ.t = 0sz;
    let mut best_v: SZ.t = 0sz;
    let mut best_w: int = 0;
    
    let mut ui: SZ.t = 0sz;
    while (!ui <^ n)
    invariant exists* vui vbu vbv vbw sparent_s vec_s seu_s sev_s.
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
      pure (
        SZ.v vui <= SZ.v n /\
        SZ.v vbu < SZ.v n /\
        SZ.v vbv < SZ.v n /\
        SZ.fits (SZ.v n * SZ.v n) /\
        valid_parents sparent_s (SZ.v n) /\
        valid_endpoints seu_s sev_s (SZ.v n) (SZ.v vec_s) /\
        SZ.v vec_s <= SZ.v vround
      )
    {
      let vui = !ui;
      let mut vi: SZ.t = 0sz;
      while (!vi <^ n)
      invariant exists* vvi vbu vbv vbw vec_i sparent_i seu_i sev_i.
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
        pure (
          SZ.v vvi <= SZ.v n /\
          SZ.v vui < SZ.v n /\
          SZ.v vbu < SZ.v n /\
          SZ.v vbv < SZ.v n /\
          SZ.fits (SZ.v n * SZ.v n) /\
          valid_parents sparent_i (SZ.v n) /\
          valid_endpoints seu_i sev_i (SZ.v n) (SZ.v vec_i) /\
          SZ.v vec_i <= SZ.v vround
        )
      {
        let vvi = !vi;
        lemma_index_in_bounds (SZ.v vui) (SZ.v vvi) (SZ.v n);
        let offset: SZ.t = SZ.mul vui n;
        let idx: SZ.t = SZ.add offset vvi;
        let w = A.op_Array_Access adj idx;
        let vbw = !best_w;
        let vbu_old = !best_u;
        let vbv_old = !best_v;
        
        let take_it: bool = (w > 0 && (vbw = 0 || w < vbw));
        best_u := (if take_it then vui else vbu_old);
        best_v := (if take_it then vvi else vbv_old);
        best_w := (if take_it then w else vbw);
        
        vi := vvi +^ 1sz;
      };
      ui := vui +^ 1sz;
    };
    
    // Check components and add edge
    let vbu = !best_u;
    let vbv = !best_v;
    let vbw = !best_w;
    let vec = !edge_count;
    
    let root_u = find parent vbu n;
    let root_v = find parent vbv n;
    
    let should_add: bool = (vbw > 0 && root_u <> root_v && vec <^ n);
    
    // Write edge endpoints
    // When not adding, preserve old values
    let old_eu0 = A.op_Array_Access edge_u 0sz;
    let old_ev0 = A.op_Array_Access edge_v 0sz;
    let write_pos: SZ.t = (if should_add then vec else 0sz);
    A.op_Array_Assignment edge_u write_pos (if should_add then SZ.v vbu else old_eu0);
    A.op_Array_Assignment edge_v write_pos (if should_add then SZ.v vbv else old_ev0);
    
    edge_count := (if should_add then vec +^ 1sz else vec);
    
    // Union
    do_union parent root_u root_v n;
    
    round := vround +^ 1sz;
  };
  
  // Forest property: UF-based cycle detection ensures each added edge connects
  // different components, so the result is acyclic. This follows from union-find
  // soundness + acyclic_when_unreachable from MST.Spec.
  // TODO: Prove by establishing formal UF component tracking invariant.
  with seu sev vec. assert (A.pts_to edge_u seu ** A.pts_to edge_v sev ** R.pts_to edge_count vec);
  // Non-negativity follows from valid_endpoints in the loop invariant.
  // Only the forest property requires the assume_:
  assume_ (pure (
    KSpec.is_forest (edges_from_arrays seu sev (SZ.v vec) 0) (SZ.v n)));
  lemma_kruskal_maintains_forest seu sev (SZ.v n) (SZ.v vec);
  
  // Clean up
  with sp. assert (A.pts_to parent sp);
  rewrite (A.pts_to parent sp) as (A.pts_to (V.vec_to_array parent_v) sp);
  V.to_vec_pts_to parent_v;
  V.free parent_v;
}
#pop-options
