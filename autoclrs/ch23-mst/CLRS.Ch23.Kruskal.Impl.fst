(*
   Kruskal's MST Algorithm - Verified implementation in Pulse
   
   Simplified Kruskal's: each round scans the full V×V adjacency matrix for the
   minimum-weight cross-component edge (i.e., the lightest edge whose endpoints
   are in different union-find components), then adds it to the forest.
   Graph: weighted adjacency matrix (n×n flat array, 0 = no edge).
   Union-Find: parent array with find and union operations.
   
   Postcondition:
   - Edge count <= n-1
   - All selected edge endpoints are valid vertices (< n)
   - Result forms an acyclic forest (proven via union-find invariant)
   - Union-find parent values remain valid throughout
   
   Key inner-scan invariant: if best_w > 0, then find(best_u) ≠ find(best_v),
   ensuring the selected edge always connects distinct components.
   
   Proof: The forest property is maintained by tracking a union-find invariant
   (uf_inv) that relates the parent array to edge connectivity. When adding an
   edge, uf_inv_union proves the invariant is maintained, and
   acyclic_snoc_unreachable proves acyclicity is preserved (since the new edge
   connects previously unreachable vertices).
*)

module CLRS.Ch23.Kruskal.Impl
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
module UF = CLRS.Ch23.Kruskal.UF
module Helpers = CLRS.Ch23.Kruskal.Helpers
module Bridge = CLRS.Ch23.Kruskal.Bridge

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

// valid_endpoints implies all edges have valid vertices (< n)
let rec valid_endpoints_implies_all_edges_valid
  (seu sev: Seq.seq int) (n ec: nat) (i: nat{i <= ec})
  : Lemma (requires valid_endpoints seu sev n ec)
          (ensures UF.all_edges_valid (edges_from_arrays seu sev ec i) n)
          (decreases (ec - i))
  = if i >= ec then ()
    else valid_endpoints_implies_all_edges_valid seu sev n ec (i + 1)

// Extending valid_endpoints by one: if valid at ec and the new entry is valid, then valid at ec+1
let valid_endpoints_extend
  (seu sev seu' sev': Seq.seq int) (n ec: nat) (vbu vbv: nat)
  : Lemma
    (requires
      valid_endpoints seu sev n ec /\
      ec + 1 <= n /\
      Seq.length seu' == n /\ Seq.length sev' == n /\
      (forall (k:nat). k < ec ==> Seq.index seu' k = Seq.index seu k /\
                                   Seq.index sev' k = Seq.index sev k) /\
      Seq.index seu' ec == vbu /\ Seq.index sev' ec == vbv /\
      vbu < n /\ vbv < n)
    (ensures valid_endpoints seu' sev' n (ec + 1))
  = // For k < ec: old valid_endpoints + array agreement
    assert (forall (k:nat). k < ec ==>
      Seq.index seu' k >= 0 /\ Seq.index seu' k < n /\
      Seq.index sev' k >= 0 /\ Seq.index sev' k < n);
    // For k = ec: explicit
    assert (Seq.index seu' ec >= 0 /\ Seq.index seu' ec < n);
    assert (Seq.index sev' ec >= 0 /\ Seq.index sev' ec < n)

// Extensionality: edges_from_arrays depends only on values in [i, ec)
let rec edges_from_arrays_ext (seu1 sev1 seu2 sev2: Seq.seq int) (ec: nat) (i: nat{i <= ec})
  : Lemma
    (requires
      ec <= Seq.length seu1 /\ ec <= Seq.length sev1 /\
      ec <= Seq.length seu2 /\ ec <= Seq.length sev2 /\
      (forall (k:nat). k < ec ==> Seq.index seu1 k >= 0 /\ Seq.index sev1 k >= 0) /\
      (forall (k:nat). k < ec ==> Seq.index seu2 k >= 0 /\ Seq.index sev2 k >= 0) /\
      (forall (k:nat). i <= k /\ k < ec ==>
        Seq.index seu1 k == Seq.index seu2 k /\ Seq.index sev1 k == Seq.index sev2 k))
    (ensures edges_from_arrays seu1 sev1 ec i == edges_from_arrays seu2 sev2 ec i)
    (decreases (ec - i))
  = if i >= ec then ()
    else edges_from_arrays_ext seu1 sev1 seu2 sev2 ec (i + 1)

// Extension: adding one element at index ec appends to the edge list
let rec edges_from_arrays_extend (seu sev: Seq.seq int) (ec: nat) (i: nat{i <= ec}) (eu ev: nat)
  : Lemma
    (requires
      ec < Seq.length seu /\ ec < Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
      Seq.index seu ec == eu /\ Seq.index sev ec == ev)
    (ensures edges_from_arrays seu sev (ec + 1) i ==
             edges_from_arrays seu sev ec i @ [{u = eu; v = ev; w = 1}])
    (decreases (ec - i))
  = if i >= ec then ()
    else edges_from_arrays_extend seu sev ec (i + 1) eu ev

// Opaque bundled invariant — prevents quantifier pollution in Pulse VCs.
// Bundles valid_parents, valid_endpoints, uf_inv, and is_forest behind an
// opaque wall so that ~8 forall quantifiers don't leak into every split query.
[@@"opaque_to_smt"]
let kruskal_inv (sparent: Seq.seq SZ.t) (seu sev: Seq.seq int) (n ec: nat) : prop =
  valid_parents sparent n /\
  valid_endpoints seu sev n ec /\
  UF.uf_inv sparent (edges_from_arrays seu sev ec 0) n ec /\
  KSpec.is_forest (edges_from_arrays seu sev ec 0) n

let kruskal_inv_intro (sparent: Seq.seq SZ.t) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires
      valid_parents sparent n /\
      valid_endpoints seu sev n ec /\
      UF.uf_inv sparent (edges_from_arrays seu sev ec 0) n ec /\
      KSpec.is_forest (edges_from_arrays seu sev ec 0) n)
    (ensures kruskal_inv sparent seu sev n ec)
  = reveal_opaque (`%kruskal_inv) (kruskal_inv sparent seu sev n ec)

let kruskal_inv_elim (sparent: Seq.seq SZ.t) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires kruskal_inv sparent seu sev n ec)
    (ensures
      valid_parents sparent n /\
      valid_endpoints seu sev n ec /\
      UF.uf_inv sparent (edges_from_arrays seu sev ec 0) n ec /\
      KSpec.is_forest (edges_from_arrays seu sev ec 0) n)
  = reveal_opaque (`%kruskal_inv) (kruskal_inv sparent seu sev n ec)

let kruskal_inv_valid_parents (sparent: Seq.seq SZ.t) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma (requires kruskal_inv sparent seu sev n ec)
          (ensures valid_parents sparent n /\ Seq.length sparent == n /\
                   Seq.length seu == n /\ Seq.length sev == n /\ ec <= n /\ ec < n)
  = reveal_opaque (`%kruskal_inv) (kruskal_inv sparent seu sev n ec)

// Extract non-negativity of old array entries (needed to prove new array validity after writes)
let kruskal_inv_endpoints (sparent: Seq.seq SZ.t) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma (requires kruskal_inv sparent seu sev n ec)
          (ensures valid_endpoints seu sev n ec)
  = reveal_opaque (`%kruskal_inv) (kruskal_inv sparent seu sev n ec)

let kruskal_inv_init (sparent: Seq.seq SZ.t) (seu sev: Seq.seq int) (n: nat)
  : Lemma (requires UF.identity_parent n sparent /\ n > 0 /\
                    Seq.length seu == n /\ Seq.length sev == n)
          (ensures kruskal_inv sparent seu sev n 0)
  = UF.uf_inv_init sparent n;
    reveal_opaque (`%kruskal_inv) (kruskal_inv sparent seu sev n 0)

// Track that each selected edge has a positive entry in the adjacency matrix.
// This connects imperative edge arrays to the graph structure (needed for subset_edges).
[@@"opaque_to_smt"]
let edges_adj_pos (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat) : prop =
  Seq.length sadj == n * n /\ n > 0 /\
  ec <= Seq.length seu /\ ec <= Seq.length sev /\
  (forall (k:nat). k < ec ==> 
    Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
    Seq.index seu k < n /\ Seq.index sev k < n /\
    Seq.index sadj (Seq.index seu k * n + Seq.index sev k) > 0)

let edges_adj_pos_init (sadj: Seq.seq int) (seu sev: Seq.seq int) (n: nat)
  : Lemma (requires Seq.length sadj == n * n /\ n > 0 /\
                    Seq.length seu == n /\ Seq.length sev == n)
          (ensures edges_adj_pos sadj seu sev n 0)
  = reveal_opaque (`%edges_adj_pos) (edges_adj_pos sadj seu sev n 0)

let edges_adj_pos_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma (requires edges_adj_pos sadj seu sev n ec)
          (ensures Seq.length sadj == n * n /\ n > 0 /\
                   ec <= Seq.length seu /\ ec <= Seq.length sev /\
                   (forall (k:nat). k < ec ==> 
                     Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
                     Seq.index seu k < n /\ Seq.index sev k < n /\
                     Seq.index sadj (Seq.index seu k * n + Seq.index sev k) > 0))
  = reveal_opaque (`%edges_adj_pos) (edges_adj_pos sadj seu sev n ec)

let edges_adj_pos_step
  (sadj: Seq.seq int) (seu sev seu' sev': Seq.seq int) (n ec ec': nat)
  (vbu vbv: nat) (should_add: bool)
  : Lemma
    (requires
      edges_adj_pos sadj seu sev n ec /\
      Seq.length sadj == n * n /\ n > 0 /\
      vbu < n /\ vbv < n /\
      ec' == (if should_add then ec + 1 else ec) /\
      Seq.length seu' == Seq.length seu /\ Seq.length sev' == Seq.length sev /\
      ec < Seq.length seu /\ ec < Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu' k = Seq.index seu k /\
                                   Seq.index sev' k = Seq.index sev k) /\
      (should_add ==> Seq.index seu' ec == vbu /\ Seq.index sev' ec == vbv /\
                       Seq.index sadj (vbu * n + vbv) > 0))
    (ensures edges_adj_pos sadj seu' sev' n ec')
  = reveal_opaque (`%edges_adj_pos) (edges_adj_pos sadj seu sev n ec);
    reveal_opaque (`%edges_adj_pos) (edges_adj_pos sadj seu' sev' n ec')

// Strengthened postcondition: forest + edges come from adjacency matrix
let result_is_forest_adj (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat) : prop =
  result_is_forest seu sev n ec /\
  edges_adj_pos sadj seu sev n ec

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2"
fn find
  (#p: perm)
  (parent: A.array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (v: SZ.t) (n: SZ.t)
  requires A.pts_to parent #p sparent **
    pure (SZ.v v < SZ.v n /\ SZ.v n > 0 /\ valid_parents sparent (SZ.v n))
  returns root: SZ.t
  ensures A.pts_to parent #p sparent **
    pure (SZ.v root < SZ.v n /\
          SZ.v root = UF.find_pure sparent (SZ.v v) (SZ.v n) (SZ.v n))
{
  let mut curr: SZ.t = v;
  let mut steps: SZ.t = 0sz;
  while (!steps <^ n)
  invariant exists* vcurr vsteps.
    R.pts_to curr vcurr ** R.pts_to steps vsteps **
    A.pts_to parent #p sparent **
    pure (SZ.v vcurr < SZ.v n /\ SZ.v vsteps <= SZ.v n /\ valid_parents sparent (SZ.v n) /\
          UF.find_pure sparent (SZ.v vcurr) (SZ.v n - SZ.v vsteps) (SZ.v n) =
          UF.find_pure sparent (SZ.v v) (SZ.v n) (SZ.v n))
  decreases (SZ.v n - SZ.v !steps)
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

// Postcondition predicate for do_union: exposes what happened to parent array
let do_union_post (sparent sparent': Seq.seq SZ.t) (root_u root_v n: nat) : prop =
  valid_parents sparent' n /\
  Seq.length sparent == n /\
  Seq.length sparent' == n /\
  (root_u < n ==> SZ.v (Seq.index sparent' root_u) == root_v) /\
  (forall (i: nat). (i < n /\ i <> root_u) ==>
    Seq.index sparent' i == Seq.index sparent i)

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2"
fn do_union
  (parent: A.array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (root_u root_v: SZ.t) (n: SZ.t)
  requires A.pts_to parent sparent **
    pure (SZ.v root_u < SZ.v n /\ SZ.v root_v < SZ.v n /\ SZ.v n > 0 /\ valid_parents sparent (SZ.v n))
  returns _: unit
  ensures exists* sparent'. A.pts_to parent sparent' **
    pure (do_union_post sparent sparent' (SZ.v root_u) (SZ.v root_v) (SZ.v n))
{
  A.op_Array_Assignment parent root_u root_v;
}
#pop-options

// Lemma for when we add an edge: proves uf_inv, is_forest, valid_endpoints for new state.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 2 --split_queries always"
let kruskal_add_edge_proof
    (sparent sparent': Seq.seq SZ.t)
    (seu sev seu' sev': Seq.seq int)
    (n ec: nat)
    (vbu vbv: nat)
    (root_u root_v: nat)
  : Lemma
    (requires
      valid_endpoints seu sev n ec /\
      UF.uf_inv sparent (edges_from_arrays seu sev ec 0) n ec /\
      KSpec.is_forest (edges_from_arrays seu sev ec 0) n /\
      vbu < n /\ vbv < n /\
      root_u == UF.find_pure sparent vbu n n /\
      root_v == UF.find_pure sparent vbv n n /\
      root_u <> root_v /\
      do_union_post sparent sparent' root_u root_v n /\
      ec + 1 < n /\
      Seq.length seu' == n /\ Seq.length sev' == n /\
      (forall (k:nat). k < ec ==> Seq.index seu' k = Seq.index seu k /\
                                   Seq.index sev' k = Seq.index sev k) /\
      Seq.index seu' ec == vbu /\ Seq.index sev' ec == vbv /\
      (forall (k:nat). k < ec + 1 ==> Seq.index seu' k >= 0 /\ Seq.index sev' k >= 0))
    (ensures
      UF.uf_inv sparent' (edges_from_arrays seu' sev' (ec + 1) 0) n (ec + 1) /\
      KSpec.is_forest (edges_from_arrays seu' sev' (ec + 1) 0) n /\
      valid_endpoints seu' sev' n (ec + 1))
  = let old_edges = edges_from_arrays seu sev ec 0 in
    let new_edge : MSTSpec.edge = {u = vbu; v = vbv; w = 1} in
    edges_from_arrays_ext seu sev seu' sev' ec 0;
    edges_from_arrays_extend seu' sev' ec 0 vbu vbv;
    UF.uf_inv_unreachable sparent old_edges n ec vbu vbv;
    UF.not_mem_when_unreachable new_edge old_edges;
    MSTSpec.acyclic_when_unreachable n old_edges new_edge;
    UF.acyclic_cons_to_append n new_edge old_edges;
    valid_endpoints_implies_all_edges_valid seu sev n ec 0;
    UF.find_pure_bounded sparent vbu n n;
    UF.find_pure_bounded sparent vbv n n;
    UF.uf_inv_union sparent sparent' old_edges n ec vbu vbv root_u root_v new_edge;
    UF.uf_inv_cons_to_append sparent' new_edge old_edges n (ec + 1);
    valid_endpoints_extend seu sev seu' sev' n ec vbu vbv
#pop-options

// Lemma for when we don't add an edge: parent is effectively unchanged.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
let kruskal_noop_proof
    (sparent sparent': Seq.seq SZ.t)
    (seu sev: Seq.seq int)
    (n ec: nat)
    (vbu: nat)
    (root_u root_v: nat)
  : Lemma
    (requires
      valid_endpoints seu sev n ec /\
      UF.uf_inv sparent (edges_from_arrays seu sev ec 0) n ec /\
      KSpec.is_forest (edges_from_arrays seu sev ec 0) n /\
      vbu < n /\
      root_u == UF.find_pure sparent vbu n n /\
      root_u == root_v /\
      do_union_post sparent sparent' root_u root_v n /\
      Seq.length sparent == n)
    (ensures
      UF.uf_inv sparent' (edges_from_arrays seu sev ec 0) n ec /\
      KSpec.is_forest (edges_from_arrays seu sev ec 0) n /\
      valid_endpoints seu sev n ec /\
      valid_parents sparent' n)
  = UF.find_pure_bounded sparent vbu n n;
    // root_u is a fixed point: sparent[root_u] = root_u (from uf_inv conjunct 4)
    assert (SZ.v (Seq.index sparent root_u) == root_u);
    // do_union sets sparent'[root_u] = root_v = root_u, all others unchanged
    assert (forall (i:nat). i < n ==> Seq.index sparent' i == Seq.index sparent i);
    UF.uf_inv_eq sparent sparent' (edges_from_arrays seu sev ec 0) n ec
#pop-options

// Unified step lemma — dispatches to add_edge or noop proof.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 2 --split_queries always"
let kruskal_step_maintains_inv
  (sparent sparent': Seq.seq SZ.t)
  (seu sev seu' sev': Seq.seq int)
  (n ec ec': nat)
  (vbu vbv: nat)
  (root_u root_v: nat)
  (should_add: bool)
  : Lemma
    (requires
      kruskal_inv sparent seu sev n ec /\
      Seq.length seu == n /\ Seq.length sev == n /\
      vbu < n /\ vbv < n /\
      root_u == UF.find_pure sparent vbu n n /\
      root_v == UF.find_pure sparent vbv n n /\
      (should_add ==> root_u <> root_v) /\
      (~should_add ==> root_u = root_v) /\
      do_union_post sparent sparent' root_u root_v n /\
      ec + 1 < n /\
      ec' == (if should_add then ec + 1 else ec) /\
      Seq.length seu' == n /\ Seq.length sev' == n /\
      (forall (k:nat). k < ec ==> Seq.index seu' k = Seq.index seu k /\
                                   Seq.index sev' k = Seq.index sev k) /\
      (should_add ==> Seq.index seu' ec == vbu /\ Seq.index sev' ec == vbv) /\
      ec' <= Seq.length seu' /\ ec' <= Seq.length sev' /\
      (forall (k:nat). k < ec' ==> Seq.index seu' k >= 0 /\ Seq.index sev' k >= 0))
    (ensures
      kruskal_inv sparent' seu' sev' n ec')
  = kruskal_inv_elim sparent seu sev n ec;
    if should_add then
      kruskal_add_edge_proof sparent sparent' seu sev seu' sev' n ec vbu vbv root_u root_v
    else begin
      edges_from_arrays_ext seu sev seu' sev' ec 0;
      UF.find_pure_bounded sparent vbu n n;
      kruskal_noop_proof sparent sparent' seu sev n ec vbu root_u root_v
    end;
    kruskal_inv_intro sparent' seu' sev' n ec'
#pop-options

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2 --split_queries always"
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
    pure (result_is_forest_adj sadj sedge_u' sedge_v' (SZ.v n) (SZ.v vec))
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
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sparent j) = j)
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    A.op_Array_Assignment parent vi vi;
    i := vi +^ 1sz;
  };
  
  // After init: establish opaque kruskal_inv (no quantifiers leak into main loop)
  with sp_init. assert (A.pts_to parent sp_init);
  with seu_init. assert (A.pts_to edge_u seu_init);
  with sev_init. assert (A.pts_to edge_v sev_init);
  kruskal_inv_init sp_init seu_init sev_init (SZ.v n);
  edges_adj_pos_init sadj seu_init sev_init (SZ.v n);
  
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
      kruskal_inv sparent seu sev (SZ.v n) (SZ.v vec) /\
      edges_adj_pos sadj seu sev (SZ.v n) (SZ.v vec)
    )
  decreases (SZ.v max_rounds - SZ.v !round)
  {
    let vround = !round;
    
    // Bind ghost variables BEFORE inner scan (find calls need parent + valid_parents)
    with sparent_cur. assert (A.pts_to parent sparent_cur);
    with seu_cur. assert (A.pts_to edge_u seu_cur);
    with sev_cur. assert (A.pts_to edge_v sev_cur);
    with vec_cur. assert (R.pts_to edge_count vec_cur);
    
    // Extract valid_parents before scan (find needs it inside inner loop)
    kruskal_inv_valid_parents sparent_cur seu_cur sev_cur (SZ.v n) (SZ.v vec_cur);
    kruskal_inv_endpoints sparent_cur seu_cur sev_cur (SZ.v n) (SZ.v vec_cur);
    
    // Find minimum weight cross-component edge
    let mut best_u: SZ.t = 0sz;
    let mut best_v: SZ.t = 0sz;
    let mut best_w: int = 0;
    
    let mut ui: SZ.t = 0sz;
    while (!ui <^ n)
    invariant exists* vui vbu vbv vbw.
      R.pts_to ui vui **
      R.pts_to best_u vbu **
      R.pts_to best_v vbv **
      R.pts_to best_w vbw **
      A.pts_to adj #p sadj **
      A.pts_to parent sparent_cur **
      pure (
        SZ.v vui <= SZ.v n /\
        SZ.v vbu < SZ.v n /\
        SZ.v vbv < SZ.v n /\
        SZ.fits (SZ.v n * SZ.v n) /\
        SZ.v n > 0 /\
        Seq.length sadj == SZ.v n * SZ.v n /\
        vbw >= 0 /\
        valid_parents sparent_cur (SZ.v n) /\
        (vbw = 0 ==> SZ.v vbu == SZ.v vbv) /\
        (vbw > 0 ==> UF.find_pure sparent_cur (SZ.v vbu) (SZ.v n) (SZ.v n) <>
                      UF.find_pure sparent_cur (SZ.v vbv) (SZ.v n) (SZ.v n)) /\
        (vbw > 0 ==> Seq.index sadj (SZ.v vbu * SZ.v n + SZ.v vbv) = vbw)
      )
    decreases (SZ.v n - SZ.v !ui)
    {
      let vui = !ui;
      let mut vi: SZ.t = 0sz;
      while (!vi <^ n)
      invariant exists* vvi vbu vbv vbw.
        R.pts_to ui vui **
        R.pts_to vi vvi **
        R.pts_to best_u vbu **
        R.pts_to best_v vbv **
        R.pts_to best_w vbw **
        A.pts_to adj #p sadj **
        A.pts_to parent sparent_cur **
        pure (
          SZ.v vvi <= SZ.v n /\
          SZ.v vui < SZ.v n /\
          SZ.v vbu < SZ.v n /\
          SZ.v vbv < SZ.v n /\
          SZ.fits (SZ.v n * SZ.v n) /\
          SZ.v n > 0 /\
          Seq.length sadj == SZ.v n * SZ.v n /\
          vbw >= 0 /\
          valid_parents sparent_cur (SZ.v n) /\
          (vbw = 0 ==> SZ.v vbu == SZ.v vbv) /\
          (vbw > 0 ==> UF.find_pure sparent_cur (SZ.v vbu) (SZ.v n) (SZ.v n) <>
                        UF.find_pure sparent_cur (SZ.v vbv) (SZ.v n) (SZ.v n)) /\
          (vbw > 0 ==> Seq.index sadj (SZ.v vbu * SZ.v n + SZ.v vbv) = vbw)
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
        
        // Component check: only consider edges between different components
        let root_ui = find parent vui n;
        let root_vi = find parent vvi n;
        let diff_comp: bool = (root_ui <> root_vi);
        
        let take_it: bool = (w > 0 && diff_comp && (vbw = 0 || w < vbw));
        best_u := (if take_it then vui else vbu_old);
        best_v := (if take_it then vvi else vbv_old);
        best_w := (if take_it then w else vbw);
        
        vi := vvi +^ 1sz;
      };
      ui := vui +^ 1sz;
    };
    
    // After scan: edge_u, edge_v, edge_count were framed (unchanged)
    // parent was in inner invariant and comes back as sparent_cur
    
    // Check components and add edge
    let vbu = !best_u;
    let vbv = !best_v;
    let vbw = !best_w;
    let vec = !edge_count;
    
    let root_u = find parent vbu n;
    let root_v = find parent vbv n;
    
    let should_add: bool = (vbw > 0 && root_u <> root_v && vec <^ n);
    
    // Branchless writes: when not adding, preserve old values at position 0
    let old_eu0 = A.op_Array_Access edge_u 0sz;
    let old_ev0 = A.op_Array_Access edge_v 0sz;
    let write_pos: SZ.t = (if should_add then vec else 0sz);
    A.op_Array_Assignment edge_u write_pos (if should_add then SZ.v vbu else old_eu0);
    A.op_Array_Assignment edge_v write_pos (if should_add then SZ.v vbv else old_ev0);
    edge_count := (if should_add then vec +^ 1sz else vec);
    do_union parent root_u root_v n;
    
    // Bind post-write existentials and call unified proof
    with sparent_new. assert (A.pts_to parent sparent_new);
    with seu_new. assert (A.pts_to edge_u seu_new);
    with sev_new. assert (A.pts_to edge_v sev_new);
    with vec_new. assert (R.pts_to edge_count vec_new);
    kruskal_step_maintains_inv
      sparent_cur sparent_new seu_cur sev_cur seu_new sev_new
      (SZ.v n) (SZ.v vec) (SZ.v vec_new) (SZ.v vbu) (SZ.v vbv)
      (SZ.v root_u) (SZ.v root_v) should_add;
    edges_adj_pos_step sadj seu_cur sev_cur seu_new sev_new
      (SZ.v n) (SZ.v vec) (SZ.v vec_new) (SZ.v vbu) (SZ.v vbv) should_add;
    
    round := vround +^ 1sz;
  };
  
  // After loop: extract facts from opaque kruskal_inv for result proof
  with sp_f. assert (A.pts_to parent sp_f);
  with seu_f sev_f vec_f. assert (
    A.pts_to edge_u seu_f ** A.pts_to edge_v sev_f ** R.pts_to edge_count vec_f);
  kruskal_inv_elim sp_f seu_f sev_f (SZ.v n) (SZ.v vec_f);
  lemma_kruskal_maintains_forest seu_f sev_f (SZ.v n) (SZ.v vec_f);
  
  // Clean up
  rewrite (A.pts_to parent sp_f) as (A.pts_to (V.vec_to_array parent_v) sp_f);
  V.to_vec_pts_to parent_v;
  V.free parent_v;
}
#pop-options

(*** Impl ↔ Spec Bridging — Pure Helper Functions ***)

(*
   The postcondition (result_is_forest_adj) proves:
   - The selected edges form a forest (acyclic)
   - All endpoints are valid vertices (< n)
   - Edge count ≤ n-1
   - Each edge comes from a positive adjacency matrix entry (edges_adj_pos)

   The functions below provide the pure machinery to convert between
   the imperative representation (flat adjacency matrix, edge arrays)
   and the graph/edge-list representation used in MST.Spec.
   
   A full MST proof would additionally need to show:
   - The weighted edges form a spanning tree of the input graph
   - The total weight is minimum among all spanning trees
   These require the cut property (MST.Spec.cut_property) applied
   inductively at each algorithm step.
*)

// Convert flat adjacency matrix (array of int, n×n) to graph
// Emits one edge {u, v, w} for each position (u,v) with w > 0 and u < v
// (avoiding duplicates for undirected graphs)
let rec adj_row_edges (sadj: Seq.seq int) (n: nat) (u v: nat)
  : Pure (list edge)
    (requires Seq.length sadj == n * n /\ u < n /\ v <= n /\ n > 0)
    (ensures fun _ -> True)
    (decreases (n - v))
  = if v >= n then []
    else
      let w = Seq.index sadj (u * n + v) in
      let rest = adj_row_edges sadj n u (v + 1) in
      if w > 0 && u < v then { u = u; v = v; w = w } :: rest
      else rest

let rec adj_all_edges (sadj: Seq.seq int) (n: nat) (u: nat)
  : Pure (list edge)
    (requires Seq.length sadj == n * n /\ u <= n /\ n > 0)
    (ensures fun _ -> True)
    (decreases (n - u))
  = if u >= n then []
    else adj_row_edges sadj n u 0 @ adj_all_edges sadj n (u + 1)

let adj_array_to_graph (sadj: Seq.seq int) (n: nat{Seq.length sadj == n * n /\ n > 0}) : graph =
  { n = n; edges = adj_all_edges sadj n 0 }

// Edges with actual weights from the adjacency matrix
// (edges_from_arrays uses weight 1 for internal forest tracking;
//  this version uses adj[u*n+v] for MST weight reasoning)
let rec weighted_edges_from_arrays
  (sadj: Seq.seq int) (seu sev: Seq.seq int) (n: nat) (ec: nat) (i: nat{i <= ec})
  : Pure (list edge)
    (requires 
      n > 0 /\ ec <= Seq.length seu /\ ec <= Seq.length sev /\
      Seq.length sadj == n * n /\
      (forall (k:nat). i <= k /\ k < ec ==> 
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
        Seq.index seu k < n /\ Seq.index sev k < n))
    (ensures fun r -> FStar.List.Tot.length r = ec - i)
    (decreases (ec - i))
  = if i >= ec then []
    else
      let u_int = Seq.index seu i in
      let v_int = Seq.index sev i in
      let w = Seq.index sadj (u_int * n + v_int) in
      {u = u_int; v = v_int; w = w} :: weighted_edges_from_arrays sadj seu sev n ec (i + 1)

(*** Graph Properties for MST Bridge ***)

/// Adjacency matrix is symmetric (undirected graph)
let symmetric_adj (sadj: Seq.seq int) (n: nat) : prop =
  Seq.length sadj == n * n /\
  (forall (u v: nat). u < n /\ v < n ==>
    Seq.index sadj (u * n + v) = Seq.index sadj (v * n + u))

/// No self-loops: diagonal entries are zero
let no_self_loops_adj (sadj: Seq.seq int) (n: nat) : prop =
  Seq.length sadj == n * n /\
  (forall (u: nat). u < n ==> Seq.index sadj (u * n + u) = 0)

(*** Bridging Lemmas: adj_array_to_graph has valid edges ***)

/// Each entry in adj_row_edges has endpoints u < v < n
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let rec adj_row_edges_props (sadj: Seq.seq int) (n: nat) (u: nat) (v: nat) (e: edge)
  : Lemma
    (requires Seq.length sadj == n * n /\ u < n /\ v <= n /\ n > 0 /\
              mem_edge e (adj_row_edges sadj n u v))
    (ensures e.u < n /\ e.v < n /\ e.u <> e.v)
    (decreases (n - v))
  = if v >= n then ()
    else
      let w = Seq.index sadj (u * n + v) in
      if w > 0 && u < v then begin
        if edge_eq e {u = u; v = v; w = w} then
          MSTSpec.edge_eq_endpoints e {u = u; v = v; w = w}
        else
          adj_row_edges_props sadj n u (v + 1) e
      end
      else
        adj_row_edges_props sadj n u (v + 1) e
#pop-options

/// Each entry in adj_all_edges has valid endpoints
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let rec adj_all_edges_props (sadj: Seq.seq int) (n: nat) (u: nat) (e: edge)
  : Lemma
    (requires Seq.length sadj == n * n /\ u <= n /\ n > 0 /\
              mem_edge e (adj_all_edges sadj n u))
    (ensures e.u < n /\ e.v < n /\ e.u <> e.v)
    (decreases (n - u))
  = if u >= n then ()
    else begin
      MSTSpec.mem_edge_append e (adj_row_edges sadj n u 0) (adj_all_edges sadj n (u + 1));
      if mem_edge e (adj_row_edges sadj n u 0) then
        adj_row_edges_props sadj n u 0 e
      else
        adj_all_edges_props sadj n (u + 1) e
    end
#pop-options

/// The graph produced by adj_array_to_graph has valid edges
let adj_graph_valid_edges (sadj: Seq.seq int) (n: nat)
  : Lemma
    (requires Seq.length sadj == n * n /\ n > 0)
    (ensures
      (forall (e: edge). mem_edge e (adj_array_to_graph sadj n).edges ==> 
        e.u < n /\ e.v < n /\ e.u <> e.v))
  = let aux (e: edge) : Lemma
      (requires mem_edge e (adj_all_edges sadj n 0))
      (ensures e.u < n /\ e.v < n /\ e.u <> e.v)
    = adj_all_edges_props sadj n 0 e
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(*** Bridging Lemmas: weighted edges ⊆ graph edges ***)

/// If u < v < n and adj[u*n+v] > 0, then {u,v,adj[u*n+v]} ∈ adj_row_edges
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let rec adj_row_edges_mem (sadj: Seq.seq int) (n: nat) (u: nat) (target_v: nat) (v: nat)
  : Lemma
    (requires Seq.length sadj == n * n /\ u < n /\ v <= n /\ n > 0 /\
              v <= target_v /\ target_v < n /\
              u < target_v /\ Seq.index sadj (u * n + target_v) > 0)
    (ensures mem_edge ({u = u; v = target_v; w = Seq.index sadj (u * n + target_v)})
                       (adj_row_edges sadj n u v))
    (decreases (n - v))
  = if v >= n then ()
    else if v = target_v then
      MSTSpec.edge_eq_reflexive ({u = u; v = target_v; w = Seq.index sadj (u * n + target_v)})
    else
      adj_row_edges_mem sadj n u target_v (v + 1)
#pop-options

/// Membership in a row's edges implies membership in all edges
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let rec adj_all_edges_row_mem (sadj: Seq.seq int) (n: nat) (u: nat) (e: edge) (start_u: nat)
  : Lemma
    (requires Seq.length sadj == n * n /\ n > 0 /\ u < n /\ start_u <= u /\ start_u <= n /\
              mem_edge e (adj_row_edges sadj n u 0))
    (ensures mem_edge e (adj_all_edges sadj n start_u))
    (decreases (n - start_u))
  = if start_u >= n then ()
    else begin
      MSTSpec.mem_edge_append e (adj_row_edges sadj n start_u 0) (adj_all_edges sadj n (start_u + 1));
      if start_u = u then ()
      else adj_all_edges_row_mem sadj n u e (start_u + 1)
    end
#pop-options

/// Each weighted edge is a graph edge (inductive helper)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 50 --split_queries always"
let rec weighted_edges_subset_graph_aux
    (sadj: Seq.seq int) (seu sev: Seq.seq int) (n: nat) (ec: nat) (i: nat{i <= ec})
  : Lemma
    (requires
      n > 0 /\ ec <= Seq.length seu /\ ec <= Seq.length sev /\
      Seq.length sadj == n * n /\
      symmetric_adj sadj n /\
      no_self_loops_adj sadj n /\
      (forall (k:nat). i <= k /\ k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
        Seq.index seu k < n /\ Seq.index sev k < n /\
        Seq.index sadj (Seq.index seu k * n + Seq.index sev k) > 0))
    (ensures
      subset_edges (weighted_edges_from_arrays sadj seu sev n ec i) (adj_all_edges sadj n 0))
    (decreases (ec - i))
  = if i >= ec then ()
    else begin
      weighted_edges_subset_graph_aux sadj seu sev n ec (i + 1);
      let u_int = Seq.index seu i in
      let v_int = Seq.index sev i in
      let w = Seq.index sadj (u_int * n + v_int) in
      if u_int = v_int then begin
        // Contradiction: no_self_loops says adj[u*n+u] = 0, but w > 0
        assert (Seq.index sadj (u_int * n + u_int) = 0);
        assert false
      end
      else if u_int < v_int then begin
        adj_row_edges_mem sadj n u_int v_int 0;
        adj_all_edges_row_mem sadj n u_int ({u = u_int; v = v_int; w = w}) 0
      end
      else begin
        // u_int > v_int: use symmetry
        assert (Seq.index sadj (v_int * n + u_int) = Seq.index sadj (u_int * n + v_int));
        let canonical : edge = {u = v_int; v = u_int; w = w} in
        adj_row_edges_mem sadj n v_int u_int 0;
        adj_all_edges_row_mem sadj n v_int canonical 0;
        // edge_eq canonical {u_int, v_int, w} holds since canonical swaps endpoints
        MSTSpec.mem_edge_eq canonical ({u = u_int; v = v_int; w = w}) (adj_all_edges sadj n 0)
      end
    end
#pop-options

/// Weighted edges are subset of graph edges
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let weighted_edges_subset_graph
    (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires
      n > 0 /\ Seq.length sadj == n * n /\
      ec <= Seq.length seu /\ ec <= Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
                                    Seq.index seu k < n /\ Seq.index sev k < n) /\
      edges_adj_pos sadj seu sev n ec /\
      symmetric_adj sadj n /\
      no_self_loops_adj sadj n)
    (ensures
      subset_edges (weighted_edges_from_arrays sadj seu sev n ec 0) (adj_array_to_graph sadj n).edges)
  = edges_adj_pos_elim sadj seu sev n ec;
    weighted_edges_subset_graph_aux sadj seu sev n ec 0
#pop-options

(*** Main MST Theorem for Kruskal's Implementation ***)

/// If the weighted edges form a safe spanning tree, the result is an MST.
///
/// Preconditions from the Pulse function: result_is_forest_adj
/// Additional preconditions (true for Kruskal's greedy selection, but
/// not yet tracked by the Pulse loop invariant):
///   - Graph is symmetric with no self-loops
///   - Weighted edges form a spanning tree (connectivity + acyclicity)
///   - Weighted edges are safe (⊆ some MST), from greedy_step_safe induction
///   - No duplicate weighted edges
///
/// See Kruskal.Bridge for greedy_step_safe and safe_spanning_tree_is_mst.
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let kruskal_result_is_mst
    (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires
      n > 0 /\ Seq.length sadj == n * n /\
      ec <= Seq.length seu /\ ec <= Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
                                    Seq.index seu k < n /\ Seq.index sev k < n) /\
      result_is_forest_adj sadj seu sev n ec /\
      symmetric_adj sadj n /\
      no_self_loops_adj sadj n /\
      is_spanning_tree (adj_array_to_graph sadj n) (weighted_edges_from_arrays sadj seu sev n ec 0) /\
      (exists (t: list edge). is_mst (adj_array_to_graph sadj n) t /\
        subset_edges (weighted_edges_from_arrays sadj seu sev n ec 0) t) /\
      Bridge.noRepeats_edge (weighted_edges_from_arrays sadj seu sev n ec 0) /\
      (forall (e: edge). mem_edge e (adj_array_to_graph sadj n).edges ==>
        e.u < n /\ e.v < n /\ e.u <> e.v))
    (ensures
      is_mst (adj_array_to_graph sadj n) (weighted_edges_from_arrays sadj seu sev n ec 0))
  = Bridge.safe_spanning_tree_is_mst
      (adj_array_to_graph sadj n)
      (weighted_edges_from_arrays sadj seu sev n ec 0)
#pop-options
