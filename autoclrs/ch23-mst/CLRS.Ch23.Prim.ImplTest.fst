(*
   CLRS Chapter 23: Prim's Algorithm — Verified Test

   Calls the imperative `fn prim` on a concrete 3-vertex triangle graph
   and proves the output is the unique MST: 0 --1-- 1 --2-- 2.

   Test instance:
     3-vertex triangle graph (source = vertex 0):
       0 --1-- 1 --2-- 2
       |               |
       +------3--------+
     Weight matrix (flat 3×3, SZ.t): [0,1,3, 1,0,2, 3,2,0]
     Expected MST: edges {(0,1) w=1, (1,2) w=2}, total weight = 3
     Expected key array:    [0, 1, 2]   (key[v] = weight of MST edge to v)
     Expected parent array: [0, 0, 1]   (parent[v] = MST parent of v)

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ prim_correct: key/parent consistency, parent validity
        ✓ prim_mst_result → is_mst: output IS a minimum spanning tree
        ✓ mst_test_facts + prim_unique_output: key=[0,1,2], parent=[0,0,1]
        ✓ ensures (r == true): proof guarantees the runtime check passes

     2. RUNTIME (computational, survives extraction to C):
        ✓ sz_eq comparisons check key=[0,1,2], parent=[0,0,1]
        ✓ Returns bool — caller can verify at runtime

   Admits: SZ.fits_u64 (platform assumption — 64-bit SizeT).
*)
module CLRS.Ch23.Prim.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.Prim.Impl
open CLRS.Ch23.Prim.ImplTestHelper

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* PLATFORM ASSUMPTION: 64-bit SizeT.
   SZ.fits_u64 is an abstract prop that asserts the platform's SizeT
   type is at least 64 bits wide. It cannot be proven from first
   principles — it is a property of the target platform.
   This is NOT a spec weakness; it is a deployment assumption. *)
let assume_fits_u64 () : Lemma (ensures SZ.fits_u64) = admit ()

(* ---------- Pure helpers ---------- *)

(* SZ.t equality check — computational, survives extraction to C *)
inline_for_extraction
let sz_eq (a b: SZ.t) : (r:bool{r <==> SZ.v a = SZ.v b}) =
  let open FStar.SizeT in not (a <^ b || b <^ a)

(* The concrete weight matrix as a sequence *)
let weights3 : Seq.seq SZ.t = Seq.seq_of_list [0sz; 1sz; 3sz; 1sz; 0sz; 2sz; 3sz; 2sz; 0sz]

(* After 9 array writes, the ghost sequence equals weights3 *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 5"
let seq_after_writes_weights ()
  : Lemma (let s = Seq.create 9 0sz in
           let s = Seq.upd s 0 0sz in
           let s = Seq.upd s 1 1sz in
           let s = Seq.upd s 2 3sz in
           let s = Seq.upd s 3 1sz in
           let s = Seq.upd s 4 0sz in
           let s = Seq.upd s 5 2sz in
           let s = Seq.upd s 6 3sz in
           let s = Seq.upd s 7 2sz in
           let s = Seq.upd s 8 0sz in
           s `Seq.equal` weights3)
  = assert_norm (weights3 `Seq.equal` Seq.seq_of_list [0sz; 1sz; 3sz; 1sz; 0sz; 2sz; 3sz; 2sz; 0sz])
#pop-options

(* ---------- Main Test ---------- *)

// Test graph preconditions (concrete data, verified by inspection)
// weights_to_adj_matrix normalization too complex for assert_norm
// Test graph preconditions — each proved from concrete data
#push-options "--fuel 2 --ifuel 1 --z3rlimit 5"
let test_valid_weights_3 () : Lemma (valid_weights weights3 3) = ()
let test_symmetric_weights_3 () : Lemma (symmetric_weights weights3 3) = ()
let test_no_zero_edges_3 () : Lemma
  (forall (u v: nat). u < 3 /\ v < 3 /\ u * 3 + v < 9 /\
    SZ.v (Seq.index weights3 (u * 3 + v)) = 0 ==> u = v) = ()
#pop-options

// all_connected for the test graph: prove paths exist
#push-options "--fuel 10 --ifuel 10 --z3rlimit 30 --split_queries always"
let test_all_connected_impl () : Lemma
  (CLRS.Ch23.MST.Spec.all_connected 3
    (CLRS.Ch23.Prim.Spec.adj_to_edges (weights_to_adj_matrix weights3 3) 3))
  = let adj = weights_to_adj_matrix weights3 3 in
    CLRS.Ch23.Prim.Spec.well_formed_adj_intro adj 3;
    CLRS.Ch23.Prim.Spec.has_edge_intro adj 3 0 1;
    CLRS.Ch23.Prim.Spec.adj_to_graph_has_edge adj 3 0 1;
    CLRS.Ch23.Prim.Spec.has_edge_intro adj 3 1 2;
    CLRS.Ch23.Prim.Spec.adj_to_graph_has_edge adj 3 1 2;
    CLRS.Ch23.Prim.Spec.adj_to_graph_edges adj 3;
    let es = CLRS.Ch23.Prim.Spec.adj_to_edges adj 3 in
    let e01 : CLRS.Ch23.MST.Spec.edge = {u=0; v=1; w=1} in
    let e12 : CLRS.Ch23.MST.Spec.edge = {u=1; v=2; w=2} in
    CLRS.Ch23.MST.Spec.edge_eq_reflexive e01;
    CLRS.Ch23.MST.Spec.edge_eq_reflexive e12;
    assert (CLRS.Ch23.MST.Spec.is_path_from_to [] 0 0);
    assert (CLRS.Ch23.MST.Spec.subset_edges ([] <: list CLRS.Ch23.MST.Spec.edge) es);
    assert (CLRS.Ch23.MST.Spec.is_path_from_to [e01] 0 1);
    assert (CLRS.Ch23.MST.Spec.subset_edges [e01] es);
    assert (CLRS.Ch23.MST.Spec.is_path_from_to [e01; e12] 0 2);
    assert (CLRS.Ch23.MST.Spec.subset_edges [e01; e12] es)
#pop-options

#push-options "--z3rlimit 5"
let test_graph_preconditions (ws: Seq.seq SZ.t) : Lemma
  (requires ws == weights3)
  (ensures
    valid_weights ws 3 /\
    symmetric_weights ws 3 /\
    CLRS.Ch23.MST.Spec.all_connected 3 (CLRS.Ch23.Prim.Spec.adj_to_edges (weights_to_adj_matrix ws 3) 3) /\
    (forall (u v: nat). u < 3 /\ v < 3 /\ u * 3 + v < 9 /\
      SZ.v (Seq.index ws (u * 3 + v)) = 0 ==> u = v))
  = test_valid_weights_3 ();
    test_symmetric_weights_3 ();
    test_no_zero_edges_3 ();
    test_all_connected_impl ()
#pop-options


// Derive concrete key/parent values from prim_correct + concrete weights
#push-options "--z3rlimit 10 --fuel 10 --ifuel 10"

```pulse
fn test_prim_3 ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // --- Set up weight matrix for 3-vertex triangle ---
  // Graph:  0 --1-- 1 --2-- 2
  //         |               |
  //         +------3--------+
  // Flat 3×3 SZ.t: [0,1,3, 1,0,2, 3,2,0]
  let wv = V.alloc 0sz 9sz;
  V.to_array_pts_to wv;
  let weights = V.vec_to_array wv;
  rewrite (A.pts_to (V.vec_to_array wv) (Seq.create 9 0sz))
       as (A.pts_to weights (Seq.create 9 0sz));

  weights.(0sz) <- 0sz;
  weights.(1sz) <- 1sz;
  weights.(2sz) <- 3sz;
  weights.(3sz) <- 1sz;
  weights.(4sz) <- 0sz;
  weights.(5sz) <- 2sz;
  weights.(6sz) <- 3sz;
  weights.(7sz) <- 2sz;
  weights.(8sz) <- 0sz;

  // --- Precondition verification ---
  // SZ.v 3sz > 0                      ✓
  // SZ.v 3sz * SZ.v 3sz < pow2 64     ✓ (9 < 2^64)
  // SZ.v 0sz < SZ.v 3sz               ✓ (source=0 < n=3)
  // Seq.length weights_seq == 9        ✓
  // SZ.fits_u64                        assumed (platform: 64-bit SizeT)

  // Platform assumption: 64-bit SizeT
  assume_fits_u64 ();

  // Bind ghost sequence for weights before calling prim
  with ws. assert (A.pts_to weights ws);

  // Establish ws == weights3 from the array writes
  seq_after_writes_weights ();
  // Establish new prim preconditions for the test graph
  test_graph_preconditions ws;

  // --- Call prim ---
  let (key_vec, parent_vec) = prim weights 3sz 0sz;

  // --- Extract postcondition ---
  // prim_correct key_seq parent_seq ws 3 0
  // prim_mst_result parent_seq key_seq ws 3 0
  with key_seq parent_seq.
    assert (V.pts_to (key_vec) key_seq **
            V.pts_to (parent_vec) parent_seq **
            pure (prim_correct key_seq parent_seq ws 3 0 /\
                  prim_mst_result parent_seq key_seq ws 3 0));

  // --- Read output arrays ---

  // Convert key vec to array for reading
  V.to_array_pts_to (key_vec);
  let key_arr = V.vec_to_array (key_vec);
  rewrite (A.pts_to (V.vec_to_array (key_vec)) key_seq)
       as (A.pts_to key_arr key_seq);

  // ✓ PROVEN: key[source] == 0
  let k0 = key_arr.(0sz);
  assert (pure (SZ.v k0 == 0));

  // Read all keys and parents
  let k1 = key_arr.(1sz);
  let k2 = key_arr.(2sz);

  // Convert key array back to vec for cleanup
  with ks. assert (A.pts_to key_arr ks);
  rewrite (A.pts_to key_arr ks) as (A.pts_to (V.vec_to_array (key_vec)) ks);
  V.to_vec_pts_to (key_vec);

  // Convert parent vec to array for reading
  V.to_array_pts_to (parent_vec);
  let parent_arr = V.vec_to_array (parent_vec);
  rewrite (A.pts_to (V.vec_to_array (parent_vec)) parent_seq)
       as (A.pts_to parent_arr parent_seq);

  let p0 = parent_arr.(0sz);
  let p1 = parent_arr.(1sz);
  let p2 = parent_arr.(2sz);
  assert (pure (SZ.v p0 == 0));  // parent[source] = source

  // --- Proof: derive unique MST output ---
  mst_test_facts parent_seq key_seq ws;
  prim_unique_output key_seq parent_seq ws;
  assert (pure (SZ.v k1 == 1 /\ SZ.v p1 == 0 /\
                SZ.v k2 == 2 /\ SZ.v p2 == 1));

  // --- Runtime check (survives extraction to C) ---
  let pass = sz_eq k0 0sz && sz_eq k1 1sz && sz_eq k2 2sz &&
             sz_eq p0 0sz && sz_eq p1 0sz && sz_eq p2 1sz;

  // Convert parent array back to vec for cleanup
  with ps2. assert (A.pts_to parent_arr ps2);
  rewrite (A.pts_to parent_arr ps2) as (A.pts_to (V.vec_to_array (parent_vec)) ps2);
  V.to_vec_pts_to (parent_vec);

  // --- Also proven: is_mst via two independent paths ---
  prim_mst_result_elim parent_seq key_seq ws 3 0;
  test_prim_mst ();

  // --- Cleanup: free returned vectors (is_full_vec now in postcondition) ---
  V.free key_vec;
  V.free parent_vec;

  with ws2. assert (A.pts_to weights ws2);
  rewrite (A.pts_to weights ws2) as (A.pts_to (V.vec_to_array wv) ws2);
  V.to_vec_pts_to wv;
  V.free wv;

  pass
}
```

#pop-options
