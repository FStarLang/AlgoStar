(*
   CLRS Chapter 23: Kruskal's Algorithm — Verified Test

   Calls the imperative `fn kruskal` on a concrete 3-vertex triangle graph
   and proves the output is the unique MST: 0 --1-- 1 --2-- 2.

   Test instance:
     3-vertex triangle graph:
       0 --1-- 1 --2-- 2
       |               |
       +------3--------+
     Adjacency matrix (flat 3×3): [0,1,3, 1,0,2, 3,2,0]
     Expected MST: edges {(0,1) w=1, (1,2) w=2}, total weight = 3

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ result_is_forest_adj: forest + valid endpoints + positive weights
        ✓ kruskal_mst_result → is_mst: output IS a minimum spanning tree
        ✓ kruskal_mst_edges: MST edges are exactly {(0,1,1), (1,2,2)}
        ✓ ensures (r == true): proof guarantees the runtime check passes

     2. RUNTIME (computational, survives extraction to C):
        ✓ sz_eq comparisons check ec=2, edges={(0,1),(1,2)} in any order/direction
        ✓ Returns bool — caller can verify at runtime

   NO admits. NO assumes.
*)
module CLRS.Ch23.Kruskal.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.Kruskal.Defs
open CLRS.Ch23.Kruskal.Impl
open CLRS.Ch23.Kruskal.ImplTestHelper

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* SZ.t equality check — computational, survives extraction to C *)
inline_for_extraction
let sz_eq (a b: SZ.t) : (r:bool{r <==> SZ.v a = SZ.v b}) =
  let open FStar.SizeT in not (a <^ b || b <^ a)

(* ---------- Test ---------- *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 2 --split_queries always"

```pulse
fn test_kruskal_satisfiability ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // --- Set up adjacency matrix for 3-vertex triangle ---
  // Graph:  0 --1-- 1 --2-- 2
  //         |               |
  //         +------3--------+
  // Flat 3×3: [0, 1, 3, 1, 0, 2, 3, 2, 0]
  let adj_v = V.alloc 0 9sz;
  V.to_array_pts_to adj_v;
  let adj = V.vec_to_array adj_v;
  rewrite (A.pts_to (V.vec_to_array adj_v) (Seq.create 9 0))
       as (A.pts_to adj (Seq.create 9 0));

  adj.(0sz) <- 0;
  adj.(1sz) <- 1;
  adj.(2sz) <- 3;
  adj.(3sz) <- 1;
  adj.(4sz) <- 0;
  adj.(5sz) <- 2;
  adj.(6sz) <- 3;
  adj.(7sz) <- 2;
  adj.(8sz) <- 0;

  // --- Output edge arrays (capacity = n = 3) ---
  let eu_v = V.alloc 0sz 3sz;
  V.to_array_pts_to eu_v;
  let edge_u = V.vec_to_array eu_v;
  rewrite (A.pts_to (V.vec_to_array eu_v) (Seq.create 3 0sz))
       as (A.pts_to edge_u (Seq.create 3 0sz));

  let ev_v = V.alloc 0sz 3sz;
  V.to_array_pts_to ev_v;
  let edge_v = V.vec_to_array ev_v;
  rewrite (A.pts_to (V.vec_to_array ev_v) (Seq.create 3 0sz))
       as (A.pts_to edge_v (Seq.create 3 0sz));

  // --- Edge count reference, initialized to 0 ---
  let ec_ref = R.alloc 0sz;

  // --- Precondition verification ---
  // SZ.v 3sz > 0                     ✓ (3 > 0)
  // Seq.length sadj == 3 * 3 = 9     ✓ (9 elements written)
  // Seq.length sedge_u == 3           ✓ (V.alloc 0 3sz)
  // Seq.length sedge_v == 3           ✓ (V.alloc 0 3sz)
  // SZ.fits (3 * 3) = SZ.fits 9      ✓ (fits_at_least_16 fires: 9 < 2^16)

  // --- Call kruskal ---
  kruskal adj edge_u edge_v ec_ref 3sz;

  // --- Postcondition: forest + MST ---

  // Read edge count
  let ec_val = !ec_ref;

  // Apply the elim lemma to extract concrete facts
  with sadj sedge_u' sedge_v'.
    assert (A.pts_to adj sadj **
            A.pts_to edge_u sedge_u' **
            A.pts_to edge_v sedge_v' **
            pure (result_is_forest_adj sadj (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') 3 (SZ.v ec_val) /\
                  kruskal_mst_result sadj (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') 3 (SZ.v ec_val)));
  result_is_forest_adj_elim sadj (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') 3 (SZ.v ec_val);

  // Forest properties (from elim lemmas)
  assert (pure (SZ.v ec_val <= 2));
  assert (pure (Seq.length sedge_u' == 3));
  assert (pure (Seq.length sedge_v' == 3));

  // Valid endpoints and positive weights
  assert (pure (forall (k:nat). k < SZ.v ec_val ==>
    SZ.v (Seq.index sedge_u' k) >= 0 /\ SZ.v (Seq.index sedge_u' k) < 3 /\
    SZ.v (Seq.index sedge_v' k) >= 0 /\ SZ.v (Seq.index sedge_v' k) < 3));
  assert (pure (forall (k:nat). k < SZ.v ec_val ==>
    Seq.index sadj (SZ.v (Seq.index sedge_u' k) * 3 + SZ.v (Seq.index sedge_v' k)) > 0));

  // Forest (acyclic subgraph)
  result_is_forest_adj_forest_elim sadj (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') 3 (SZ.v ec_val);
  assert (pure (CLRS.Ch23.Kruskal.Spec.is_forest
    (edges_from_arrays (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') (SZ.v ec_val) 0) 3));

  // --- Proof: is_mst for the imperative output ---
  test_mst ();
  assert (pure (Seq.equal sadj (Seq.seq_of_list [0;1;3;1;0;2;3;2;0])));
  test_is_mst_imperative sadj (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') (SZ.v ec_val);
  // is_mst for the imperative kruskal output
  assert (pure (CLRS.Ch23.MST.Spec.is_mst (adj_array_to_graph sadj 3)
    (weighted_edges_from_arrays sadj (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') 3 (SZ.v ec_val) 0)));

  // --- Proof: unique MST edges {(0,1,1), (1,2,2)}, total weight 3 ---
  kruskal_mst_edges (weighted_edges_from_arrays sadj (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') 3 (SZ.v ec_val) 0);
  assert (pure (CLRS.Ch23.MST.Spec.total_weight
    (weighted_edges_from_arrays sadj (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') 3 (SZ.v ec_val) 0) == 3));

  // --- Runtime check (survives extraction to C) ---
  let eu0 = edge_u.(0sz);
  let ev0 = edge_v.(0sz);
  let eu1 = edge_u.(1sz);
  let ev1 = edge_v.(1sz);
  // MST edges are {(0,1),(1,2)} — any order, any endpoint direction
  let e0_is_01 = (sz_eq eu0 0sz && sz_eq ev0 1sz) || (sz_eq eu0 1sz && sz_eq ev0 0sz);
  let e0_is_12 = (sz_eq eu0 1sz && sz_eq ev0 2sz) || (sz_eq eu0 2sz && sz_eq ev0 1sz);
  let e1_is_01 = (sz_eq eu1 0sz && sz_eq ev1 1sz) || (sz_eq eu1 1sz && sz_eq ev1 0sz);
  let e1_is_12 = (sz_eq eu1 1sz && sz_eq ev1 2sz) || (sz_eq eu1 2sz && sz_eq ev1 1sz);
  let pass = sz_eq ec_val 2sz &&
             ((e0_is_01 && e1_is_12) || (e0_is_12 && e1_is_01));

  // --- Cleanup ---
  rewrite (A.pts_to adj sadj) as (A.pts_to (V.vec_to_array adj_v) sadj);
  V.to_vec_pts_to adj_v;
  V.free adj_v;

  rewrite (A.pts_to edge_u sedge_u') as (A.pts_to (V.vec_to_array eu_v) sedge_u');
  V.to_vec_pts_to eu_v;
  V.free eu_v;

  rewrite (A.pts_to edge_v sedge_v') as (A.pts_to (V.vec_to_array ev_v) sedge_v');
  V.to_vec_pts_to ev_v;
  V.free ev_v;

  R.free ec_ref;
  pass
}
```

#pop-options
