(*
   CLRS Chapter 23: Kruskal's Algorithm — Spec Validation Test

   Validates the Impl.fsti API for CLRS §23.2 Kruskal's MST algorithm
   by calling it on a small concrete instance and checking what the
   postcondition can prove about the output.

   Test instance:
     3-vertex triangle graph:
       0 --1-- 1 --2-- 2
       |               |
       +------3--------+
     Adjacency matrix (flat 3×3): [0,1,3, 1,0,2, 3,2,0]
     Expected MST: edges {(0,1) w=1, (1,2) w=2}, total weight = 3

   Result: The postcondition `result_is_forest_adj` is declared as an
   opaque `val` in the .fsti. However, we added an elim lemma
   `result_is_forest_adj_elim` that exposes concrete facts:
     ✓ Precondition is satisfiable
     ✓ Edge count bounded by n-1 (ec <= 2 for n=3)
     ✓ All selected endpoints are valid vertices (< n)
     ✓ Each selected edge has a positive adjacency matrix entry
     ✗ Cannot verify exact edge count (could be 0, 1, or 2)
     ✗ Cannot verify specific edge endpoints
     ✗ Cannot verify spanning tree or MST property

   Attribution: Pattern inspired by
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   NO admits. NO assumes.
*)
module CLRS.Ch23.Kruskal.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.Kruskal.Impl
open CLRS.Ch23.Kruskal.ImplTestHelper

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* ---------- Test ---------- *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

(*
   Satisfiability & completeness test for Kruskal's algorithm.

   This test constructs a concrete 3-vertex triangle graph and calls
   the verified kruskal function. It demonstrates that:

   1. The PRECONDITION IS SATISFIABLE: we can construct a valid input
      that meets all requirements (n > 0, adj sized n×n, output arrays
      sized n, SZ.fits(n*n)).

   2. The POSTCONDITION IS OPAQUE: result_is_forest_adj is declared as
      `val result_is_forest_adj (sadj: Seq.seq int) (seu sev: Seq.seq int)
       (n ec: nat) : prop`
      in CLRS.Ch23.Kruskal.Impl.fsti, making it completely opaque to
      external consumers. We cannot unfold it to learn:
      - How many edges were selected (ec value)
      - Which specific edges were selected
      - That the result is a spanning tree
      - That the result is an MST

   FINDING: The Kruskal API's postcondition is too opaque for spec
   validation. A consumer calling kruskal gets a proof of an opaque
   prop but cannot extract any useful information from it.
*)

```pulse
fn test_kruskal_satisfiability ()
  requires emp
  returns _: unit
  ensures emp
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
  let eu_v = V.alloc 0 3sz;
  V.to_array_pts_to eu_v;
  let edge_u = V.vec_to_array eu_v;
  rewrite (A.pts_to (V.vec_to_array eu_v) (Seq.create 3 0))
       as (A.pts_to edge_u (Seq.create 3 0));

  let ev_v = V.alloc 0 3sz;
  V.to_array_pts_to ev_v;
  let edge_v = V.vec_to_array ev_v;
  rewrite (A.pts_to (V.vec_to_array ev_v) (Seq.create 3 0))
       as (A.pts_to edge_v (Seq.create 3 0));

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

  // --- Postcondition analysis ---
  // We now have (existentially quantified):
  //   result_is_forest_adj sadj sedge_u' sedge_v' 3 (SZ.v vec)
  //
  // Using the elim lemma result_is_forest_adj_elim, we CAN extract:
  //   - ec <= n - 1 = 2 (edge count bound)
  //   - All selected edge endpoints are valid (< n = 3)
  //   - Each selected edge has a positive adjacency matrix entry
  //
  // We still CANNOT determine:
  //   - The exact value of ec (could be 0, 1, or 2)
  //   - Which specific edges were selected
  //   - Whether the result is a spanning tree or MST

  // Read edge count
  let ec_val = !ec_ref;

  // Apply the elim lemma to extract concrete facts
  with sadj sedge_u' sedge_v'.
    assert (A.pts_to adj sadj **
            A.pts_to edge_u sedge_u' **
            A.pts_to edge_v sedge_v' **
            pure (result_is_forest_adj sadj sedge_u' sedge_v' 3 (SZ.v ec_val)));
  result_is_forest_adj_elim sadj sedge_u' sedge_v' 3 (SZ.v ec_val);

  // ✓ PROVEN: edge count bounded by n-1 = 2
  assert (pure (SZ.v ec_val <= 2));

  // ✓ PROVEN: output arrays have correct length
  assert (pure (Seq.length sedge_u' == 3));
  assert (pure (Seq.length sedge_v' == 3));

  // ✓ PROVEN: all selected endpoints are valid vertices
  assert (pure (forall (k:nat). k < SZ.v ec_val ==>
    Seq.index sedge_u' k >= 0 /\ Seq.index sedge_u' k < 3 /\
    Seq.index sedge_v' k >= 0 /\ Seq.index sedge_v' k < 3));

  // ✓ PROVEN: each selected edge has a positive adjacency matrix entry
  assert (pure (forall (k:nat). k < SZ.v ec_val ==>
    Seq.index sadj (Seq.index sedge_u' k * 3 + Seq.index sedge_v' k) > 0));

  // ✓ PROVEN (NEW): the selected edges form a forest (acyclic subgraph)
  result_is_forest_adj_forest_elim sadj sedge_u' sedge_v' 3 (SZ.v ec_val);
  assert (pure (CLRS.Ch23.Kruskal.Spec.is_forest
    (edges_from_arrays sedge_u' sedge_v' (SZ.v ec_val) 0) 3));

  // ✓ PROVEN (MST): the pure spec determines an MST for this graph
  //   (proven in CLRS.Ch23.Kruskal.ImplTestHelper.test_mst via pure_kruskal_is_mst)
  test_mst ();
  assert (pure (CLRS.Ch23.MST.Spec.is_mst
    (adj_array_to_graph (Seq.seq_of_list [0;1;3;1;0;2;3;2;0]) 3)
    (CLRS.Ch23.Kruskal.Spec.pure_kruskal
      (adj_array_to_graph (Seq.seq_of_list [0;1;3;1;0;2;3;2;0]) 3))));

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
  ()
}
```

#pop-options
