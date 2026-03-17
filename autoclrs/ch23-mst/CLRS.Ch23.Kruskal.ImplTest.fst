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
   opaque `val` in the .fsti, so external consumers cannot extract any
   information about the selected edges. The test proves:
     ✓ Precondition is satisfiable
     ✗ Cannot verify edge count, endpoints, or MST property from postcondition

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
  // Since result_is_forest_adj is an opaque val in the .fsti,
  // we CANNOT unfold it. We have no way to determine:
  //   - The value of vec (edge count)
  //   - The contents of sedge_u' or sedge_v'
  //   - Whether the result is a spanning tree or MST
  //
  // The postcondition is satisfied but provides no usable information
  // to the external consumer.

  // We CAN still read the actual values at runtime:
  let ec_val = !ec_ref;
  // But we CANNOT prove ec_val == 2 or any other specific value,
  // because result_is_forest_adj is opaque.

  // --- Cleanup ---
  with sadj. assert (A.pts_to adj sadj);
  rewrite (A.pts_to adj sadj) as (A.pts_to (V.vec_to_array adj_v) sadj);
  V.to_vec_pts_to adj_v;
  V.free adj_v;

  with seu. assert (A.pts_to edge_u seu);
  rewrite (A.pts_to edge_u seu) as (A.pts_to (V.vec_to_array eu_v) seu);
  V.to_vec_pts_to eu_v;
  V.free eu_v;

  with sev. assert (A.pts_to edge_v sev);
  rewrite (A.pts_to edge_v sev) as (A.pts_to (V.vec_to_array ev_v) sev);
  V.to_vec_pts_to ev_v;
  V.free ev_v;

  R.free ec_ref;
  ()
}
```

#pop-options
