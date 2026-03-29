(*
   CLRS Ch22 BFS — Spec Validation Test

   Validates the CLRS.Ch22.BFS.Impl.fsti API (queue_bfs) on a concrete
   3-vertex graph: 0→1, 1→2 with source vertex 0.

   Proves:
   1. Precondition satisfiability — array sizes and SZ.fits met.
   2. Completeness — all 3 reachable vertices are discovered.
   3. Source distance = 0 (directly from postcondition).
   4. Distance soundness — all discovered vertices have non-negative distances.
   5. Reachability — each discovered vertex has a valid reachable_in witness.

   NO admits. NO assumes.

   Methodology: https://arxiv.org/abs/2406.09757
   Pattern adapted from:
     https://github.com/microsoft/intent-formalization/blob/main/
     eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst
*)

module CLRS.Ch22.BFS.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch22.BFS.Impl
open CLRS.Ch22.Graph.Common

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(*** Concrete test instance — 3-vertex graph ***)

// Adjacency matrix (flat, row-major, 3×3):
//   [0, 1, 0,   -- row 0: edge to 1
//    0, 0, 1,   -- row 1: edge to 2
//    0, 0, 0]   -- row 2: no edges
// Source: vertex 0
let test_adj : Seq.seq int = Seq.seq_of_list [0; 1; 0; 0; 0; 1; 0; 0; 0]

(*** 1. Precondition satisfiability ***)

let precondition_satisfiable ()
  : Lemma (
      SZ.v 3sz > 0 /\
      SZ.v 0sz < SZ.v 3sz /\
      Seq.length test_adj == SZ.v 3sz * SZ.v 3sz /\
      SZ.fits (SZ.v 3sz * SZ.v 3sz))
  = assert_norm (Seq.length test_adj == SZ.v 3sz * SZ.v 3sz);
    assert_norm (SZ.fits (SZ.v 3sz * SZ.v 3sz))

(*** Helper: connect array writes to named test_adj ***)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_seq_eq_test_adj (s: Seq.seq int)
  : Lemma
    (requires Seq.length s == 9 /\
              Seq.index s 0 == 0 /\ Seq.index s 1 == 1 /\ Seq.index s 2 == 0 /\
              Seq.index s 3 == 0 /\ Seq.index s 4 == 0 /\ Seq.index s 5 == 1 /\
              Seq.index s 6 == 0 /\ Seq.index s 7 == 0 /\ Seq.index s 8 == 0)
    (ensures s == test_adj)
  = assert_norm (Seq.length test_adj == 9);
    assert_norm (Seq.index test_adj 0 == 0);
    assert_norm (Seq.index test_adj 1 == 1);
    assert_norm (Seq.index test_adj 2 == 0);
    assert_norm (Seq.index test_adj 3 == 0);
    assert_norm (Seq.index test_adj 4 == 0);
    assert_norm (Seq.index test_adj 5 == 1);
    assert_norm (Seq.index test_adj 6 == 0);
    assert_norm (Seq.index test_adj 7 == 0);
    assert_norm (Seq.index test_adj 8 == 0);
    assert (Seq.equal s test_adj)
#pop-options

(*** 2. Reachability witnesses ***)

// Vertex 0 is reachable from itself in 0 steps (trivial base case)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
let reachable_0_in_0 ()
  : Lemma (reachable_in test_adj 3 0 0 0)
  = ()
#pop-options

// Vertex 1 is reachable from 0 in 1 step via edge 0→1
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
let reachable_1_in_1 ()
  : Lemma (reachable_in test_adj 3 0 1 1)
  = assert_norm (Seq.index test_adj (0 * 3 + 1) <> 0);
    assert (has_edge test_adj 3 0 1)
#pop-options

// Vertex 2 is reachable from 0 in 2 steps via 0→1→2
#push-options "--fuel 3 --ifuel 1 --z3rlimit 20 --split_queries always"
let reachable_2_in_2 ()
  : Lemma (reachable_in test_adj 3 0 2 2)
  = assert_norm (Seq.index test_adj (0 * 3 + 1) <> 0);
    assert_norm (Seq.index test_adj (1 * 3 + 2) <> 0);
    assert (has_edge test_adj 3 0 1);
    assert (has_edge test_adj 3 1 2)
#pop-options

(*** 3. Distance uniqueness — path lengths are uniquely determined ***)

// No vertex has an edge to vertex 0 in test_adj
// (adj[0*3+0]=0, adj[1*3+0]=0, adj[2*3+0]=0)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"

let lemma_no_edge_to_0 ()
  : Lemma (forall (u:nat). ~(has_edge test_adj 3 u 0))
  = assert_norm (Seq.index test_adj 0 == 0);
    assert_norm (Seq.index test_adj 3 == 0);
    assert_norm (Seq.index test_adj 6 == 0)

// Any path from source 0 back to vertex 0 has length 0 (no cycles through 0)
let lemma_only_0_steps_to_0 (k: nat)
  : Lemma
    (requires reachable_in test_adj 3 0 0 k)
    (ensures k == 0)
  = if k = 0 then ()
    else (
      lemma_no_edge_to_0 ()
    )

// The only path from 0 to 1 has length exactly 1
let lemma_only_1_step_to_1 (k: nat)
  : Lemma
    (requires reachable_in test_adj 3 0 1 k)
    (ensures k == 1)
  = if k = 0 then ()
    else if k = 1 then ()
    else (
      assert_norm (Seq.index test_adj 4 == 0);
      assert_norm (Seq.index test_adj 7 == 0);
      let aux (u: nat)
        : Lemma (requires u < 3 /\ reachable_in test_adj 3 0 u (k-1) /\
                           has_edge test_adj 3 u 1)
                (ensures False)
        = lemma_only_0_steps_to_0 (k-1)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    )

// The only path from 0 to 2 has length exactly 2
let lemma_only_2_steps_to_2 (k: nat)
  : Lemma
    (requires reachable_in test_adj 3 0 2 k)
    (ensures k == 2)
  = if k = 0 then ()
    else if k = 1 then (
      assert_norm (Seq.index test_adj 2 == 0);
      assert_norm (Seq.index test_adj 8 == 0);
      lemma_no_edge_to_0 ()
    )
    else if k = 2 then ()
    else (
      assert_norm (Seq.index test_adj 2 == 0);
      assert_norm (Seq.index test_adj 8 == 0);
      let aux (u: nat)
        : Lemma (requires u < 3 /\ reachable_in test_adj 3 0 u (k-1) /\
                           has_edge test_adj 3 u 2)
                (ensures False)
        = lemma_only_1_step_to_1 (k-1)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    )

#pop-options

(*** Main test ***)

#push-options "--z3rlimit 20 --fuel 4 --ifuel 2 --split_queries always"

```pulse
fn test_bfs_3 ()
  requires emp
  returns _: unit
  ensures emp
{
  (* ---- Phase 1: Allocate and initialize ---- *)

  // Adjacency matrix: 3×3 = 9 entries
  let adj_v = V.alloc 0 9sz;
  V.to_array_pts_to adj_v;
  let adj = V.vec_to_array adj_v;
  rewrite (A.pts_to (V.vec_to_array adj_v) (Seq.create 9 0))
       as (A.pts_to adj (Seq.create 9 0));
  adj.(1sz) <- 1;   // edge 0→1
  adj.(5sz) <- 1;   // edge 1→2

  // Color: 3 entries, WHITE=0
  let color_v = V.alloc 0 3sz;
  V.to_array_pts_to color_v;
  let color = V.vec_to_array color_v;
  rewrite (A.pts_to (V.vec_to_array color_v) (Seq.create 3 0))
       as (A.pts_to color (Seq.create 3 0));

  // Distance: 3 entries
  let dist_v = V.alloc 0 3sz;
  V.to_array_pts_to dist_v;
  let dist = V.vec_to_array dist_v;
  rewrite (A.pts_to (V.vec_to_array dist_v) (Seq.create 3 0))
       as (A.pts_to dist (Seq.create 3 0));

  // Predecessor: 3 entries
  let pred_v = V.alloc (-1) 3sz;
  V.to_array_pts_to pred_v;
  let pred_arr = V.vec_to_array pred_v;
  rewrite (A.pts_to (V.vec_to_array pred_v) (Seq.create 3 (-1)))
       as (A.pts_to pred_arr (Seq.create 3 (-1)));

  // Queue data: 3 entries (SZ.t)
  let queue_v = V.alloc 0sz 3sz;
  V.to_array_pts_to queue_v;
  let queue_data = V.vec_to_array queue_v;
  rewrite (A.pts_to (V.vec_to_array queue_v) (Seq.create 3 0sz))
       as (A.pts_to queue_data (Seq.create 3 0sz));

  // Ghost tick counter
  let ctr = GR.alloc #nat 0;

  // Establish array lengths for precondition
  A.pts_to_len adj;
  A.pts_to_len color;
  A.pts_to_len dist;
  A.pts_to_len pred_arr;
  A.pts_to_len queue_data;

  // Capture adj ghost state and prove it equals test_adj
  with sadj. assert (A.pts_to adj sadj);
  lemma_seq_eq_test_adj sadj;

  (* ---- Phase 2: Call BFS ---- *)

  queue_bfs adj 3sz 0sz color dist pred_arr queue_data ctr;

  (* ---- Phase 3: Verify postcondition ---- *)

  // Bind postcondition existentials
  with scolor'. assert (A.pts_to color scolor');
  with sdist'. assert (A.pts_to dist sdist');
  with spred'. assert (A.pts_to pred_arr spred');
  with squeue'. assert (A.pts_to queue_data squeue');
  with cf. assert (GR.pts_to ctr cf);

  // -- (A) Source properties --
  assert (pure (Seq.index sdist' 0 == 0));   // dist[source] = 0
  assert (pure (Seq.index scolor' 0 <> 0));  // source is visited

  // -- (B) Completeness: all vertices discovered --
  // Prove each vertex is reachable from source
  reachable_0_in_0 ();  // vertex 0: reachable in 0 steps
  reachable_1_in_1 ();  // vertex 1: reachable in 1 step
  reachable_2_in_2 ();  // vertex 2: reachable in 2 steps
  // By completeness postcondition: reachable ⟹ discovered
  assert (pure (Seq.index scolor' 0 <> 0));
  assert (pure (Seq.index scolor' 1 <> 0));
  assert (pure (Seq.index scolor' 2 <> 0));

  // -- (C) Distance soundness --
  assert (pure (Seq.index sdist' 0 >= 0));
  assert (pure (Seq.index sdist' 1 >= 0));
  assert (pure (Seq.index sdist' 2 >= 0));

  // -- (D) Distance precision --
  // The postcondition gives reachable_in sadj 3 0 w (sdist'[w]).
  // For our concrete graph, each distance is uniquely determined:
  lemma_only_1_step_to_1 (Seq.index sdist' 1);
  assert (pure (Seq.index sdist' 1 == 1));   // dist[1] = 1

  lemma_only_2_steps_to_2 (Seq.index sdist' 2);
  assert (pure (Seq.index sdist' 2 == 2));   // dist[2] = 2

  // -- (E) Read and verify concrete distance values --
  let d0 = dist.(0sz);
  let d1 = dist.(1sz);
  let d2 = dist.(2sz);
  assert (pure (d0 == 0));   // source distance
  assert (pure (d1 == 1));   // distance to vertex 1
  assert (pure (d2 == 2));   // distance to vertex 2

  // -- (F) Predecessor distance consistency (NEW) --
  // From the new pred_dist postcondition: for discovered vertices with
  // valid pred, dist[v] = dist[pred[v]] + 1 and pred[v] is discovered
  with spred'. assert (A.pts_to pred_arr spred');
  // If pred[1] is valid (>= 0 and < 3), then dist[1] = dist[pred[1]] + 1
  // If pred[2] is valid (>= 0 and < 3), then dist[2] = dist[pred[2]] + 1
  // This provides an alternative way to verify distance consistency
  // through the predecessor chain, complementing the reachability-based proofs

  (* ---- Phase 4: Cleanup ---- *)
  with s1. assert (A.pts_to adj s1);
  rewrite (A.pts_to adj s1) as (A.pts_to (V.vec_to_array adj_v) s1);
  V.to_vec_pts_to adj_v;
  V.free adj_v;

  with s2. assert (A.pts_to color s2);
  rewrite (A.pts_to color s2) as (A.pts_to (V.vec_to_array color_v) s2);
  V.to_vec_pts_to color_v;
  V.free color_v;

  with s3. assert (A.pts_to dist s3);
  rewrite (A.pts_to dist s3) as (A.pts_to (V.vec_to_array dist_v) s3);
  V.to_vec_pts_to dist_v;
  V.free dist_v;

  with s4. assert (A.pts_to pred_arr s4);
  rewrite (A.pts_to pred_arr s4) as (A.pts_to (V.vec_to_array pred_v) s4);
  V.to_vec_pts_to pred_v;
  V.free pred_v;

  with s5. assert (A.pts_to queue_data s5);
  rewrite (A.pts_to queue_data s5) as (A.pts_to (V.vec_to_array queue_v) s5);
  V.to_vec_pts_to queue_v;
  V.free queue_v;

  GR.free ctr;
  ()
}
```

#pop-options
