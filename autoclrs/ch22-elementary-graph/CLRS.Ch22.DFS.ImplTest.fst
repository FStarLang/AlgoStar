(*
   CLRS Ch22 DFS — Spec Validation Test

   Validates the CLRS.Ch22.DFS.Impl.fsti API (stack_dfs) on a concrete
   3-vertex graph: 0→1, 1→2.

   Proves:
   1. Precondition satisfiability — array sizes and SZ.fits met.
   2. All vertices colored BLACK (color[u] == 2 for all u < n).
   3. Discovery times positive (d[u] > 0).
   4. Finish times positive (f[u] > 0).
   5. Parenthesis theorem: d[u] < f[u] for all u.
   6. pred_edge_ok — predecessor tree is a valid subgraph.

   NO admits. NO assumes.

   Methodology: https://arxiv.org/abs/2406.09757
   Pattern adapted from:
     https://github.com/microsoft/intent-formalization/blob/main/
     eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst
*)

module CLRS.Ch22.DFS.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch22.DFS.Impl
open CLRS.Ch22.Graph.Common

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(*** Concrete test instance — 3-vertex graph ***)

// Same graph as BFS test: edges 0→1 and 1→2
let test_adj : Seq.seq int = Seq.seq_of_list [0; 1; 0; 0; 0; 1; 0; 0; 0]

(*** 1. Precondition satisfiability ***)

let precondition_satisfiable ()
  : Lemma (
      SZ.v 3sz > 0 /\
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

(*** Main test ***)

#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"

```pulse
fn test_dfs_3 ()
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

  // Discovery time: 3 entries
  let d_v = V.alloc 0 3sz;
  V.to_array_pts_to d_v;
  let d_arr = V.vec_to_array d_v;
  rewrite (A.pts_to (V.vec_to_array d_v) (Seq.create 3 0))
       as (A.pts_to d_arr (Seq.create 3 0));

  // Finish time: 3 entries
  let f_v = V.alloc 0 3sz;
  V.to_array_pts_to f_v;
  let f_arr = V.vec_to_array f_v;
  rewrite (A.pts_to (V.vec_to_array f_v) (Seq.create 3 0))
       as (A.pts_to f_arr (Seq.create 3 0));

  // Predecessor: 3 entries
  let pred_v = V.alloc (-1) 3sz;
  V.to_array_pts_to pred_v;
  let pred_arr = V.vec_to_array pred_v;
  rewrite (A.pts_to (V.vec_to_array pred_v) (Seq.create 3 (-1)))
       as (A.pts_to pred_arr (Seq.create 3 (-1)));

  // Stack data: 3 entries (SZ.t)
  let stack_v = V.alloc 0sz 3sz;
  V.to_array_pts_to stack_v;
  let stack_data = V.vec_to_array stack_v;
  rewrite (A.pts_to (V.vec_to_array stack_v) (Seq.create 3 0sz))
       as (A.pts_to stack_data (Seq.create 3 0sz));

  // Scan index: 3 entries (SZ.t)
  let scan_v = V.alloc 0sz 3sz;
  V.to_array_pts_to scan_v;
  let scan_idx = V.vec_to_array scan_v;
  rewrite (A.pts_to (V.vec_to_array scan_v) (Seq.create 3 0sz))
       as (A.pts_to scan_idx (Seq.create 3 0sz));

  // Ghost tick counter
  let ctr = GR.alloc #nat 0;

  // Establish array lengths for precondition
  A.pts_to_len adj;
  A.pts_to_len color;
  A.pts_to_len d_arr;
  A.pts_to_len f_arr;
  A.pts_to_len pred_arr;
  A.pts_to_len stack_data;
  A.pts_to_len scan_idx;

  // Capture adj ghost state and prove it equals test_adj
  with sadj. assert (A.pts_to adj sadj);
  lemma_seq_eq_test_adj sadj;

  (* ---- Phase 2: Call DFS ---- *)

  stack_dfs adj 3sz color d_arr f_arr pred_arr stack_data scan_idx ctr;

  (* ---- Phase 3: Verify postcondition ---- *)

  // Bind postcondition existentials
  with scolor'. assert (A.pts_to color scolor');
  with sd'. assert (A.pts_to d_arr sd');
  with sf'. assert (A.pts_to f_arr sf');
  with spred'. assert (A.pts_to pred_arr spred');
  with sstack'. assert (A.pts_to stack_data sstack');
  with sscan'. assert (A.pts_to scan_idx sscan');
  with cf. assert (GR.pts_to ctr cf);

  // -- (A) All vertices colored BLACK (== 2) --
  assert (pure (Seq.index scolor' 0 == 2));
  assert (pure (Seq.index scolor' 1 == 2));
  assert (pure (Seq.index scolor' 2 == 2));

  // -- (B) Discovery times positive --
  assert (pure (Seq.index sd' 0 > 0));
  assert (pure (Seq.index sd' 1 > 0));
  assert (pure (Seq.index sd' 2 > 0));

  // -- (C) Finish times positive --
  assert (pure (Seq.index sf' 0 > 0));
  assert (pure (Seq.index sf' 1 > 0));
  assert (pure (Seq.index sf' 2 > 0));

  // -- (D) Parenthesis: d[u] < f[u] --
  assert (pure (Seq.index sd' 0 < Seq.index sf' 0));
  assert (pure (Seq.index sd' 1 < Seq.index sf' 1));
  assert (pure (Seq.index sd' 2 < Seq.index sf' 2));

  // -- (E) pred_edge_ok --
  assert (pure (pred_edge_ok sadj 3 scolor' sd' spred'));

  // -- (F) Complexity bound --
  assert (pure (cf - 0 <= 2 * (3 * 3)));

  (* ---- Phase 4: Cleanup ---- *)
  with s1. assert (A.pts_to adj s1);
  rewrite (A.pts_to adj s1) as (A.pts_to (V.vec_to_array adj_v) s1);
  V.to_vec_pts_to adj_v;
  V.free adj_v;

  with s2. assert (A.pts_to color s2);
  rewrite (A.pts_to color s2) as (A.pts_to (V.vec_to_array color_v) s2);
  V.to_vec_pts_to color_v;
  V.free color_v;

  with s3. assert (A.pts_to d_arr s3);
  rewrite (A.pts_to d_arr s3) as (A.pts_to (V.vec_to_array d_v) s3);
  V.to_vec_pts_to d_v;
  V.free d_v;

  with s4. assert (A.pts_to f_arr s4);
  rewrite (A.pts_to f_arr s4) as (A.pts_to (V.vec_to_array f_v) s4);
  V.to_vec_pts_to f_v;
  V.free f_v;

  with s5. assert (A.pts_to pred_arr s5);
  rewrite (A.pts_to pred_arr s5) as (A.pts_to (V.vec_to_array pred_v) s5);
  V.to_vec_pts_to pred_v;
  V.free pred_v;

  with s6. assert (A.pts_to stack_data s6);
  rewrite (A.pts_to stack_data s6) as (A.pts_to (V.vec_to_array stack_v) s6);
  V.to_vec_pts_to stack_v;
  V.free stack_v;

  with s7. assert (A.pts_to scan_idx s7);
  rewrite (A.pts_to scan_idx s7) as (A.pts_to (V.vec_to_array scan_v) s7);
  V.to_vec_pts_to scan_v;
  V.free scan_v;

  GR.free ctr;
  ()
}
```

#pop-options
