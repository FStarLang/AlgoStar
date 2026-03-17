(*
   CLRS Ch22 Topological Sort — Spec Validation Test

   Validates the CLRS.Ch22.TopologicalSort.Impl.fsti API (topological_sort)
   on a concrete 3-vertex DAG: 0→1, 1→2.

   Proves:
   1. Precondition satisfiability — including ~(has_cycle) via a
      concrete topological order witness and lemma_topo_order_implies_dag.
   2. Output elements are valid vertex indices (< n).
   3. Output elements are non-negative.
   4. Output elements are all distinct (via all_distinct).
   5. Output is a valid topological order (via is_topological_order).

   NO admits. NO assumes.

   Methodology: https://arxiv.org/abs/2406.09757
   Pattern adapted from:
     https://github.com/microsoft/intent-formalization/blob/main/
     eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst
*)

module CLRS.Ch22.TopologicalSort.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open Pulse.Lib.WithPure
open CLRS.Ch22.TopologicalSort.Spec
open CLRS.Ch22.TopologicalSort.Impl.Defs
open CLRS.Ch22.TopologicalSort.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(*** Concrete test instance — 3-vertex DAG ***)

// Adjacency matrix (flat, row-major, 3×3):
//   [0, 1, 0,   -- row 0: edge to 1
//    0, 0, 1,   -- row 1: edge to 2
//    0, 0, 0]   -- row 2: no edges
let test_adj : Seq.seq int = Seq.seq_of_list [0; 1; 0; 0; 0; 1; 0; 0; 0]

// The only valid topological order: [0, 1, 2]
let test_order : Seq.seq nat = Seq.seq_of_list [0; 1; 2]

(*** 1. Precondition satisfiability ***)

let fits_9 () : Lemma (SZ.fits (SZ.v 3sz * SZ.v 3sz))
  = assert_norm (SZ.fits (SZ.v 3sz * SZ.v 3sz))

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

(*** 2. Prove graph is DAG: construct topological order, use theorem ***)

// Position lookups for the witness topological order [0,1,2]
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"

let positions_correct ()
  : Lemma (
      position_in_order test_order 0 == Some 0 /\
      position_in_order test_order 1 == Some 1 /\
      position_in_order test_order 2 == Some 2)
  = lemma_position_in_order_correct test_order 0 0;
    lemma_position_in_order_correct test_order 1 0;
    lemma_position_in_order_correct test_order 2 0

// Enumerate all edges and verify appears_before
let edge_01_ordered ()
  : Lemma (requires has_edge 3 test_adj 0 1)
          (ensures appears_before test_order 0 1)
  = positions_correct ()

let edge_12_ordered ()
  : Lemma (requires has_edge 3 test_adj 1 2)
          (ensures appears_before test_order 1 2)
  = positions_correct ()

// Enumerate all vertex pairs to prove no other edges exist
let no_other_edges ()
  : Lemma (
      has_edge 3 test_adj 0 0 == false /\
      has_edge 3 test_adj 0 2 == false /\
      has_edge 3 test_adj 1 0 == false /\
      has_edge 3 test_adj 1 1 == false /\
      has_edge 3 test_adj 2 0 == false /\
      has_edge 3 test_adj 2 1 == false /\
      has_edge 3 test_adj 2 2 == false)
  = assert_norm (has_edge 3 test_adj 0 0 == false);
    assert_norm (has_edge 3 test_adj 0 2 == false);
    assert_norm (has_edge 3 test_adj 1 0 == false);
    assert_norm (has_edge 3 test_adj 1 1 == false);
    assert_norm (has_edge 3 test_adj 2 0 == false);
    assert_norm (has_edge 3 test_adj 2 1 == false);
    assert_norm (has_edge 3 test_adj 2 2 == false)

// test_order is a valid topological order for test_adj
let is_topo_order_test ()
  : Lemma (is_topological_order test_adj 3 test_order)
  = assert_norm (Seq.length test_order == 3);
    assert_norm (Seq.length test_adj == 3 * 3);
    positions_correct ();
    no_other_edges ();
    assert_norm (has_edge 3 test_adj 0 1 == true);
    assert_norm (has_edge 3 test_adj 1 2 == true);
    // For u >= 3 or v >= 3, has_edge returns false by the u < n check
    // Z3 can derive the universal quantifier from the concrete enumeration
    ()

// Main DAG proof: no cycles in test_adj
let no_cycle_test ()
  : Lemma (~(has_cycle test_adj 3))
  = is_topo_order_test ();
    lemma_topo_order_implies_dag test_adj 3 test_order

#pop-options

(*** Main test ***)

#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"

```pulse
fn test_topo_sort_3 ()
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

  // Ghost tick counter
  let ctr = GR.alloc #nat 0;

  // Establish array length for precondition
  A.pts_to_len adj;

  // Capture adj ghost state and prove it equals test_adj
  with sadj. assert (A.pts_to adj sadj);
  lemma_seq_eq_test_adj sadj;

  // Prove graph is a DAG (required by precondition)
  no_cycle_test ();

  (* ---- Phase 2: Call topological_sort ---- *)

  let output = topological_sort adj 3sz ctr;

  (* ---- Phase 3: Verify postcondition ---- *)

  // Bind postcondition existentials
  with sout. assert (V.pts_to output sout);
  with cf. assert (GR.pts_to ctr cf);

  // -- (A) Output length --
  assert (pure (Seq.length sout == 3));

  // -- (B) All output elements are valid vertex indices --
  assert (pure (Seq.index sout 0 < 3));
  assert (pure (Seq.index sout 1 < 3));
  assert (pure (Seq.index sout 2 < 3));

  // -- (C) All output elements are non-negative --
  assert (pure (Seq.index sout 0 >= 0));
  assert (pure (Seq.index sout 1 >= 0));
  assert (pure (Seq.index sout 2 >= 0));

  // -- (D) All distinct --
  assert (pure (all_distinct (seq_int_to_nat sout)));

  // -- (E) Valid topological order --
  assert (pure (is_topological_order sadj 3 (seq_int_to_nat sout)));

  // -- (F) Complexity bound --
  assert (pure (cf - 0 <= 3 * 3));

  (* ---- Phase 4: Cleanup ---- *)
  // Free the output vec
  drop_ (V.pts_to output sout);

  with s1. assert (A.pts_to adj s1);
  rewrite (A.pts_to adj s1) as (A.pts_to (V.vec_to_array adj_v) s1);
  V.to_vec_pts_to adj_v;
  V.free adj_v;

  GR.free ctr;
  ()
}
```

#pop-options
