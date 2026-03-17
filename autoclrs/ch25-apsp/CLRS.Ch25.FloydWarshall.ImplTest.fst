module CLRS.Ch25.FloydWarshall.ImplTest

(**
 * Spec validation test for Floyd-Warshall (CLRS §25.2).
 *
 * Tests the Impl.fsti API (`floyd_warshall`) on a concrete 3×3 graph,
 * proving:
 *
 * 1. Precondition satisfiability — the array-size and SZ.fits constraints
 *    are met for a concrete input.
 *
 * 2. Postcondition precision — the postcondition `contents' == fw_outer
 *    contents n 0` is strong enough to determine all 9 output entries
 *    exactly (shortest-path distances for every vertex pair).
 *
 * 3. Complexity — the ghost tick counter proves exactly n³ = 27
 *    relaxation operations.
 *
 * Methodology from: https://arxiv.org/abs/2406.09757
 * Testing pattern adapted from:
 *   https://github.com/microsoft/intent-formalization/blob/main/
 *   eval-autoclrs-specs/intree-tests/ch04-divide-conquer/Test.MatrixMultiply.fst
 *
 * NO admits. NO assumes.
 *)

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch25.FloydWarshall.Spec
open CLRS.Ch25.FloydWarshall.Impl
open CLRS.Ch25.FloydWarshall.Lemmas

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(*** Concrete test instance — 3×3 graph ***)

// 3×3 adjacency matrix (row-major):
//     0   1   2
// 0 [ 0   5  inf ]
// 1 [ 50  0   15 ]
// 2 [ 30 inf  0  ]
let test_adj : Seq.seq int = Seq.seq_of_list [0; 5; 1000000; 50; 0; 15; 30; 1000000; 0]

// Expected shortest-path distances after Floyd-Warshall:
//     0   1   2
// 0 [ 0   5   20 ]
// 1 [ 45  0   15 ]
// 2 [ 30  35  0  ]

(*** 1. Precondition satisfiability ***)

// The precondition of floyd_warshall requires:
//   Seq.length contents == SZ.v n * SZ.v n /\ SZ.fits (SZ.v n * SZ.v n)
// This is satisfiable for n = 3.
let precondition_satisfiable ()
  : Lemma (
      Seq.length test_adj == SZ.v 3sz * SZ.v 3sz /\
      SZ.fits (SZ.v 3sz * SZ.v 3sz))
  = assert_norm (Seq.length test_adj == SZ.v 3sz * SZ.v 3sz);
    assert_norm (SZ.fits (SZ.v 3sz * SZ.v 3sz))

(*** Helper: connect array write sequence to named test_adj ***)

// After 9 array writes in the Pulse function, the ghost state is a chain
// of Seq.upd operations. This lemma proves extensional equality with
// test_adj given the 9 concrete index values.
let lemma_seq_eq_test_adj (s: Seq.seq int)
  : Lemma
    (requires Seq.length s == 9 /\
              Seq.index s 0 == 0 /\ Seq.index s 1 == 5 /\ Seq.index s 2 == inf /\
              Seq.index s 3 == 50 /\ Seq.index s 4 == 0 /\ Seq.index s 5 == 15 /\
              Seq.index s 6 == 30 /\ Seq.index s 7 == inf /\ Seq.index s 8 == 0)
    (ensures s == test_adj)
  = assert_norm (Seq.length test_adj == 9);
    assert_norm (Seq.index test_adj 0 == 0);
    assert_norm (Seq.index test_adj 1 == 5);
    assert_norm (Seq.index test_adj 2 == inf);
    assert_norm (Seq.index test_adj 3 == 50);
    assert_norm (Seq.index test_adj 4 == 0);
    assert_norm (Seq.index test_adj 5 == 15);
    assert_norm (Seq.index test_adj 6 == 30);
    assert_norm (Seq.index test_adj 7 == inf);
    assert_norm (Seq.index test_adj 8 == 0);
    assert (Seq.equal s test_adj)

(*** 2. Postcondition precision — all 9 output entries ***)

// The postcondition states: contents' == fw_outer contents n 0
// Combined with floyd_warshall_full_correctness, this determines each
// output entry:
//   Seq.index (fw_outer test_adj 3 0) (qi*3+qj) == fw_entry test_adj 3 qi qj 3
// The SMT solver evaluates fw_entry to the expected concrete value.

#push-options "--fuel 8 --ifuel 2 --z3rlimit 80 --split_queries always"

// Step 1: Prove fw_entry values for all 9 entries (same as SpecTest.fst)
let fw_val_00 () : Lemma (fw_entry test_adj 3 0 0 3 == 0) = ()
let fw_val_01 () : Lemma (fw_entry test_adj 3 0 1 3 == 5) = ()
let fw_val_02 () : Lemma (fw_entry test_adj 3 0 2 3 == 20) = ()
let fw_val_10 () : Lemma (fw_entry test_adj 3 1 0 3 == 45) = ()
let fw_val_11 () : Lemma (fw_entry test_adj 3 1 1 3 == 0) = ()
let fw_val_12 () : Lemma (fw_entry test_adj 3 1 2 3 == 15) = ()
let fw_val_20 () : Lemma (fw_entry test_adj 3 2 0 3 == 30) = ()
let fw_val_21 () : Lemma (fw_entry test_adj 3 2 1 3 == 35) = ()
let fw_val_22 () : Lemma (fw_entry test_adj 3 2 2 3 == 0) = ()

// Step 2: Connect fw_outer to fw_entry, then to concrete values
let post_entry_00 () : Lemma (Seq.index (fw_outer test_adj 3 0) 0 == 0)
  = fw_val_00 (); floyd_warshall_full_correctness test_adj 3 0 0

let post_entry_01 () : Lemma (Seq.index (fw_outer test_adj 3 0) 1 == 5)
  = fw_val_01 (); floyd_warshall_full_correctness test_adj 3 0 1

let post_entry_02 () : Lemma (Seq.index (fw_outer test_adj 3 0) 2 == 20)
  = fw_val_02 (); floyd_warshall_full_correctness test_adj 3 0 2

let post_entry_10 () : Lemma (Seq.index (fw_outer test_adj 3 0) 3 == 45)
  = fw_val_10 (); floyd_warshall_full_correctness test_adj 3 1 0

let post_entry_11 () : Lemma (Seq.index (fw_outer test_adj 3 0) 4 == 0)
  = fw_val_11 (); floyd_warshall_full_correctness test_adj 3 1 1

let post_entry_12 () : Lemma (Seq.index (fw_outer test_adj 3 0) 5 == 15)
  = fw_val_12 (); floyd_warshall_full_correctness test_adj 3 1 2

let post_entry_20 () : Lemma (Seq.index (fw_outer test_adj 3 0) 6 == 30)
  = fw_val_20 (); floyd_warshall_full_correctness test_adj 3 2 0

let post_entry_21 () : Lemma (Seq.index (fw_outer test_adj 3 0) 7 == 35)
  = fw_val_21 (); floyd_warshall_full_correctness test_adj 3 2 1

let post_entry_22 () : Lemma (Seq.index (fw_outer test_adj 3 0) 8 == 0)
  = fw_val_22 (); floyd_warshall_full_correctness test_adj 3 2 2

#pop-options

(*** 3. Complexity bound ***)

let complexity_bound ()
  : Lemma (fw_complexity_bounded 27 0 3)
  = assert_norm (fw_complexity_bounded 27 0 3)

(*** Main test: call floyd_warshall and verify outputs ***)

```pulse
fn test_floyd_warshall_impl ()
  requires emp
  returns _: unit
  ensures emp
{
  let n = 3sz;

  // Allocate and initialize the 3×3 distance matrix
  let dv = V.alloc 0 9sz;
  V.to_array_pts_to dv;
  let dist = V.vec_to_array dv;
  rewrite (A.pts_to (V.vec_to_array dv) (Seq.create 9 0))
       as (A.pts_to dist (Seq.create 9 0));

  // Write the adjacency matrix
  A.op_Array_Assignment dist 0sz 0;
  A.op_Array_Assignment dist 1sz 5;
  A.op_Array_Assignment dist 2sz inf;
  A.op_Array_Assignment dist 3sz 50;
  A.op_Array_Assignment dist 4sz 0;
  A.op_Array_Assignment dist 5sz 15;
  A.op_Array_Assignment dist 6sz 30;
  A.op_Array_Assignment dist 7sz inf;
  A.op_Array_Assignment dist 8sz 0;

  // Capture input ghost state and prove it equals test_adj
  with s_in. assert (A.pts_to dist s_in);
  lemma_seq_eq_test_adj s_in;

  // Ghost tick counter
  let ctr = GR.alloc #nat 0;

  // --- Call the Impl.fsti API ---
  floyd_warshall dist n ctr;

  // --- Verify postcondition precision ---
  // Postcondition gives: contents' == fw_outer s_in 3 0
  // Since s_in == test_adj: contents' == fw_outer test_adj 3 0
  with contents'. assert (A.pts_to dist contents');

  // Verify all 9 output entries
  post_entry_00 ();
  assert (pure (Seq.index contents' 0 == 0));

  post_entry_01 ();
  assert (pure (Seq.index contents' 1 == 5));

  post_entry_02 ();
  assert (pure (Seq.index contents' 2 == 20));

  post_entry_10 ();
  assert (pure (Seq.index contents' 3 == 45));

  post_entry_11 ();
  assert (pure (Seq.index contents' 4 == 0));

  post_entry_12 ();
  assert (pure (Seq.index contents' 5 == 15));

  post_entry_20 ();
  assert (pure (Seq.index contents' 6 == 30));

  post_entry_21 ();
  assert (pure (Seq.index contents' 7 == 35));

  post_entry_22 ();
  assert (pure (Seq.index contents' 8 == 0));

  // --- Verify complexity: exactly 27 relaxation operations ---
  with cf. assert (GR.pts_to ctr cf);
  complexity_bound ();
  assert (pure (cf == 27));

  // Clean up
  GR.free ctr;
  rewrite (A.pts_to dist contents')
       as (A.pts_to (V.vec_to_array dv) contents');
  V.to_vec_pts_to dv;
  V.free dv;
}
```
