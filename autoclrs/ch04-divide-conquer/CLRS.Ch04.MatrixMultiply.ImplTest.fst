(*
   Spec validation test for Matrix Multiply (CLRS §4.2, pp. 75–76)

   Adapted from:
     https://github.com/microsoft/intent-formalization/blob/main/
       eval-autoclrs-specs/intree-tests/ch04-divide-conquer/Test.MatrixMultiply.fst

   Tests the CLRS.Ch04.MatrixMultiply.Impl.fsti API on a 2×2 instance:
     A = [[1,2],[3,4]], B = [[5,6],[7,8]]
     Expected C = [[19,22],[43,50]]

   Also verifies the exact complexity bound: 2³ = 8 multiply-add operations.

   Validates:
   - Precondition (n>0, SZ.fits, lengths match) is satisfiable
   - Postcondition (mat_mul_correct) uniquely determines all output entries
   - Complexity bound (cf == c0 + n³) is exact and verifiable
   - No admits. No assumes.
*)

module CLRS.Ch04.MatrixMultiply.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch04.MatrixMultiply.Impl
open CLRS.Ch04.MatrixMultiply.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ---------- Helper lemmas (pre-normalize spec for Z3) ----------

let mm_indices ()
  : Lemma (flat_index 2 0 0 == 0 /\
           flat_index 2 0 1 == 1 /\
           flat_index 2 1 0 == 2 /\
           flat_index 2 1 1 == 3)
  = assert_norm (flat_index 2 0 0 == 0 /\
                 flat_index 2 0 1 == 1 /\
                 flat_index 2 1 0 == 2 /\
                 flat_index 2 1 1 == 3)

// Connect ghost sequences (from array writes) to concrete values,
// then normalize dot_product_spec via extensional equality.
let mm_dot_products (sa sb: Seq.seq int)
  : Lemma
    (requires Seq.length sa == 4 /\ Seq.length sb == 4 /\
              Seq.index sa 0 == 1 /\ Seq.index sa 1 == 2 /\
              Seq.index sa 2 == 3 /\ Seq.index sa 3 == 4 /\
              Seq.index sb 0 == 5 /\ Seq.index sb 1 == 6 /\
              Seq.index sb 2 == 7 /\ Seq.index sb 3 == 8)
    (ensures dot_product_spec sa sb 2 0 0 2 == 19 /\
             dot_product_spec sa sb 2 0 1 2 == 22 /\
             dot_product_spec sa sb 2 1 0 2 == 43 /\
             dot_product_spec sa sb 2 1 1 2 == 50)
  = let sa' = Seq.seq_of_list [1; 2; 3; 4] in
    let sb' = Seq.seq_of_list [5; 6; 7; 8] in
    Seq.lemma_eq_intro sa sa';
    Seq.lemma_eq_intro sb sb';
    assert_norm (dot_product_spec sa' sb' 2 0 0 2 == 19);
    assert_norm (dot_product_spec sa' sb' 2 0 1 2 == 22);
    assert_norm (dot_product_spec sa' sb' 2 1 0 2 == 43);
    assert_norm (dot_product_spec sa' sb' 2 1 1 2 == 50)

let mm_2sz_pre ()
  : Lemma
    (ensures SZ.v 2sz > 0 /\
             SZ.v 4sz == op_Multiply (SZ.v 2sz) (SZ.v 2sz) /\
             SZ.fits (op_Multiply (SZ.v 2sz) (SZ.v 2sz)))
  = assert_norm (SZ.v 2sz > 0 /\
                 SZ.v 4sz == op_Multiply (SZ.v 2sz) (SZ.v 2sz) /\
                 SZ.fits (op_Multiply (SZ.v 2sz) (SZ.v 2sz)))

// ---------- Test function ----------

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"

fn test_matrix_multiply_2x2 ()
  requires emp
  returns _: unit
  ensures emp
{
  // Allocate A = [[1,2],[3,4]] as flat array [1,2,3,4]
  let av = V.alloc 0 4sz;
  V.to_array_pts_to av;
  let a_arr = V.vec_to_array av;
  rewrite (A.pts_to (V.vec_to_array av) (Seq.create 4 0))
       as (A.pts_to a_arr (Seq.create 4 0));
  A.pts_to_len a_arr;
  a_arr.(0sz) <- 1;
  a_arr.(1sz) <- 2;
  a_arr.(2sz) <- 3;
  a_arr.(3sz) <- 4;

  // Allocate B = [[5,6],[7,8]] as flat array [5,6,7,8]
  let bv = V.alloc 0 4sz;
  V.to_array_pts_to bv;
  let b_arr = V.vec_to_array bv;
  rewrite (A.pts_to (V.vec_to_array bv) (Seq.create 4 0))
       as (A.pts_to b_arr (Seq.create 4 0));
  A.pts_to_len b_arr;
  b_arr.(0sz) <- 5;
  b_arr.(1sz) <- 6;
  b_arr.(2sz) <- 7;
  b_arr.(3sz) <- 8;

  // Allocate C (output), initially all zeros
  let cv = V.alloc 0 4sz;
  V.to_array_pts_to cv;
  let c_arr = V.vec_to_array cv;
  rewrite (A.pts_to (V.vec_to_array cv) (Seq.create 4 0))
       as (A.pts_to c_arr (Seq.create 4 0));
  A.pts_to_len c_arr;

  // Bind ghost sequences before the call
  with sa0. assert (A.pts_to a_arr sa0);
  with sb0. assert (A.pts_to b_arr sb0);
  with sc0. assert (A.pts_to c_arr sc0);
  A.pts_to_len a_arr;
  A.pts_to_len b_arr;
  A.pts_to_len c_arr;

  // Establish preconditions
  mm_2sz_pre ();
  assert (pure (Seq.length sa0 == op_Multiply (SZ.v 2sz) (SZ.v 2sz)));
  assert (pure (Seq.length sb0 == op_Multiply (SZ.v 2sz) (SZ.v 2sz)));
  assert (pure (Seq.length sc0 == op_Multiply (SZ.v 2sz) (SZ.v 2sz)));

  // C = A × B
  let ctr = GR.alloc #nat 0;
  matrix_multiply a_arr b_arr c_arr 2sz ctr;

  // Bind result ghost sequence
  with sc1. assert (A.pts_to c_arr sc1);

  // Prove postcondition precision: mat_mul_correct determines exact output
  mm_indices ();
  mm_dot_products sa0 sb0;

  // Assert exact output values: C = [[19,22],[43,50]]
  assert (pure (Seq.index sc1 0 == 19));
  assert (pure (Seq.index sc1 1 == 22));
  assert (pure (Seq.index sc1 2 == 43));
  assert (pure (Seq.index sc1 3 == 50));

  // Read and verify concrete values (exercises extraction)
  let c00 = c_arr.(0sz);
  let c01 = c_arr.(1sz);
  let c10 = c_arr.(2sz);
  let c11 = c_arr.(3sz);
  assert (pure (c00 == 19));
  assert (pure (c01 == 22));
  assert (pure (c10 == 43));
  assert (pure (c11 == 50));

  // Cleanup
  with cf. assert (GR.pts_to ctr cf);
  // Complexity: exactly n³ = 2³ = 8 multiply-add operations
  assert (pure (cf == 8));
  GR.free ctr;

  with sc2. assert (A.pts_to c_arr sc2);
  rewrite (A.pts_to c_arr sc2) as (A.pts_to (V.vec_to_array cv) sc2);
  V.to_vec_pts_to cv;
  V.free cv;

  with sb1. assert (A.pts_to b_arr sb1);
  rewrite (A.pts_to b_arr sb1) as (A.pts_to (V.vec_to_array bv) sb1);
  V.to_vec_pts_to bv;
  V.free bv;

  with sa1. assert (A.pts_to a_arr sa1);
  rewrite (A.pts_to a_arr sa1) as (A.pts_to (V.vec_to_array av) sa1);
  V.to_vec_pts_to av;
  V.free av;
}

#pop-options
