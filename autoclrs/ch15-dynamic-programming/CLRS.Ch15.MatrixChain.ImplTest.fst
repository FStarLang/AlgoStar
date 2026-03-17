(*
   Spec validation test for Matrix Chain Multiplication (CLRS §15.2)

   Adapted from: https://github.com/microsoft/intent-formalization/blob/main/
     eval-autoclrs-specs/intree-tests/ch15-dynamic-programming/Test.MatrixChain.fst

   Input: dims = [10, 30, 5, 60], n = 3 (three matrices)
     Matrix A₁: 10×30, A₂: 30×5, A₃: 5×60
   Expected: mc_result [10,30,5,60] 3 = 4500
     Optimal parenthesization: (A₁A₂)A₃
       cost = 10*30*5 + 10*5*60 = 1500 + 3000 = 4500

   What is proven:
   1. The precondition of matrix_chain_order is satisfiable for a concrete input.
   2. The postcondition is precise: after calling matrix_chain_order, we can
      prove result == 4500 using only the postcondition
      (result == mc_result s_dims n) and a normalization lemma.
   3. Non-negativity: result >= 0 is proven directly from the postcondition.
   4. No admits, no assumes.
*)

module CLRS.Ch15.MatrixChain.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch15.MatrixChain.Impl
open CLRS.Ch15.MatrixChain.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Prove the expected output by normalizing the spec on the concrete input
let mc_expected ()
  : Lemma (mc_result (Seq.seq_of_list [10; 30; 5; 60]) 3 == 4500)
  = assert_norm (mc_result (Seq.seq_of_list [10; 30; 5; 60]) 3 == 4500)

/// Prove the precondition is satisfiable
let mc_pre_satisfiable ()
  : Lemma
    (ensures SZ.v 3sz > 0 /\
             SZ.fits (op_Multiply (SZ.v 3sz) (SZ.v 3sz)))
  = assert_norm (SZ.v 3sz > 0 /\
                 SZ.fits (op_Multiply (SZ.v 3sz) (SZ.v 3sz)))

#push-options "--z3rlimit 20"

fn test_matrix_chain ()
  requires emp
  returns _: unit
  ensures emp
{
  // Allocate dimension array [10, 30, 5, 60]
  let dv = V.alloc 10 4sz;
  V.to_array_pts_to dv;
  let dims = V.vec_to_array dv;
  rewrite (A.pts_to (V.vec_to_array dv) (Seq.create 4 10))
       as (A.pts_to dims (Seq.create 4 10));
  A.pts_to_len dims;
  assert (pure (A.length dims == SZ.v 4sz));

  dims.(0sz) <- 10;
  dims.(1sz) <- 30;
  dims.(2sz) <- 5;
  dims.(3sz) <- 60;

  // Prove precondition is satisfiable
  mc_pre_satisfiable ();

  // Call matrix_chain_order
  let ctr = GR.alloc #nat 0;
  let result = matrix_chain_order dims 3sz ctr;

  // Prove the result is exactly 4500 using the postcondition
  mc_expected ();
  assert (pure (result == 4500));

  // Verify non-negativity directly from postcondition (no extra lemmas needed)
  assert (pure (result >= 0));

  // Cleanup
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  with s1. assert (A.pts_to dims s1);
  rewrite (A.pts_to dims s1) as (A.pts_to (V.vec_to_array dv) s1);
  V.to_vec_pts_to dv;
  V.free dv;
}

#pop-options
