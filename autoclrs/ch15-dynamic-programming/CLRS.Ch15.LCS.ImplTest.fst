(*
   Spec validation test for Longest Common Subsequence (CLRS §15.4)

   Adapted from: https://github.com/microsoft/intent-formalization/blob/main/
     eval-autoclrs-specs/intree-tests/ch15-dynamic-programming/Test.LCS.fst

   Input: x = [1, 2, 3], y = [2, 3, 4], m = 3, n = 3
   Expected: lcs_length [1,2,3] [2,3,4] 3 3 = 2
     LCS is [2, 3], length 2

   What is proven:
   1. The precondition of lcs is satisfiable for a concrete input.
   2. The postcondition is precise: after calling lcs, we can prove
      result == 2 using only the postcondition
      (result == lcs_length sx sy m n) and a normalization lemma.
   3. No admits, no assumes.
*)

module CLRS.Ch15.LCS.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch15.LCS.Impl
open CLRS.Ch15.LCS.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Prove the expected output by normalizing the spec on the concrete input
let lcs_expected ()
  : Lemma (lcs_length (Seq.seq_of_list [1; 2; 3]) (Seq.seq_of_list [2; 3; 4]) 3 3 == 2)
  = assert_norm (lcs_length (Seq.seq_of_list [1; 2; 3]) (Seq.seq_of_list [2; 3; 4]) 3 3 == 2)

/// Prove the precondition is satisfiable
let lcs_pre_satisfiable ()
  : Lemma
    (ensures SZ.fits (op_Multiply (SZ.v 3sz + 1) (SZ.v 3sz + 1)))
  = assert_norm (SZ.fits (op_Multiply (SZ.v 3sz + 1) (SZ.v 3sz + 1)))

fn test_lcs ()
  requires emp
  returns _: unit
  ensures emp
{
  // Allocate x = [1, 2, 3]
  let xv = V.alloc 0 3sz;
  V.to_array_pts_to xv;
  let x_arr = V.vec_to_array xv;
  rewrite (A.pts_to (V.vec_to_array xv) (Seq.create 3 0))
       as (A.pts_to x_arr (Seq.create 3 0));
  A.pts_to_len x_arr;
  assert (pure (A.length x_arr == SZ.v 3sz));

  x_arr.(0sz) <- 1;
  x_arr.(1sz) <- 2;
  x_arr.(2sz) <- 3;

  // Allocate y = [2, 3, 4]
  let yv = V.alloc 0 3sz;
  V.to_array_pts_to yv;
  let y_arr = V.vec_to_array yv;
  rewrite (A.pts_to (V.vec_to_array yv) (Seq.create 3 0))
       as (A.pts_to y_arr (Seq.create 3 0));
  A.pts_to_len y_arr;
  assert (pure (A.length y_arr == SZ.v 3sz));

  y_arr.(0sz) <- 2;
  y_arr.(1sz) <- 3;
  y_arr.(2sz) <- 4;

  // Prove precondition is satisfiable
  lcs_pre_satisfiable ();

  // Call lcs
  let ctr = GR.alloc #nat 0;
  let result = lcs x_arr y_arr 3sz 3sz ctr;

  // Prove the result is exactly 2 using the postcondition
  lcs_expected ();
  assert (pure (result == 2));

  // Cleanup
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  with sy1. assert (A.pts_to y_arr sy1);
  rewrite (A.pts_to y_arr sy1) as (A.pts_to (V.vec_to_array yv) sy1);
  V.to_vec_pts_to yv;
  V.free yv;

  with sx1. assert (A.pts_to x_arr sx1);
  rewrite (A.pts_to x_arr sx1) as (A.pts_to (V.vec_to_array xv) sx1);
  V.to_vec_pts_to xv;
  V.free xv;
}
