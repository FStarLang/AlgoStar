(*
   Spec validation test for Rod Cutting (CLRS §15.1)

   Adapted from: https://github.com/microsoft/intent-formalization/blob/main/
     eval-autoclrs-specs/intree-tests/ch15-dynamic-programming/Test.RodCutting.fst

   Input: prices = [1, 5, 8, 9] for rod lengths 1–4
   Expected: optimal_revenue [1,5,8,9] 4 = 10
     (optimal cut: two pieces of length 2, revenue = 5 + 5 = 10)

   What is proven:
   1. The precondition of rod_cutting is satisfiable for a concrete input.
   2. The postcondition is precise: after calling rod_cutting, we can prove
      result == 10 (the known optimal) using only the postcondition
      (result == optimal_revenue s_prices n) and a normalization lemma.
   3. No admits, no assumes.
*)

module CLRS.Ch15.RodCutting.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch15.RodCutting.Impl
open CLRS.Ch15.RodCutting.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Prove the expected output by normalizing the spec on the concrete input
let rod_cutting_expected ()
  : Lemma (optimal_revenue (Seq.seq_of_list [1; 5; 8; 9]) 4 == 10)
  = assert_norm (optimal_revenue (Seq.seq_of_list [1; 5; 8; 9]) 4 == 10)

/// Prove the precondition is satisfiable
let rod_cutting_pre_satisfiable ()
  : Lemma
    (ensures SZ.fits (SZ.v 4sz + 1))
  = assert_norm (SZ.fits (SZ.v 4sz + 1))

#push-options "--z3rlimit 10"
fn test_rod_cutting ()
  requires emp
  returns _: unit
  ensures emp
{
  // Allocate price array [1, 5, 8, 9]
  let pv = V.alloc (0 <: nat) 4sz;
  V.to_array_pts_to pv;
  let prices_arr = V.vec_to_array pv;
  rewrite (A.pts_to (V.vec_to_array pv) (Seq.create 4 (0 <: nat)))
       as (A.pts_to prices_arr (Seq.create 4 (0 <: nat)));
  A.pts_to_len prices_arr;
  assert (pure (A.length prices_arr == SZ.v 4sz));

  A.op_Array_Assignment prices_arr 0sz (1 <: nat);
  A.op_Array_Assignment prices_arr 1sz (5 <: nat);
  A.op_Array_Assignment prices_arr 2sz (8 <: nat);
  A.op_Array_Assignment prices_arr 3sz (9 <: nat);

  // Prove precondition is satisfiable
  rod_cutting_pre_satisfiable ();

  // Call rod_cutting
  let ctr = GR.alloc #nat 0;
  let result = rod_cutting prices_arr 4sz ctr;

  // Prove the result is exactly 10 using the postcondition
  // The postcondition gives us: result == optimal_revenue s_prices 4
  // The lemma gives us: optimal_revenue [1,5,8,9] 4 == 10
  rod_cutting_expected ();
  assert (pure (result == 10));

  // Cleanup
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  with s1. assert (A.pts_to prices_arr s1);
  rewrite (A.pts_to prices_arr s1) as (A.pts_to (V.vec_to_array pv) s1);
  V.to_vec_pts_to pv;
  V.free pv;
}
#pop-options
