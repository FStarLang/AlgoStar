(*
   Spec validation test for Rod Cutting (CLRS Â§15.1)

   Input: prices = [1, 5, 8, 9] for rod lengths 1â4
   Expected: optimal_revenue [1,5,8,9] 4 = 10
     (optimal cut: two pieces of length 2, revenue = 5 + 5 = 10)

   What is proven:
   1. The precondition of rod_cutting is satisfiable for a concrete input.
   2. The postcondition is precise: result == 10 (the known optimal).
   3. No admits, no assumes.
   4. Runtime check: returns bool (true iff result == 10), proven true.
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

let rod_cutting_expected ()
  : Lemma (optimal_revenue (Seq.seq_of_list [1; 5; 8; 9]) 4 == 10)
  = assert_norm (optimal_revenue (Seq.seq_of_list [1; 5; 8; 9]) 4 == 10)

let rod_cutting_pre_satisfiable ()
  : Lemma
    (ensures SZ.fits (SZ.v 4sz + 1))
  = assert_norm (SZ.fits (SZ.v 4sz + 1))

#push-options "--z3rlimit 10"
fn test_rod_cutting ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
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

  rod_cutting_pre_satisfiable ();

  let ctr = GR.alloc #nat 0;
  let result = rod_cutting prices_arr 4sz ctr;

  rod_cutting_expected ();
  assert (pure (result == 10));

  // Runtime check that survives extraction to C
  let pass = (result = 10);

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  with s1. assert (A.pts_to prices_arr s1);
  rewrite (A.pts_to prices_arr s1) as (A.pts_to (V.vec_to_array pv) s1);
  V.to_vec_pts_to pv;
  V.free pv;

  pass
}
#pop-options
