(*
   Spec validation test for Binary Search (CLRS §2.3, Exercise 2.3-5)

   Tests the CLRS.Ch04.BinarySearch.Impl.fsti API on a small concrete instance:
   - Found case:     search for 3 in [1; 3; 5] → proves result == 1
   - Not found case: search for 2 in [1; 3; 5] → proves result == 3 (sentinel)

   Validates:
   - Precondition (is_sorted) is satisfiable on concrete sorted input
   - Postcondition uniquely determines the output for concrete inputs
   - No admits. No assumes.
*)

module CLRS.Ch04.BinarySearch.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch04.BinarySearch.Impl
open CLRS.Ch04.BinarySearch.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"

// Test 1: Found case — search for 3 in sorted array [1; 3; 5]
// Expected: result == 1 (the index where 3 resides)
//
// Postcondition reasoning (Z3 derives this automatically):
//   From result <= 3:
//   - If result == 3, postcondition gives forall i < 3. s0[i] != 3.
//     But s0[1] = 3, contradiction. So result < 3.
//   - Then s0[result] == 3. Since s0 = [1,3,5]:
//     result=0 → s0[0]=1 ≠ 3, result=2 → s0[2]=5 ≠ 3.
//     Only result=1 works: s0[1]=3 == 3. ✓
fn test_binary_search_found ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0))
       as (A.pts_to arr (Seq.create 3 0));
  A.pts_to_len arr;
  arr.(0sz) <- 1;
  arr.(1sz) <- 3;
  arr.(2sz) <- 5;

  let ctr = GR.alloc #nat 0;
  let result = binary_search arr 3sz 3 ctr;

  // Postcondition precision: result is uniquely determined
  assert (pure (SZ.v result == 1));

  // Cleanup
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s1. assert (A.pts_to arr s1);
  rewrite (A.pts_to arr s1) as (A.pts_to (V.vec_to_array v) s1);
  V.to_vec_pts_to v;
  V.free v;
  ()
}

// Test 2: Not found case — search for 2 in sorted array [1; 3; 5]
// Expected: result == 3 (sentinel value = len, meaning not found)
//
// Postcondition reasoning (Z3 derives this automatically):
//   If result < 3, then s0[result] == 2.
//   But s0 = [1,3,5], and none of 1,3,5 equals 2.
//   So result < 3 leads to contradiction, hence result == 3.
fn test_binary_search_not_found ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0))
       as (A.pts_to arr (Seq.create 3 0));
  A.pts_to_len arr;
  arr.(0sz) <- 1;
  arr.(1sz) <- 3;
  arr.(2sz) <- 5;

  let ctr = GR.alloc #nat 0;
  let result = binary_search arr 3sz 2 ctr;

  // Postcondition precision: result is uniquely determined (not found sentinel)
  assert (pure (SZ.v result == SZ.v 3sz));

  // Cleanup
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s1. assert (A.pts_to arr s1);
  rewrite (A.pts_to arr s1) as (A.pts_to (V.vec_to_array v) s1);
  V.to_vec_pts_to v;
  V.free v;
  ()
}

#pop-options
