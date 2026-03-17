(*
   Spec validation test for Kadane's Maximum Subarray (CLRS §4.1)

   Tests the CLRS.Ch04.MaxSubarray.Kadane.fsti API on concrete instances:

   Test 1 — Mixed array:
     Input array: [-1, 3, -2]
     Expected result: 3  (the maximum contiguous subarray sum, achieved by [3])

   Test 2 — All-negative array:
     Input array: [-5, -3, -1]
     Expected result: -1  (the least-negative element, achieved by [-1])

   Both tests also verify the exact complexity bound (3 operations for 3 elements),
   exercising the now-transparent complexity_bounded_linear predicate from Spec.fst.

   Validates:
   - Precondition (len > 0, lengths match) is satisfiable
   - Postcondition (result == max_subarray_spec s0) is fully precise:
     it uniquely determines the output integer for any concrete input
   - Complexity bound (cf == c0 + len) is exact and verifiable
   - No admits. No assumes.
*)

module CLRS.Ch04.MaxSubarray.Kadane.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch04.MaxSubarray.Kadane
open CLRS.Ch04.MaxSubarray.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ---------- Helper lemma ----------

// Connect the ghost sequence (from array writes) to a concrete seq_of_list,
// then normalize max_subarray_spec to get the expected value.
//
// Trace of max_subarray_spec ([-1, 3, -2]):
//   kadane_spec s 0 0 (-1):
//     i=0: elem=-1, new_current=max(-1, 0+(-1))=-1, new_best=max(-1,-1)=-1
//   kadane_spec s 1 (-1) (-1):
//     i=1: elem=3, new_current=max(3, -1+3)=3, new_best=max(-1,3)=3
//   kadane_spec s 2 3 3:
//     i=2: elem=-2, new_current=max(-2, 3+(-2))=1, new_best=max(3,1)=3
//   kadane_spec s 3 1 3:
//     i=3 >= 3, return 3
//
// Result: 3 (the subarray [3] at index 1)

#push-options "--fuel 8 --ifuel 2"
let kadane_test_lemma (s: Seq.seq int)
  : Lemma
    (requires Seq.length s == 3 /\
              Seq.index s 0 == (0 - 1) /\
              Seq.index s 1 == 3 /\
              Seq.index s 2 == (0 - 2))
    (ensures max_subarray_spec s == 3)
  = let s' = Seq.seq_of_list [(0-1); 3; (0-2)] in
    assert_norm (Seq.length s' == 3);
    assert_norm (Seq.index s' 0 == (0 - 1));
    assert_norm (Seq.index s' 1 == 3);
    assert_norm (Seq.index s' 2 == (0 - 2));
    Seq.lemma_eq_intro s s';
    assert_norm (max_subarray_spec s' == 3)
#pop-options

// ---------- All-negative helper lemma ----------
//
// Trace of max_subarray_spec ([-5, -3, -1]):
//   kadane_spec s 0 0 (-5):
//     i=0: elem=-5, new_current=max(-5, 0+(-5))=-5, new_best=max(-5,-5)=-5
//   kadane_spec s 1 (-5) (-5):
//     i=1: elem=-3, new_current=max(-3, -5+(-3))=-3, new_best=max(-5,-3)=-3
//   kadane_spec s 2 (-3) (-3):
//     i=2: elem=-1, new_current=max(-1, -3+(-1))=-1, new_best=max(-3,-1)=-1
//   kadane_spec s 3 (-1) (-1):
//     i=3 >= 3, return -1
//
// Result: -1 (the least-negative element, subarray [-1] at index 2)

#push-options "--fuel 8 --ifuel 2"
let kadane_all_negative_lemma (s: Seq.seq int)
  : Lemma
    (requires Seq.length s == 3 /\
              Seq.index s 0 == (0 - 5) /\
              Seq.index s 1 == (0 - 3) /\
              Seq.index s 2 == (0 - 1))
    (ensures max_subarray_spec s == (0 - 1))
  = let s' = Seq.seq_of_list [(0-5); (0-3); (0-1)] in
    assert_norm (Seq.length s' == 3);
    assert_norm (Seq.index s' 0 == (0 - 5));
    assert_norm (Seq.index s' 1 == (0 - 3));
    assert_norm (Seq.index s' 2 == (0 - 1));
    Seq.lemma_eq_intro s s';
    assert_norm (max_subarray_spec s' == (0 - 1))
#pop-options

// ---------- Test functions ----------

#push-options "--z3rlimit 80 --fuel 8 --ifuel 2"

// Test 1: Mixed array — max subarray is a single positive element
fn test_kadane_max_subarray ()
  requires emp
  returns _: unit
  ensures emp
{
  // Create array [-1, 3, -2]
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0))
       as (A.pts_to arr (Seq.create 3 0));
  A.pts_to_len arr;
  arr.(0sz) <- (0 - 1);
  arr.(1sz) <- 3;
  arr.(2sz) <- (0 - 2);

  // Bind ghost sequence
  with s0. assert (A.pts_to arr s0);
  A.pts_to_len arr;

  let ctr = GR.alloc #nat 0;
  let result = max_subarray arr 3sz ctr;

  // Postcondition: result == max_subarray_spec s0
  // Helper lemma proves max_subarray_spec s0 == 3
  kadane_test_lemma s0;
  assert (pure (result == 3));

  // Complexity: exactly 3 operations for 3 elements
  // (Now provable because complexity_bounded_linear is transparent via Spec.fst)
  with cf. assert (GR.pts_to ctr cf);
  assert (pure (cf == 3));

  // Cleanup
  GR.free ctr;
  with s1. assert (A.pts_to arr s1);
  rewrite (A.pts_to arr s1) as (A.pts_to (V.vec_to_array v) s1);
  V.to_vec_pts_to v;
  V.free v;
  ()
}

// Test 2: All-negative array — result is the least-negative element
// This exercises the edge case where no positive subarray sum exists.
// Expected: result == -1 (the maximum element in [-5, -3, -1])
fn test_kadane_all_negative ()
  requires emp
  returns _: unit
  ensures emp
{
  // Create array [-5, -3, -1]
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0))
       as (A.pts_to arr (Seq.create 3 0));
  A.pts_to_len arr;
  arr.(0sz) <- (0 - 5);
  arr.(1sz) <- (0 - 3);
  arr.(2sz) <- (0 - 1);

  // Bind ghost sequence
  with s0. assert (A.pts_to arr s0);
  A.pts_to_len arr;

  let ctr = GR.alloc #nat 0;
  let result = max_subarray arr 3sz ctr;

  // Postcondition: result == max_subarray_spec s0
  // Helper lemma proves max_subarray_spec s0 == -1
  kadane_all_negative_lemma s0;
  assert (pure (result == (0 - 1)));

  // Complexity: exactly 3 operations for 3 elements
  with cf. assert (GR.pts_to ctr cf);
  assert (pure (cf == 3));

  // Cleanup
  GR.free ctr;
  with s1. assert (A.pts_to arr s1);
  rewrite (A.pts_to arr s1) as (A.pts_to (V.vec_to_array v) s1);
  V.to_vec_pts_to v;
  V.free v;
  ()
}

#pop-options
