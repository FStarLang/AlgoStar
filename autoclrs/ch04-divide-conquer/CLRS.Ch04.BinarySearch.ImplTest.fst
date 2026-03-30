(*
   Spec validation test for Binary Search (CLRS §2.3, Exercise 2.3-5)

   Tests the CLRS.Ch04.BinarySearch.Impl.fsti API on concrete instances:
   - Found case:     search for 3 in [1; 3; 5] → proves result == 1
   - Not found case: search for 2 in [1; 3; 5] → proves result == 3 (sentinel)
   - Empty array:    search for 1 in []         → proves result == 0 (sentinel)

   Also verifies the complexity bound: at most ⌊log₂ n⌋ + 1 comparisons.

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        Ghost assertions prove the postcondition uniquely determines the result.
     2. RUNTIME (computational, survives extraction to C):
        sz_eq comparisons produce a bool that is checked by the C test driver.

   Validates:
   - Precondition (is_sorted) is satisfiable on concrete sorted input
   - Postcondition uniquely determines the output for concrete inputs
   - Complexity bound is verifiable (transparent via Spec.fst)
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

(* SZ.t equality check — computational, survives extraction to C *)
inline_for_extraction
let sz_eq (a b: SZ.t) : (r:bool{r <==> SZ.v a = SZ.v b}) =
  let open FStar.SizeT in not (a <^ b || b <^ a)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"

// Test 1: Found case — search for 3 in sorted array [1; 3; 5]
// Expected: result == 1 (the index where 3 resides)
fn test_binary_search_found ()
  requires emp
  returns r: bool
  ensures pure (r == true)
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

  // PROOF: ghost assertion proves result is uniquely determined
  assert (pure (SZ.v result == 1));

  // Complexity: at most log2f(3) + 1 = 2 comparisons
  with cf. assert (GR.pts_to ctr cf);
  assert (pure (cf <= 2));

  // RUNTIME: computational check (survives extraction to C)
  let ok = sz_eq result 1sz;

  // Cleanup
  GR.free ctr;
  with s1. assert (A.pts_to arr s1);
  rewrite (A.pts_to arr s1) as (A.pts_to (V.vec_to_array v) s1);
  V.to_vec_pts_to v;
  V.free v;
  ok
}

// Test 2: Not found case — search for 2 in sorted array [1; 3; 5]
// Expected: result == 3 (sentinel value = len, meaning not found)
fn test_binary_search_not_found ()
  requires emp
  returns r: bool
  ensures pure (r == true)
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

  // PROOF: ghost assertion proves result is uniquely determined (not found sentinel)
  assert (pure (SZ.v result == SZ.v 3sz));

  // Complexity: at most log2f(3) + 1 = 2 comparisons
  with cf. assert (GR.pts_to ctr cf);
  assert (pure (cf <= 2));

  // RUNTIME: computational check (survives extraction to C)
  let ok = sz_eq result 3sz;

  // Cleanup
  GR.free ctr;
  with s1. assert (A.pts_to arr s1);
  rewrite (A.pts_to arr s1) as (A.pts_to (V.vec_to_array v) s1);
  V.to_vec_pts_to v;
  V.free v;
  ok
}

// Test 3: Empty array — search for 1 in [] (len=0)
// Expected: result == 0 (sentinel = len, not found)
fn test_binary_search_empty ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let v = V.alloc 0 0sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 0 0))
       as (A.pts_to arr (Seq.create 0 0));
  A.pts_to_len arr;

  let ctr = GR.alloc #nat 0;
  let result = binary_search arr 0sz 1 ctr;

  // PROOF: ghost assertion proves result == 0 (sentinel for empty array)
  assert (pure (SZ.v result == 0));

  // Complexity: at most log2f(0) + 1 = 1 comparison
  with cf. assert (GR.pts_to ctr cf);
  assert (pure (cf <= 1));

  // RUNTIME: computational check (survives extraction to C)
  let ok = sz_eq result 0sz;

  // Cleanup
  GR.free ctr;
  with s1. assert (A.pts_to arr s1);
  rewrite (A.pts_to arr s1) as (A.pts_to (V.vec_to_array v) s1);
  V.to_vec_pts_to v;
  V.free v;
  ok
}

#pop-options
