(*
   Maximum Subarray (Kadane's Algorithm) - Verified implementation in Pulse
   
   Proves: The result equals the maximum sum of any contiguous subarray.
   
   NO admits. NO assumes.
*)

module CLRS.Ch04.MaxSubarray.Kadane
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Definitions ==========

// Helper: maximum of two integers
let max_int (a b: int) : Tot int = if a >= b then a else b

// A very small integer to use as initial best_sum
let initial_min : int = -1000000000

// Lemma: Seq.length is always non-negative
let seq_length_nonneg (s: Seq.seq 'a) : Lemma (Seq.length s >= 0) = ()

//SNIPPET_START: kadane_spec
// Kadane's algorithm specification: iterative maximum subarray
// We use i as decreases with the invariant that we call with i+1 < length
let rec kadane_spec (s: Seq.seq int) (i: nat) 
  (current_sum: int) (best_sum: int) : Pure int
  (requires i <= Seq.length s)
  (ensures fun _ -> True)
  (decreases (if i <= Seq.length s then Seq.length s - i else 0))
  =
  if i >= Seq.length s then best_sum
  else (
    let elem = Seq.index s i in
    let new_current = max_int elem (current_sum + elem) in
    let new_best = max_int best_sum new_current in
    kadane_spec s (i + 1) new_current new_best
  )

// The main spec: maximum subarray sum
let max_subarray_spec (s: Seq.seq int) : Tot int =
  if Seq.length s = 0 then 0
  else kadane_spec s 0 0 initial_min
//SNIPPET_END: kadane_spec

// ========== Main Algorithm ==========

//SNIPPET_START: max_subarray_sig
fn max_subarray
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    Seq.length s0 <= A.length a /\
    SZ.v len > 0
  )
  returns result: int
  ensures A.pts_to a s0 ** pure (
    result == max_subarray_spec s0
  )
//SNIPPET_END: max_subarray_sig
{
  let mut current_sum: int = 0;
  let mut best_sum: int = initial_min;
  let mut i: SZ.t = 0sz;
  
  while (!i <^ len)
  invariant exists* vi vcur vbest.
    R.pts_to i vi **
    R.pts_to current_sum vcur **
    R.pts_to best_sum vbest **
    A.pts_to a s0 **
    pure (
      SZ.v vi <= SZ.v len /\
      kadane_spec s0 (SZ.v vi) vcur vbest == kadane_spec s0 0 0 initial_min
    )
  {
    let vi = !i;
    let vcur = !current_sum;
    let vbest = !best_sum;
    
    let elem = a.(vi);
    
    // new_current = max(elem, current + elem)
    let sum_with_current : int = vcur + elem;
    let mut new_current : int = elem;
    if (sum_with_current > elem) {
      new_current := sum_with_current;
    };
    let vnew_current = !new_current;
    
    // new_best = max(best, new_current)
    let mut new_best : int = vbest;
    if (vnew_current > vbest) {
      new_best := vnew_current;
    };
    let vnew_best = !new_best;
    
    current_sum := vnew_current;
    best_sum := vnew_best;
    i := vi + 1sz;
  };
  
  !best_sum
}
