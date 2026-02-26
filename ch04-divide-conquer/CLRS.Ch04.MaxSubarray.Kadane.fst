(*
   Maximum Subarray (Kadane's Algorithm) - Verified implementation in Pulse
   
   Proves:
   1. The result equals the maximum sum of any contiguous subarray.
   2. O(n) complexity: exactly n operations.

   Uses GhostReference.ref nat for the tick counter -- fully erased at runtime.

   NO admits. NO assumes.
*)

module CLRS.Ch04.MaxSubarray.Kadane
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open CLRS.Ch04.MaxSubarray.Spec

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = CLRS.Ch04.MaxSubarray.Spec

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Complexity bound predicate ==========

let complexity_bounded_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n

// ========== Main Algorithm with Complexity ==========

//SNIPPET_START: max_subarray_sig
fn max_subarray
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0
  requires pure (
    SZ.v len == Seq.length s0 /\
    Seq.length s0 <= A.length a /\
    SZ.v len > 0
  )
  returns result: int
  ensures exists* (cf: nat). A.pts_to a s0 ** GR.pts_to ctr cf ** pure (
    result == max_subarray_spec s0 /\
    complexity_bounded_linear cf (reveal c0) (SZ.v len)
  )
//SNIPPET_END: max_subarray_sig
{
  let mut current_sum: int = 0;
  let mut best_sum: int = initial_min;
  let mut i: SZ.t = 0sz;

  while (!i <^ len)
  invariant exists* vi vcur vbest (vc : nat).
    R.pts_to i vi **
    R.pts_to current_sum vcur **
    R.pts_to best_sum vbest **
    GR.pts_to ctr vc **
    A.pts_to a s0 **
    pure (
      SZ.v vi <= SZ.v len /\
      kadane_spec s0 (SZ.v vi) vcur vbest == kadane_spec s0 0 0 initial_min /\
      // Complexity: exactly i ticks so far (relative to c0)
      vc == reveal c0 + SZ.v vi
    )
  {
    let vi = !i;
    let vcur = !current_sum;
    let vbest = !best_sum;

    let elem = a.(vi);

    // Count the operation
    tick ctr;

    let sum_with_current : int = vcur + elem;
    let mut new_current : int = elem;
    if (sum_with_current > elem) {
      new_current := sum_with_current;
    };
    let vnew_current = !new_current;

    let mut new_best : int = vbest;
    if (vnew_current > vbest) {
      new_best := vnew_current;
    };
    let vnew_best = !new_best;

    current_sum := vnew_current;
    best_sum := vnew_best;
    i := vi + 1sz;
  };

  // At loop exit: i == len, so ctr == c0 + len = Theta(n) operations
  !best_sum
}
