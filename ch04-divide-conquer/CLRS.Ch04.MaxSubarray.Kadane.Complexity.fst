(*
   Maximum Subarray (Kadane's) with Complexity Bound

   Proves O(n) comparison complexity for the maximum subarray algorithm.
   Specifically: exactly n iterations (one per element).

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each element processed gets one ghost tick.

   Also proves functional correctness (result == max_subarray_spec s0).

   NO admits. NO assumes.
*)

module CLRS.Ch04.MaxSubarray.Kadane.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Definitions (same as MaxSubarray.fst) ==========

let max_int (a b: int) : Tot int = if a >= b then a else b

let initial_min : int = -1000000000

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

let max_subarray_spec (s: Seq.seq int) : Tot int =
  if Seq.length s = 0 then 0
  else kadane_spec s 0 0 initial_min

// ========== Complexity bound predicate ==========
// (Avoids BoundedIntegers elaboration issues in Pulse ensures)
let complexity_bounded_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n

// ========== Main Algorithm with Complexity ==========

fn max_subarray_complexity
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
    // Complexity: exactly n operations = Θ(n)
    complexity_bounded_linear cf (reveal c0) (SZ.v len)
  )
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

    // Count the operation — one ghost tick
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

  // At loop exit: i == len, so ctr == c0 + len = Θ(n) operations
  !best_sum
}
