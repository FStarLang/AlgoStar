(*
   CLRS Chapter 4: Kadane's maximum-subarray algorithm as an instance
   of the shared divide-and-conquer complexity rubric.
*)

module CLRS.Ch04.MaxSubarray.Kadane.Rubric
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open CLRS.Common.Complexity.DivideConquer.Class

module A = Pulse.Lib.Array
module DC = CLRS.Common.Complexity.DivideConquer.Class
module MR = Pulse.Lib.MonotonicGhostRef
module O = FStar.Order
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TO = Pulse.Lib.TotalOrder

fn max_subarray_poly
  (a: Type0)
  (#p: perm)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: DC.ticks_t)
  (#ops: erased (DC.ordered_monoid a))
  (zero: a)
  (iadd: DC.instrumented_binary_op a ops.om_add ctr)
  (icmp: DC.instrumented_total_order a ops.om_ord ctr)
  (#s0: Ghost.erased (Seq.seq a))
  (#c0: erased nat)
  preserves A.pts_to arr #p s0
  requires MR.pts_to ctr #1.0R c0 **
    pure (
      zero == ops.om_zero /\
      SZ.v len == Seq.length s0 /\
      Seq.length s0 <= A.length arr /\
      SZ.v len > 0
    )
  returns result: a
  ensures exists* (cf: nat). MR.pts_to ctr #1.0R cf ** pure (
    result == DC.max_subarray_spec ops s0 /\
    cf <= reveal c0 + DC.max_subarray_bound (Seq.length s0)
  )
{
  let first_elem = arr.(0sz);
  let mut current_sum: a = zero;
  let mut best_sum: a = first_elem;
  let mut i: SZ.t = 0sz;

  while (!i <^ len)
  invariant exists* vi vcur vbest (vc : nat).
    R.pts_to i vi **
    R.pts_to current_sum vcur **
    R.pts_to best_sum vbest **
    MR.pts_to ctr #1.0R vc **
    A.pts_to arr #p s0 **
    pure (
      zero == ops.om_zero /\
      SZ.v vi <= SZ.v len /\
      DC.kadane_spec ops s0 (SZ.v vi) vcur vbest ==
        DC.kadane_spec ops s0 0 ops.om_zero (Seq.index (reveal s0) 0) /\
      vc == reveal c0 + 3 * SZ.v vi
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !i)
  {
    let vi = !i;
    let vcur = !current_sum;
    let vbest = !best_sum;

    let elem = arr.(vi);

    let sum_with_current = iadd vcur elem;
    let current_cmp = icmp sum_with_current elem;
    let mut new_current : a = elem;
    if (O.gt current_cmp) {
      new_current := sum_with_current;
    };
    let vnew_current = !new_current;

    let best_cmp = icmp vnew_current vbest;
    let mut new_best : a = vbest;
    if (O.gt best_cmp) {
      new_best := vnew_current;
    };
    let vnew_best = !new_best;

    current_sum := vnew_current;
    best_sum := vnew_best;
    i := vi +^ 1sz;
  };

  !best_sum
}

instance kadane_array_max_subarray : DC.array_max_subarray DC.max_subarray_bound =
  Pulse.Lib.Core.slprop_equivs ();
  {
    max_subarray = max_subarray_poly
  }
