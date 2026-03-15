(*
   CLRS Chapter 9.1: Simultaneous Min and Max — Verified Pulse Implementation

   Two implementations, each with inline ghost ticks:
   1. Simple linear scan: 2(n-1) comparisons
   2. CLRS Section 9.1 pair-processing: ⌊3n/2⌋ comparisons

   NO admits. NO assumes.
*)
module CLRS.Ch09.SimultaneousMinMax.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open CLRS.Ch09.SimultaneousMinMax.Spec
open CLRS.Common.Complexity

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Simple linear scan — 2(n-1) comparisons ==========

//SNIPPET_START: find_minmax
fn find_minmax
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len >= 1 /\
      SZ.v len == A.length a
    )
  returns result: minmax_result
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
      complexity_bounded_minmax cf (reveal c0) (SZ.v len)
    )
//SNIPPET_END: find_minmax
{
  let v0 = a.(0sz);
  let mut min: int = v0;
  let mut max: int = v0;
  let mut i: SZ.t = 1sz;
  
  while (!i <^ len)
  invariant exists* vi vmin vmax (vc: nat).
    R.pts_to i vi **
    R.pts_to min vmin **
    R.pts_to max vmax **
    GR.pts_to ctr vc **
    A.pts_to a #p s0 **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v len /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmin) /\
      (forall (k:nat). k < SZ.v vi ==> vmin <= Seq.index s0 k) /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmax) /\
      (forall (k:nat). k < SZ.v vi ==> vmax >= Seq.index s0 k) /\
      vc >= reveal c0 /\
      vc - reveal c0 == op_Multiply 2 (SZ.v vi - 1)
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !i)
  {
    let vi = !i;
    let elem = a.(vi);
    let vmin = !min;
    let vmax = !max;
    
    tick ctr;
    if (elem < vmin) {
      min := elem;
    };
    
    tick ctr;
    if (elem > vmax) {
      max := elem;
    };
    
    i := vi + 1sz;
  };
  
  let final_min = !min;
  let final_max = !max;
  
  { min_val = final_min; max_val = final_max }
}

// ========== CLRS pair-processing — ⌊3n/2⌋ comparisons ==========

#push-options "--z3rlimit 500 --ifuel 3 --fuel 3"
//SNIPPET_START: find_minmax_pairs
fn find_minmax_pairs
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len >= 1 /\
      SZ.v len == A.length a
    )
  returns result: minmax_result
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
      complexity_bounded_minmax_pairs cf (reveal c0) (SZ.v len)
    )
//SNIPPET_END: find_minmax_pairs
{
  let v0 = a.(0sz);
  let mut min_ref: int = v0;
  let mut max_ref: int = v0;
  let mut i: SZ.t = 1sz;

  if (len >=^ 2sz) {
    let v1 = a.(1sz);
    tick ctr;
    if (v0 <= v1) {
      max_ref := v1;
    } else {
      min_ref := v1;
    };
    i := 2sz;
  };

  let len_m1 = len -^ 1sz;
  while (
    let vi = !i;
    vi <^ len_m1
  )
  invariant exists* vi vmin vmax (vc: nat).
    R.pts_to i vi **
    R.pts_to min_ref vmin **
    R.pts_to max_ref vmax **
    GR.pts_to ctr vc **
    A.pts_to a #p s0 **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v len /\
      (SZ.v vi == 1 ==> SZ.v len == 1) /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmin) /\
      (forall (k:nat). k < SZ.v vi ==> vmin <= Seq.index s0 k) /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmax) /\
      (forall (k:nat). k < SZ.v vi ==> vmax >= Seq.index s0 k) /\
      vc >= reveal c0 /\
      op_Multiply 2 (vc - reveal c0) <= op_Multiply 3 (SZ.v vi) - 2 /\
      (SZ.v vi >= 2 ==> op_Multiply 2 (vc - reveal c0) + 4 <= op_Multiply 3 (SZ.v vi))
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !i)
  {
    let vi = !i;
    let a_i = a.(vi);
    let a_next = a.(vi +^ 1sz);
    let vmin = !min_ref;
    let vmax = !max_ref;

    // 3 comparisons per pair
    tick ctr; tick ctr; tick ctr;
    if (a_i <= a_next) {
      if (a_i < vmin) { min_ref := a_i; };
      if (a_next > vmax) { max_ref := a_next; };
    } else {
      if (a_next < vmin) { min_ref := a_next; };
      if (a_i > vmax) { max_ref := a_i; };
    };

    i := vi +^ 2sz;
  };

  // Handle odd trailing element
  let vi = !i;
  if (vi <^ len) {
    let last = a.(vi);
    let vmin = !min_ref;
    let vmax = !max_ref;
    tick ctr; tick ctr;
    if (last < vmin) { min_ref := last; };
    if (last > vmax) { max_ref := last; };
  };

  let final_min = !min_ref;
  let final_max = !max_ref;
  { min_val = final_min; max_val = final_max }
}
#pop-options
