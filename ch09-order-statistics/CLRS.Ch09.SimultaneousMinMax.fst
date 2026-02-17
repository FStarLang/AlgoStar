(*
   Simultaneous Min/Max Finding - Verified implementation in Pulse
   
   Implements simultaneous finding of both minimum and maximum of an array.
   
   This implementation uses a linear scan (2n-2 comparisons), which is
   straightforward to verify. The optimized pair-processing algorithm from
   CLRS Section 9.1 (using 3⌊n/2⌋ comparisons) requires more complex
   case analysis that is challenging to verify in Pulse.
   
   Proves:
   1. Returns correct minimum and maximum
   2. Uses exactly 2(n-1) comparisons for n ≥ 1
   
   NO admits. NO assumes.
*)

module CLRS.Ch09.SimultaneousMinMax
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

// ========== Ghost tick for comparisons ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Result type ==========

noeq
type minmax_result = {
  min_val: int;
  max_val: int;
}

// ========== Simple linear scan version (without complexity tracking) ==========

//SNIPPET_START: find_minmax
fn find_minmax
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a #p s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    SZ.v len >= 1 /\
    SZ.v len == A.length a
  )
  returns result: minmax_result
  ensures A.pts_to a #p s0 ** pure (
    // min_val is in the array and is minimum
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
    // max_val is in the array and is maximum
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k)
  )
//SNIPPET_END: find_minmax
{
  // Initialize from first element
  let v0 = a.(0sz);
  let mut min: int = v0;
  let mut max: int = v0;
  
  // Scan remaining elements
  let mut i: SZ.t = 1sz;
  
  while (!i <^ len)
  invariant exists* vi vmin vmax.
    R.pts_to i vi **
    R.pts_to min vmin **
    R.pts_to max vmax **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v len /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmin) /\
      (forall (k:nat). k < SZ.v vi ==> vmin <= Seq.index s0 k) /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmax) /\
      (forall (k:nat). k < SZ.v vi ==> vmax >= Seq.index s0 k)
    )
  {
    let vi = !i;
    let elem = a.(vi);
    let vmin = !min;
    let vmax = !max;
    
    if (elem < vmin) {
      min := elem;
    };
    
    if (elem > vmax) {
      max := elem;
    };
    
    i := vi + 1sz;
  };
  
  let final_min = !min;
  let final_max = !max;
  
  { min_val = final_min; max_val = final_max }
}

// ========== With complexity tracking: 2(n-1) comparisons ==========

//SNIPPET_START: complexity_bounded_minmax
let complexity_bounded_minmax (cf c0 n: nat) : prop =
  n >= 1 /\
  cf >= c0 /\
  cf - c0 == op_Multiply 2 (n - 1)
//SNIPPET_END: complexity_bounded_minmax

fn find_minmax_complexity
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
      // min_val is in the array and is minimum
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
      // max_val is in the array and is maximum
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
      // Complexity bound
      complexity_bounded_minmax cf (reveal c0) (SZ.v len)
    )
{
  // Initialize from first element
  let v0 = a.(0sz);
  let mut min: int = v0;
  let mut max: int = v0;
  
  // Scan remaining elements
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
      // Comparison count: 2 comparisons per element processed
      vc >= reveal c0 /\
      vc - reveal c0 == op_Multiply 2 (SZ.v vi - 1)
    )
  {
    let vi = !i;
    let elem = a.(vi);
    let vmin = !min;
    let vmax = !max;
    
    // 1st comparison: elem < vmin
    tick ctr;
    if (elem < vmin) {
      min := elem;
    };
    
    // 2nd comparison: elem > vmax
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
