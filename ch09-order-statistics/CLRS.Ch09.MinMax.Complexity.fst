(*
   Min/Max Finding with Complexity Bounds

   Proves O(n) comparison complexity for find_minimum and find_maximum.
   Specifically: exactly (n - 1) comparisons for an array of length n.

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   A ghost `tick` function increments the counter by 1 for each comparison.

   NO admits. NO assumes.
*)

module CLRS.Ch09.MinMax.Complexity
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

// ========== Ghost tick: increment counter by 1 ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Minimum Finding with Complexity Bound ==========

// Proves: exactly (len - 1) comparisons, i.e., Θ(n)
fn find_minimum_complexity
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a #p s0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len > 0 /\
      SZ.v len == A.length a
    )
  returns min_val: int
  ensures A.pts_to a #p s0 **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> min_val <= Seq.index s0 k)
    )
{
  let min_val = a.(0sz);
  let mut min: int = min_val;
  let mut i: SZ.t = 1sz;
  let ctr = GR.alloc #nat 0;
  
  while (!i <^ len)
  invariant exists* vi vmin (vc : nat).
    R.pts_to i vi **
    R.pts_to min vmin **
    GR.pts_to ctr vc **
    A.pts_to a #p s0 **
    pure (
      SZ.v vi > 0 /\
      SZ.v vi <= SZ.v len /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmin) /\
      (forall (k:nat). k < SZ.v vi ==> vmin <= Seq.index s0 k) /\
      vc == SZ.v vi - 1
    )
  {
    let vi = !i;
    let curr = a.(vi);
    let vmin = !min;
    
    // Count the comparison — one ghost tick
    tick ctr;
    
    if (curr < vmin) {
      min := curr
    };
    
    i := vi + 1sz
  };
  
  // At loop exit: i == len, so ctr == len - 1.
  // This proves exactly (n-1) comparisons were performed.
  let final_ctr = GR.op_Bang ctr;
  assert (pure (reveal final_ctr == SZ.v len - 1));
  
  GR.free ctr;
  !min
}

// ========== Maximum Finding with Complexity Bound ==========

// Proves: exactly (len - 1) comparisons, i.e., Θ(n)
fn find_maximum_complexity
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a #p s0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len > 0 /\
      SZ.v len == A.length a
    )
  returns max_val: int
  ensures A.pts_to a #p s0 **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> max_val >= Seq.index s0 k)
    )
{
  let max_val = a.(0sz);
  let mut max: int = max_val;
  let mut i: SZ.t = 1sz;
  let ctr = GR.alloc #nat 0;
  
  while (!i <^ len)
  invariant exists* vi vmax (vc : nat).
    R.pts_to i vi **
    R.pts_to max vmax **
    GR.pts_to ctr vc **
    A.pts_to a #p s0 **
    pure (
      SZ.v vi > 0 /\
      SZ.v vi <= SZ.v len /\
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmax) /\
      (forall (k:nat). k < SZ.v vi ==> vmax >= Seq.index s0 k) /\
      vc == SZ.v vi - 1
    )
  {
    let vi = !i;
    let curr = a.(vi);
    let vmax = !max;
    
    // Count the comparison — one ghost tick
    tick ctr;
    
    if (curr > vmax) {
      max := curr
    };
    
    i := vi + 1sz
  };
  
  let final_ctr = GR.op_Bang ctr;
  assert (pure (reveal final_ctr == SZ.v len - 1));
  
  GR.free ctr;
  !max
}
