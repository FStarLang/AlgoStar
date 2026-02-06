(*
   Min/Max Finding - Verified implementation in Pulse
   
   Implements linear-time algorithms to find minimum and maximum elements in an array.
   
   Proves:
   1. The returned value exists in the array
   2. The returned value is the minimum/maximum (universally bounded)
   
   NO admits. NO assumes.
*)

module CLRS.Ch09.MinMax
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

// ========== Minimum Finding ==========

fn find_minimum
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a #p s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    SZ.v len > 0 /\
    SZ.v len == A.length a
  )
  returns min_val: int
  ensures A.pts_to a #p s0 ** pure (
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == min_val) /\
    (forall (k:nat). k < Seq.length s0 ==> min_val <= Seq.index s0 k)
  )
{
  // Initialize min to first element
  let min_val = a.(0sz);
  let mut min: int = min_val;
  
  // Scan through array starting from index 1
  let mut i: SZ.t = 1sz;
  
  while (!i <^ len)
  invariant exists* vi vmin.
    R.pts_to i vi **
    R.pts_to min vmin **
    pure (
      SZ.v vi > 0 /\
      SZ.v vi <= SZ.v len /\
      // vmin exists in the array (at some position < vi)
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmin) /\
      // vmin is minimum of elements seen so far
      (forall (k:nat). k < SZ.v vi ==> vmin <= Seq.index s0 k)
    )
  {
    let vi = !i;
    let curr = a.(vi);
    let vmin = !min;
    
    if (curr < vmin) {
      min := curr;
    };
    
    i := vi + 1sz;
  };
  
  !min
}

// ========== Maximum Finding ==========

fn find_maximum
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a #p s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    SZ.v len > 0 /\
    SZ.v len == A.length a
  )
  returns max_val: int
  ensures A.pts_to a #p s0 ** pure (
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == max_val) /\
    (forall (k:nat). k < Seq.length s0 ==> max_val >= Seq.index s0 k)
  )
{
  // Initialize max to first element
  let max_val = a.(0sz);
  let mut max: int = max_val;
  
  // Scan through array starting from index 1
  let mut i: SZ.t = 1sz;
  
  while (!i <^ len)
  invariant exists* vi vmax.
    R.pts_to i vi **
    R.pts_to max vmax **
    pure (
      SZ.v vi > 0 /\
      SZ.v vi <= SZ.v len /\
      // vmax exists in the array (at some position < vi)
      (exists (k:nat). k < SZ.v vi /\ Seq.index s0 k == vmax) /\
      // vmax is maximum of elements seen so far
      (forall (k:nat). k < SZ.v vi ==> vmax >= Seq.index s0 k)
    )
  {
    let vi = !i;
    let curr = a.(vi);
    let vmax = !max;
    
    if (curr > vmax) {
      max := curr;
    };
    
    i := vi + 1sz;
  };
  
  !max
}
