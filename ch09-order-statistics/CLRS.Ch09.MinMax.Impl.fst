(*
   CLRS Chapter 9.1: MINIMUM / MAXIMUM — Verified Pulse Implementation

   Implements linear-time algorithms to find minimum and maximum elements in an array.

   Proves:
   1. The returned value exists in the array
   2. The returned value is the minimum/maximum (universally bounded)
   3. Exactly (n - 1) comparisons for an array of length n — Θ(n)

   NO admits. NO assumes.
*)
module CLRS.Ch09.MinMax.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open CLRS.Ch09.MinMax.Spec
open CLRS.Ch09.MinMax.Complexity

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Minimum Finding ==========

//SNIPPET_START: find_minimum
fn find_minimum
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len > 0 /\
      SZ.v len == A.length a
    )
  returns min_val: int
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> min_val <= Seq.index s0 k) /\
      complexity_bounded_min cf (reveal c0) (SZ.v len)
    )
//SNIPPET_END: find_minimum
{
  let min_val = a.(0sz);
  let mut min: int = min_val;
  let mut i: SZ.t = 1sz;
  
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
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi - 1
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !i)
  {
    let vi = !i;
    let curr = a.(vi);
    let vmin = !min;
    
    tick ctr;
    
    if (curr < vmin) {
      min := curr
    };
    
    i := vi + 1sz
  };
  
  !min
}

// ========== Maximum Finding ==========

//SNIPPET_START: find_maximum
fn find_maximum
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len > 0 /\
      SZ.v len == A.length a
    )
  returns max_val: int
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> max_val >= Seq.index s0 k) /\
      complexity_bounded_max cf (reveal c0) (SZ.v len)
    )
//SNIPPET_END: find_maximum
{
  let max_val = a.(0sz);
  let mut max: int = max_val;
  let mut i: SZ.t = 1sz;
  
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
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi - 1
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !i)
  {
    let vi = !i;
    let curr = a.(vi);
    let vmax = !max;
    
    tick ctr;
    
    if (curr > vmax) {
      max := curr
    };
    
    i := vi + 1sz
  };
  
  !max
}
