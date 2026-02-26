(*
   Binary Search - Corrected Implementation with Early Exit Pattern
   
   Demonstrates: How to handle "early return" in Pulse while loops
   - Use mutable "found" flag
   - Use mutable "result" reference
   - Loop invariant tracks: if found, result is valid
   
   NO admits. NO assumes.
*)

module CLRS.Ch04.BinarySearch.Corrected
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Definitions ==========

// Predicate: array is sorted
let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

// Helper lemma: In a sorted array, if s[mid] < key, then no element at index <= mid equals key
let sorted_left_exclude (s: Seq.seq int) (mid: nat) (key: int) : Lemma
  (requires is_sorted s /\ mid < Seq.length s /\ Seq.index s mid < key)
  (ensures forall (j: nat). j <= mid /\ j < Seq.length s ==> Seq.index s j =!= key)
= 
  assert (forall (j: nat). j <= mid /\ j < Seq.length s ==> Seq.index s j <= Seq.index s mid)

// Helper lemma: In a sorted array, if s[mid] > key, then no element at index >= mid equals key  
let sorted_right_exclude (s: Seq.seq int) (mid: nat) (key: int) : Lemma
  (requires is_sorted s /\ mid < Seq.length s /\ Seq.index s mid > key)
  (ensures forall (j: nat). j >= mid /\ j < Seq.length s ==> Seq.index s j =!= key)
=
  assert (forall (j: nat). j >= mid /\ j < Seq.length s ==> Seq.index s mid <= Seq.index s j)

open Pulse.Lib.BoundedIntegers

// ========== Pattern 1: Linear Search with Early Exit ==========

fn linear_search_with_early_exit
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (key: int)
  requires A.pts_to a s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    Seq.length s0 <= A.length a /\
    SZ.v len > 0
  )
  returns result: SZ.t
  ensures A.pts_to a s0 ** pure (
    SZ.v result <= SZ.v len /\
    (SZ.v result < SZ.v len ==> (
      SZ.v result < Seq.length s0 /\
      Seq.index s0 (SZ.v result) == key
    )) /\
    (SZ.v result == SZ.v len ==> (
      forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= key
    ))
  )
{
  // State variables for early exit pattern
  let mut i: SZ.t = 0sz;
  let mut found: bool = false;
  let mut result: SZ.t = len;  // Default: not found
  
  while (!i <^ len && not !found)
  invariant exists* vi vfound vresult.
    R.pts_to i vi **
    R.pts_to found vfound **
    R.pts_to result vresult **
    A.pts_to a s0 **
    pure (
      SZ.v vi <= SZ.v len /\
      SZ.v vresult <= SZ.v len /\
      // If found, result is valid
      (vfound ==> (
        SZ.v vresult < SZ.v len /\
        SZ.v vresult < Seq.length s0 /\
        Seq.index s0 (SZ.v vresult) == key
      )) /\
      // If not found yet, we haven't seen key in [0, vi)
      (not vfound ==> (
        SZ.v vresult == SZ.v len /\
        (forall (j:nat). j < SZ.v vi /\ j < Seq.length s0 ==> Seq.index s0 j =!= key)
      ))
    )
  {
    let vi = !i;
    let elem = a.(vi);
    
    if (elem = key) {
      // Found it! Set flag and result
      found := true;
      result := vi;
      ()
    } else {
      // Keep searching
      i := vi +^ 1sz;
      ()
    }
  };
  
  !result
}

// ========== Pattern 2: True Binary Search with Early Exit ==========

fn binary_search
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (key: int)
  requires A.pts_to a s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    Seq.length s0 <= A.length a /\
    SZ.v len > 0 /\
    is_sorted s0
  )
  returns result: SZ.t
  ensures A.pts_to a s0 ** pure (
    SZ.v result <= SZ.v len /\
    (SZ.v result < SZ.v len ==> (
      SZ.v result < Seq.length s0 /\
      Seq.index s0 (SZ.v result) == key
    )) /\
    (SZ.v result == SZ.v len ==> (
      forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= key
    ))
  )
{
  // State variables for binary search with early exit
  let mut left: SZ.t = 0sz;
  let mut right: SZ.t = len;
  let mut found: bool = false;
  let mut result: SZ.t = len;  // Default: not found
  
  while (!left <^ !right && not !found)
  invariant exists* vleft vright vfound vresult.
    R.pts_to left vleft **
    R.pts_to right vright **
    R.pts_to found vfound **
    R.pts_to result vresult **
    A.pts_to a s0 **
    pure (
      SZ.v vleft <= SZ.v vright /\
      SZ.v vright <= SZ.v len /\
      SZ.v vresult <= SZ.v len /\
      // If found, result is valid
      (vfound ==> (
        SZ.v vresult < SZ.v len /\
        SZ.v vresult < Seq.length s0 /\
        Seq.index s0 (SZ.v vresult) == key
      )) /\
      // If not found yet, key (if exists) must be in [vleft, vright)
      (not vfound ==> (
        SZ.v vresult == SZ.v len /\
        (forall (j:nat). 
          (j < SZ.v vleft \/ j >= SZ.v vright) /\ j < Seq.length s0 
          ==> Seq.index s0 j =!= key)
      ))
    )
  {
    let vleft = !left;
    let vright = !right;
    
    // Compute mid = left + (right - left) / 2
    let diff = vright -^ vleft;
    let half = diff /^ 2sz;
    let mid = vleft +^ half;
    
    let elem = a.(mid);
    
    if (elem = key) {
      // Found it!
      found := true;
      result := mid;
      ()
    } else if (elem < key) {
      // Go right: search in [mid+1, right)
      sorted_left_exclude s0 (SZ.v mid) key;
      left := mid +^ 1sz;
      ()
    } else {
      // Go left: search in [left, mid)
      sorted_right_exclude s0 (SZ.v mid) key;
      right := mid;
      ()
    }
  };
  
  !result
}

// ========== Pattern 3: Binary Search Returning Option Type ==========
// Alternative: Return Option instead of sentinel value

fn binary_search_option
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (key: int)
  requires A.pts_to a s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    Seq.length s0 <= A.length a /\
    SZ.v len > 0 /\
    is_sorted s0
  )
  returns result: option SZ.t
  ensures A.pts_to a s0 ** pure (
    match result with
    | Some idx -> 
        SZ.v idx < SZ.v len /\
        SZ.v idx < Seq.length s0 /\
        Seq.index s0 (SZ.v idx) == key
    | None ->
        (forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= key)
  )
{
  // State variables
  let mut left: SZ.t = 0sz;
  let mut right: SZ.t = len;
  let mut found: bool = false;
  let mut result: SZ.t = 0sz;  // Will be valid if found=true
  
  while (!left <^ !right && not !found)
  invariant exists* vleft vright vfound vresult.
    R.pts_to left vleft **
    R.pts_to right vright **
    R.pts_to found vfound **
    R.pts_to result vresult **
    A.pts_to a s0 **
    pure (
      SZ.v vleft <= SZ.v vright /\
      SZ.v vright <= SZ.v len /\
      // If found, result is valid
      (vfound ==> (
        SZ.v vresult < SZ.v len /\
        SZ.v vresult < Seq.length s0 /\
        Seq.index s0 (SZ.v vresult) == key
      )) /\
      // If not found yet, key (if exists) must be in [vleft, vright)
      (not vfound ==> (
        (forall (j:nat). 
          (j < SZ.v vleft \/ j >= SZ.v vright) /\ j < Seq.length s0 
          ==> Seq.index s0 j =!= key)
      ))
    )
  {
    let vleft = !left;
    let vright = !right;
    
    let diff = vright -^ vleft;
    let half = diff /^ 2sz;
    let mid = vleft +^ half;
    
    let elem = a.(mid);
    
    if (elem = key) {
      found := true;
      result := mid;
      ()
    } else if (elem < key) {
      sorted_left_exclude s0 (SZ.v mid) key;
      left := mid +^ 1sz;
      ()
    } else {
      sorted_right_exclude s0 (SZ.v mid) key;
      right := mid;
      ()
    }
  };
  
  let vfound = !found;
  let vresult = !result;
  
  if (vfound) {
    Some vresult
  } else {
    None
  }
}
