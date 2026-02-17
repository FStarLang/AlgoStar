(*
   Binary Search - Verified Divide-and-Conquer Algorithm (CLRS Chapter 4)
   
   Proves: For a sorted array, binary_search returns an index where the key
           is found, or n if the key is not in the array.
   
   NO admits. NO assumes.
*)

module CLRS.Ch04.BinarySearch
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

//SNIPPET_START: is_sorted
// Predicate: array is sorted
let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j
//SNIPPET_END: is_sorted

// ========== Main Algorithm ==========

//SNIPPET_START: binary_search_sig
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
//SNIPPET_END: binary_search_sig
{
  let mut lo: SZ.t = 0sz;
  let mut hi: SZ.t = len;
  let mut found: bool = false;
  let mut result_idx: SZ.t = len;
  
  //SNIPPET_START: binary_search_loop
  // Main binary search loop - exit when found or range is empty
  while (!lo <^ !hi && not !found)
  invariant exists* vlo vhi vfound vresult.
    R.pts_to lo vlo **
    R.pts_to hi vhi **
    R.pts_to found vfound **
    R.pts_to result_idx vresult **
    A.pts_to a s0 **
    pure (
      // Include sorted property with SMT pattern
      (forall (i j: nat). {:pattern Seq.index s0 i; Seq.index s0 j}
        i < j /\ j < Seq.length s0 ==> Seq.index s0 i <= Seq.index s0 j) /\
      
      SZ.v vlo <= SZ.v vhi /\
      SZ.v vhi <= SZ.v len /\
      
      // If found, result is correct
      (vfound ==> (
        SZ.v vresult < SZ.v len /\
        SZ.v vresult < Seq.length s0 /\
        Seq.index s0 (SZ.v vresult) == key
      )) /\
      
      // If not found, result is len and key not in excluded regions
      (not vfound ==> (
        SZ.v vresult == SZ.v len /\
        (forall (i:nat). i < SZ.v vlo /\ i < Seq.length s0 ==> Seq.index s0 i =!= key) /\
        (forall (i:nat). i >= SZ.v vhi /\ i < Seq.length s0 ==> Seq.index s0 i =!= key) /\
        (forall (i:nat). i < Seq.length s0 /\ Seq.index s0 i == key ==> 
          SZ.v vlo <= i /\ i < SZ.v vhi)
      ))
    )
  //SNIPPET_END: binary_search_loop
  {
    let vlo = !lo;
    let vhi = !hi;
    
    // Calculate mid = lo + (hi - lo) / 2
    let diff : SZ.t = vhi -^ vlo;
    let half : SZ.t = diff /^ 2sz;
    let mid : SZ.t = vlo +^ half;
    
    // Read the middle element
    let mid_val : int = a.(mid);
    
    if (mid_val = key) {
      // Found! Set flag and result
      found := true;
      result_idx := mid;
      ()
    } else if (mid_val < key) {
      // key > mid_val, search upper half: [mid+1, hi)
      lo := mid +^ 1sz;
      ()
    } else {
      // key < mid_val, search lower half: [lo, mid)
      hi := mid;
      ()
    }
  };
  
  // After loop: either found=true or lo >= hi
  let vfound = !found;
  let vresult = !result_idx;
  let vlo = !lo;
  let vhi = !hi;
  
  // If not found and loop exited, then lo >= hi, so range [lo, hi) is empty
  // Combined with invariant: key not in [0, lo) and not in [hi, len)
  // Since lo >= hi, we have [0, len) = [0, lo) ∪ [lo, hi) ∪ [hi, len)
  //                                    = [0, lo) ∪ {} ∪ [hi, len)
  // So key not in entire array
  assert pure (vfound \/ SZ.v vlo >= SZ.v vhi);
  assert pure (not vfound ==> (
    SZ.v vlo >= SZ.v vhi /\
    (forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= key)
  ));
  
  vresult
}

