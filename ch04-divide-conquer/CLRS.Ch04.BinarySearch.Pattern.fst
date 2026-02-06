(*
   Binary Search - Early Exit Pattern for Pulse
   
   This shows the CORRECT patterns for implementing binary search in Pulse
   where you need "early exit" semantics (returning when key is found).
   
   Key Pattern: Use state variables (found flag + result reference)
   Loop body MUST return (), but state tracks the result.
   
   NO admits. NO assumes.
*)

module CLRS.Ch04.BinarySearch.Pattern
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

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

// ========== Pattern 1: Linear Search (Simpler Example) ==========

fn linear_search
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
      Seq.index s0 (SZ.v result) == key /\
      (forall (j:nat). j < SZ.v result ==> Seq.index s0 j =!= key)  // First occurrence
    )) /\
    (SZ.v result == SZ.v len ==> (
      forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= key
    ))
  )
{
  // KEY PATTERN: Use mutable state variables
  let mut i: SZ.t = 0sz;
  let mut found: bool = false;
  let mut result: SZ.t = len;  // Default: not found (sentinel value)
  
  // Loop condition checks BOTH bounds and found flag
  while (!i <^ len && not !found)
  invariant exists* vi vfound vresult.
    R.pts_to i vi **
    R.pts_to found vfound **
    R.pts_to result vresult **
    A.pts_to a s0 **
    pure (
      SZ.v vi <= SZ.v len /\
      SZ.v vresult <= SZ.v len /\
      // CRITICAL: Relate found flag to result validity
      (vfound ==> (
        SZ.v vresult < SZ.v len /\
        SZ.v vresult < Seq.length s0 /\
        Seq.index s0 (SZ.v vresult) == key /\
        (forall (j:nat). j < SZ.v vresult ==> Seq.index s0 j =!= key)
      )) /\
      (not vfound ==> (
        SZ.v vresult == SZ.v len /\
        (forall (j:nat). j < SZ.v vi /\ j < Seq.length s0 ==> Seq.index s0 j =!= key)
      ))
    )
  {
    let vi = !i;
    let elem = a.(vi);
    
    if (elem = key) {
      // Found it! Update state variables
      found := true;
      result := vi;
      // MUST return () from loop body
      ()
    } else {
      // Keep searching
      i := vi +^ 1sz;
      ()
    }
  };
  
  // Return the result after loop
  !result
}

// ========== Pattern 2: Binary Search (Returns Index or Len) ==========

fn binary_search_with_sentinel
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
  let mut left: SZ.t = 0sz;
  let mut right: SZ.t = len;
  let mut found: bool = false;
  let mut result: SZ.t = len;
  
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
      // Keep sorted property in the invariant
      (forall (i j: nat). {:pattern Seq.index s0 i; Seq.index s0 j}
        i < j /\ j < Seq.length s0 ==> Seq.index s0 i <= Seq.index s0 j) /\
      (vfound ==> (
        SZ.v vresult < Seq.length s0 /\
        Seq.index s0 (SZ.v vresult) == key
      )) /\
      (not vfound ==> (
        SZ.v vresult == SZ.v len /\
        (forall (j:nat). 
          j < Seq.length s0 /\
          (j < SZ.v vleft \/ j >= SZ.v vright) 
          ==> Seq.index s0 j =!= key)
      ))
    )
  {
    let vleft = !left;
    let vright = !right;
    
    // Compute mid avoiding overflow
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
      // Key must be in (mid, right) due to sortedness
      // Since s is sorted and elem < key:
      //   forall j <= mid. s[j] <= s[mid] = elem < key
      // The is_sorted predicate should give us this
      left := mid +^ 1sz;
      ()
    } else {
      // elem > key
      // Since s is sorted and elem > key:
      //   forall j >= mid. s[j] >= s[mid] = elem > key
      right := mid;
      ()
    }
  };
  
  !result
}

// ========== Pattern 3: Binary Search Returning Option ==========
// This is cleaner than using sentinel values

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
        SZ.v idx < Seq.length s0 /\
        Seq.index s0 (SZ.v idx) == key
    | None ->
        (forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= key)
  )
{
  let mut left: SZ.t = 0sz;
  let mut right: SZ.t = len;
  let mut found: bool = false;
  let mut result_idx: SZ.t = 0sz;  // Only valid if found=true
  
  while (!left <^ !right && not !found)
  invariant exists* vleft vright vfound vresult.
    R.pts_to left vleft **
    R.pts_to right vright **
    R.pts_to found vfound **
    R.pts_to result_idx vresult **
    A.pts_to a s0 **
    pure (
      SZ.v vleft <= SZ.v vright /\
      SZ.v vright <= SZ.v len /\
      // Keep sorted property in the invariant with SMT patterns
      (forall (i j: nat). {:pattern Seq.index s0 i; Seq.index s0 j}
        i < j /\ j < Seq.length s0 ==> Seq.index s0 i <= Seq.index s0 j) /\
      (vfound ==> (
        SZ.v vresult < Seq.length s0 /\
        Seq.index s0 (SZ.v vresult) == key
      )) /\
      (not vfound ==> (
        (forall (j:nat). 
          j < Seq.length s0 /\
          (j < SZ.v vleft \/ j >= SZ.v vright) 
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
      result_idx := mid;
      ()
    } else if (elem < key) {
      left := mid +^ 1sz;
      ()
    } else {
      right := mid;
      ()
    }
  };
  
  // Construct option based on found flag
  let vfound = !found;
  if (vfound) {
    Some (!result_idx)
  } else {
    None
  }
}

// ========== Summary of the Pattern ==========
(*

KEY INSIGHTS FOR PULSE BINARY SEARCH WITH EARLY EXIT:

1. **Loop Body Must Return ()**
   - Pulse while loops require body to return unit
   - Cannot return value directly from inside loop
   
2. **Use State Variables**
   - `found: bool` - tracks whether key was found
   - `result: SZ.t` or similar - stores the index where found
   - Loop condition: `!left <^ !right && not !found`
   
3. **Loop Invariant Structure**
   ```
   invariant exists* vleft vright vfound vresult.
     <resources> **
     pure (
       <bounds on variables> /\
       (vfound ==> <result is valid>) /\
       (not vfound ==> <key not in excluded region>)
     )
   ```

4. **Three Cases in Loop Body**
   ```pulse
   if (elem = key) {
     found := true;
     result := mid;
     ()
   } else if (elem < key) {
     left := mid +^ 1sz;  // Go right
     ()
   } else {
     right := mid;  // Go left
     ()
   }
   ```

5. **Return After Loop**
   - Read final value: `let vresult = !result`
   - Return value or construct option

6. **Sentinel vs Option**
   - Sentinel: return `len` when not found
   - Option: return `Some idx` or `None`
   - Option is cleaner but sentinel avoids allocation

*)
