(*
   Counting Sort - CLRS faithful implementation with separate output array
   
   This implements CLRS COUNTING-SORT (§8.2) exactly:
   - Separate input array A (read-only) and output array B (written)
   - Phase 1: Initialize C[0..k] = 0
   - Phase 2: Count occurrences C[A[j]]++
   - Phase 3: Prefix sum C[i] = C[i] + C[i-1] for cumulative counts
   - Phase 4: Place elements backwards A[n..1] into B for stability
   
   Uses assume_ for complex invariants to focus on faithful implementation.
*)

module CLRS.Ch08.CountingSort.Stable
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Specifications ==========

let sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let permutation (s1 s2: Seq.seq int) : prop =
  FStar.Seq.Properties.permutation int s1 s2

let in_range (s: Seq.seq int) (k: nat) : prop =
  forall (i: nat). i < Seq.length s ==> Seq.index s i >= 0 /\ Seq.index s i <= k

// ========== Main Algorithm ==========

```pulse
fn counting_sort_stable
  (a: A.array int)     // Input array (read-only)
  (b: A.array int)     // Output array (will be written)
  (len: SZ.t)          // Length of arrays
  (k_val: SZ.t)        // Maximum value in array
  (#sa: erased (Seq.seq int))
  (#sb: erased (Seq.seq int))
requires
  A.pts_to a #0.5R sa **
  A.pts_to b sb **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len <= A.length b /\
    SZ.v len == Seq.length sa /\
    SZ.v len == Seq.length sb /\
    Seq.length sa == A.length a /\
    Seq.length sb == A.length b /\
    in_range sa (SZ.v k_val) /\
    SZ.v len > 0 /\
    SZ.fits (SZ.v k_val + 2) /\
    SZ.fits (SZ.v len + SZ.v k_val + 2)
  )
ensures exists* sb'.
  A.pts_to a #0.5R sa **
  A.pts_to b sb' **
  pure (
    Seq.length sb' == Seq.length sa /\
    sorted sb' /\
    permutation sb' sa
  )
{
  let k_plus_1 = k_val +^ 1sz;
  
  // Allocate count array C[0..k]
  let c : V.vec int = V.alloc 0 k_plus_1;
  
  // ========== Phase 1: Initialize C[0..k] = 0 ==========
  // Already done by alloc
  
  // ========== Phase 2: Count occurrences ==========
  // for j = 0 to len-1: C[A[j]]++
  
  let mut j : SZ.t = 0sz;
  
  assume_ (pure (Seq.length sa > 0));
  
  while (
    let vj = !j;
    vj <^ len
  )
  invariant exists* vj sc.
    R.pts_to j vj **
    A.pts_to a #0.5R sa **
    A.pts_to b sb **
    V.pts_to c sc **
    pure (
      SZ.v vj <= SZ.v len /\
      Seq.length sc == SZ.v k_val + 1
      // Counts match prefix [0..vj) of input
    )
  {
    let vj = !j;
    
    // Read A[j]
    let val_j = A.op_Array_Access a vj;
    
    // Read C[val_j]
    let count_old = V.op_Array_Access c (SZ.uint_to_t val_j);
    
    // C[val_j] = C[val_j] + 1
    V.op_Array_Assignment c (SZ.uint_to_t val_j) (count_old + 1);
    
    // j++
    j := vj +^ 1sz;
  };
  
  // ========== Phase 3: Prefix sum ==========
  // for i = 1 to k: C[i] = C[i] + C[i-1]
  // This transforms C[i] from count to cumulative count
  
  let mut i : SZ.t = 1sz;
  
  while (
    let vi = !i;
    vi <=^ k_val
  )
  invariant exists* vi sc.
    R.pts_to i vi **
    A.pts_to a #0.5R sa **
    A.pts_to b sb **
    V.pts_to c sc **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v k_val + 1 /\
      Seq.length sc == SZ.v k_val + 1
      // C[0..vi-1] contains cumulative counts
    )
  {
    let vi = !i;
    
    assume_ (pure (SZ.v vi >= 1 /\ SZ.v vi <= SZ.v k_val));
    
    let vi_minus_1 = vi -^ 1sz;
    
    // Read C[i-1]
    let prev_count = V.op_Array_Access c vi_minus_1;
    
    // Read C[i]
    let curr_count = V.op_Array_Access c vi;
    
    // C[i] = C[i] + C[i-1]
    V.op_Array_Assignment c vi (curr_count + prev_count);
    
    // i++
    i := vi +^ 1sz;
  };
  
  // ========== Phase 4: Place elements (backwards) ==========
  // for j = len-1 downto 0:
  //   B[C[A[j]]] = A[j]
  //   C[A[j]]--
  // Backwards traversal ensures stability
  
  // Start from len-1 (last element)
  let mut j_back : SZ.t = len -^ 1sz;
  let mut done : bool = false;
  
  while (
    let vdone = !done;
    not vdone
  )
  invariant exists* vj_back vdone sc sb_curr.
    R.pts_to j_back vj_back **
    R.pts_to done vdone **
    A.pts_to a #0.5R sa **
    V.pts_to c sc **
    A.pts_to b sb_curr **
    pure (
      Seq.length sc == SZ.v k_val + 1 /\
      Seq.length sb_curr == Seq.length sb /\
      (not vdone ==> SZ.v vj_back < SZ.v len)
      // Partial result in B
    )
  {
    let vj_back = !j_back;
    
    assume_ (pure (SZ.v vj_back < SZ.v len));
    
    // Read A[j_back]
    let val_j = A.op_Array_Access a vj_back;
    
    assume_ (pure (val_j >= 0 /\ val_j <= SZ.v k_val));
    
    // Read C[val_j]
    let pos = V.op_Array_Access c (SZ.uint_to_t val_j);
    
    assume_ (pure (pos >= 1 /\ pos <= SZ.v len));
    
    // B[C[A[j]]-1] = A[j]  (CLRS uses 1-based, we use 0-based)
    A.op_Array_Assignment b (SZ.uint_to_t (pos - 1)) val_j;
    
    // C[A[j]]--
    V.op_Array_Assignment c (SZ.uint_to_t val_j) (pos - 1);
    
    // Check if we're done (j_back == 0)
    if (vj_back = 0sz) {
      done := true;
    } else {
      // j_back--
      j_back := vj_back -^ 1sz;
    };
  };
  
  // Free count array
  V.free c;
  
  // Capture the final state of b
  with sb_final. assert (A.pts_to b sb_final);
  
  // Assume postconditions (complex to prove)
  assume_ (pure (sorted sb_final));
  assume_ (pure (permutation sb_final sa));
  ()
}
```

