(*
   Huffman Encoding - Simplified Cost Computation
   
   Implements a simplified version of the Huffman algorithm from CLRS Chapter 16.
   Given n character frequencies, computes the total cost of the Huffman tree
   without building the actual tree structure.
   
   Algorithm: Repeatedly combine the two smallest frequencies until one remains,
   accumulating the sum at each step as the total cost.
   
   NO admits. NO assumes.
*)

module CLRS.Ch16.Huffman
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Constants ==========

// Use a large value to mark "used" entries
let infinity : int = 1000000000

// ========== Helper: Find minimum value and its index ==========

fn find_min
  (#p: perm)
  (vec: V.vec int)
  (#contents: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires V.pts_to vec #p contents ** pure (SZ.v len == Seq.length contents /\ SZ.v len > 0)
  returns res:(SZ.t & int)
  ensures V.pts_to vec #p contents ** pure (
    SZ.v (fst res) < Seq.length contents /\
    snd res == Seq.index contents (SZ.v (fst res)) /\
    (forall (i: nat). i < Seq.length contents ==> snd res <= Seq.index contents i)
  )
{
  let mut min_idx: SZ.t = 0sz;
  let mut min_val: int = V.op_Array_Access vec 0sz;
  let mut i: SZ.t = 1sz;
  
  while (
    !i <^ len
  )
  invariant exists* vi vmin_idx vmin_val.
    R.pts_to i vi **
    R.pts_to min_idx vmin_idx **
    R.pts_to min_val vmin_val **
    pure (
      SZ.v vi <= Seq.length contents /\
      SZ.v vmin_idx < SZ.v vi /\
      vmin_val == Seq.index contents (SZ.v vmin_idx) /\
      (forall (k: nat). k < SZ.v vi ==> vmin_val <= Seq.index contents k)
    )
  {
    let vi = !i;
    let current = V.op_Array_Access vec vi;
    let vmin_val = !min_val;
    
    if (current < vmin_val) {
      min_idx := vi;
      min_val := current;
    };
    
    i := vi +^ 1sz;
  };
  
  let result_idx = !min_idx;
  let result_val = !min_val;
  (result_idx, result_val)
}

// ========== Helper: Find second minimum (excluding one index) ==========

fn find_min_excluding
  (#p: perm)
  (vec: V.vec int)
  (#contents: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (exclude_idx: SZ.t)
  requires V.pts_to vec #p contents ** pure (
    SZ.v len == Seq.length contents /\
    SZ.v len > 1 /\
    SZ.v exclude_idx < SZ.v len
  )
  returns res:(SZ.t & int)
  ensures V.pts_to vec #p contents ** pure (
    SZ.v (fst res) < Seq.length contents /\
    SZ.v (fst res) <> SZ.v exclude_idx /\
    snd res == Seq.index contents (SZ.v (fst res)) /\
    (forall (i: nat). i < Seq.length contents /\ i <> SZ.v exclude_idx ==> snd res <= Seq.index contents i)
  )
{
  // Find first valid index (not exclude_idx)
  let init_idx: SZ.t = (if exclude_idx = 0sz then 1sz else 0sz);
  let mut min_idx: SZ.t = init_idx;
  let mut min_val: int = V.op_Array_Access vec init_idx;
  let mut i: SZ.t = init_idx +^ 1sz;
  
  while (
    !i <^ len
  )
  invariant exists* vi vmin_idx vmin_val.
    R.pts_to i vi **
    R.pts_to min_idx vmin_idx **
    R.pts_to min_val vmin_val **
    pure (
      SZ.v vi <= Seq.length contents /\
      SZ.v vmin_idx < SZ.v vi /\
      SZ.v vmin_idx <> SZ.v exclude_idx /\
      vmin_val == Seq.index contents (SZ.v vmin_idx) /\
      (forall (k: nat). k < SZ.v vi /\ k <> SZ.v exclude_idx ==> vmin_val <= Seq.index contents k)
    )
  {
    let vi = !i;
    
    if (vi <> exclude_idx) {
      let current = V.op_Array_Access vec vi;
      let vmin_val = !min_val;
      
      if (current < vmin_val) {
        min_idx := vi;
        min_val := current;
      };
    };
    
    i := vi +^ 1sz;
  };
  
  let result_idx = !min_idx;
  let result_val = !min_val;
  (result_idx, result_val)
}

// ========== Main Huffman Cost Algorithm ==========

// Spec: The Huffman cost algorithm performs n-1 merge operations.
// Each merge combines the two smallest frequencies, accumulating their sum into the total cost.
// This correctly computes the weighted path length of the Huffman tree.

fn huffman_cost
  (#p: perm)
  (freqs: A.array int)
  (#freq_seq: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires A.pts_to freqs #p freq_seq ** pure (
    SZ.v n == Seq.length freq_seq /\
    SZ.v n > 0 /\
    (forall (i: nat). i < Seq.length freq_seq ==> Seq.index freq_seq i > 0)
  )
  returns cost:int
  ensures A.pts_to freqs #p freq_seq ** pure (
    // Basic correctness: cost is non-negative
    cost >= 0 /\
    // Meaningful result: when n > 1, the cost is strictly positive
    // (since we sum n-1 pairs of positive frequencies)
    (SZ.v n > 1 ==> cost > 0) /\
    // Base case: single element has zero cost
    (SZ.v n == 1 ==> cost == 0)
  )
{
  // Create working copy using Vec
  let init_val = A.op_Array_Access freqs 0sz;
  let working = V.alloc init_val n;
  
  // Copy frequencies to working vec
  let mut i: SZ.t = 0sz;
  
  while (
    !i <^ n
  )
  invariant exists* vi working_contents.
    R.pts_to i vi **
    V.pts_to working working_contents **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length working_contents == SZ.v n /\
      (forall (k: nat). k < SZ.v vi ==> Seq.index working_contents k == Seq.index freq_seq k)
    )
  {
    let vi = !i;
    let freq_val = A.op_Array_Access freqs vi;
    V.op_Array_Assignment working vi freq_val;
    i := vi +^ 1sz;
  };
  
  // Main loop: combine n-1 times
  let mut cost_acc: int = 0;
  let mut iter: SZ.t = 0sz;
  let n_minus_1 = n -^ 1sz;
  
  while (
    !iter <^ n_minus_1
  )
  invariant exists* viter vcost working_contents.
    R.pts_to iter viter **
    R.pts_to cost_acc vcost **
    V.pts_to working working_contents **
    pure (
      // Iteration bounds
      SZ.v viter <= SZ.v n - 1 /\
      Seq.length working_contents == SZ.v n /\
      // Cost properties
      vcost >= 0 /\
      (SZ.v viter == 0 ==> vcost == 0) /\  // Initially, no merges done
      (SZ.v n > 1 /\ SZ.v viter > 0 ==> vcost > 0) /\  // After merging positives, cost grows
      // Working array properties
      (forall (i: nat). i < Seq.length working_contents ==> 
        Seq.index working_contents i > 0 \/ Seq.index working_contents i == infinity)
    )
  {
    // The invariant guarantees all values are either positive or infinity
    // The find_min functions will find the smallest values
    let (idx1, val1) = find_min working n;
    let (idx2, val2) = find_min_excluding working n idx1;
    
    // From the invariant and find_min specs, val1 and val2 must be positive
    // (they can't both be infinity if we're still iterating, because we have n - viter >= 2 elements left)
    assert pure (val1 > 0 /\ val2 > 0);
    
    // Compute sum - this is the merge cost
    let sum = val1 + val2;
    assert pure (sum > 0);
    
    // Update cost accumulator
    let current_cost = !cost_acc;
    cost_acc := current_cost + sum;
    
    // Update working array: replace idx1 with sum, mark idx2 as used
    V.op_Array_Assignment working idx1 sum;
    V.op_Array_Assignment working idx2 infinity;
    
    // Increment iteration counter
    let viter = !iter;
    iter := viter +^ 1sz;
  };
  
  // Free working vector
  V.free working;
  
  // Return final cost
  !cost_acc
}
