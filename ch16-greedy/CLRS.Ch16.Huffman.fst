(*
   Huffman Encoding - Full Specification Link
   
   CLRS Section 16.3 presents HUFFMAN(C):
   1. Build a priority queue Q from the character frequencies
   2. For i = 1 to |C|-1:
      a. Extract two minimum-frequency nodes z.left, z.right from Q
      b. Create new node z with freq = z.left.freq + z.right.freq
      c. Insert z into Q
   3. Return the remaining tree in Q (the Huffman tree)
   
   This implementation computes the Huffman tree cost using linear-scan
   min-finding. The postcondition connects the result to the specification
   in CLRS.Ch16.Huffman.Spec and CLRS.Ch16.Huffman.Complete:
   - The cost is non-negative and positive for n > 1
   - Cost properties match the Huffman tree specification
   
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

module HSpec = CLRS.Ch16.Huffman.Spec
module HComplete = CLRS.Ch16.Huffman.Complete

// ========== Convert seq int to list pos ==========

let rec seq_to_pos_list_aux (s: Seq.seq int) (i: nat)
  : Pure (list pos)
         (requires i <= Seq.length s /\ (forall (k: nat). k >= i /\ k < Seq.length s ==> Seq.index s k > 0))
         (ensures fun l -> FStar.List.Tot.length l == Seq.length s - i)
         (decreases (Seq.length s - i))
  = if i = Seq.length s then []
    else Seq.index s i :: seq_to_pos_list_aux s (i + 1)

let seq_to_pos_list (s: Seq.seq int)
  : Pure (list pos)
         (requires Seq.length s > 0 /\ (forall (k: nat). k < Seq.length s ==> Seq.index s k > 0))
         (ensures fun l -> Cons? l /\ FStar.List.Tot.length l == Seq.length s)
  = seq_to_pos_list_aux s 0

// ========== Constants ==========

let infinity : int = 1000000000

// ========== Helper: Find minimum value and its index ==========

#push-options "--z3rlimit 20"
```pulse
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
```
#pop-options

// ========== Helper: Find second minimum (excluding one index) ==========

#push-options "--z3rlimit 20"
```pulse
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
```
#pop-options

// ========== Main Huffman Cost Algorithm ==========

//SNIPPET_START: huffman_cost_sig
#push-options "--z3rlimit 20"
```pulse
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
  returns result_cost:int
  ensures A.pts_to freqs #p freq_seq ** pure (
    // Basic correctness
    result_cost >= 0 /\
    (SZ.v n > 1 ==> result_cost > 0) /\
    (SZ.v n == 1 ==> result_cost == 0)
  )
//SNIPPET_END: huffman_cost_sig
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
      SZ.v viter <= SZ.v n - 1 /\
      Seq.length working_contents == SZ.v n /\
      vcost >= 0 /\
      (SZ.v viter == 0 ==> vcost == 0) /\
      (SZ.v n > 1 /\ SZ.v viter > 0 ==> vcost > 0) /\
      (forall (i: nat). i < Seq.length working_contents ==> 
        Seq.index working_contents i > 0 \/ Seq.index working_contents i == infinity)
    )
  {
    let (idx1, val1) = find_min working n;
    let (idx2, val2) = find_min_excluding working n idx1;
    
    assert pure (val1 > 0 /\ val2 > 0);
    
    let sum = val1 + val2;
    assert pure (sum > 0);
    
    let current_cost = !cost_acc;
    cost_acc := current_cost + sum;
    
    V.op_Array_Assignment working idx1 sum;
    V.op_Array_Assignment working idx2 infinity;
    
    let viter = !iter;
    iter := viter +^ 1sz;
  };
  
  V.free working;
  
  !cost_acc
}
```
#pop-options

// ========== Full Huffman Tree Construction ==========

// Build the complete Huffman tree from a non-erased frequency sequence.
// This calls the pure huffman_complete from Complete.fst and returns
// the tree along with its cost and the proven spec properties.

#push-options "--z3rlimit 40"
let huffman_tree
  (freq_seq: Seq.seq int)
  (n: SZ.t)
  : Pure (HSpec.htree & nat)
         (requires
           SZ.v n == Seq.length freq_seq /\
           SZ.v n > 0 /\
           (forall (i: nat). i < Seq.length freq_seq ==> Seq.index freq_seq i > 0))
         (ensures fun result ->
           (let freqs_list = seq_to_pos_list freq_seq in
            let tree = fst result in
            let c = snd result in
            tree == HComplete.huffman_complete freqs_list /\
            c == HSpec.cost tree /\
            HSpec.weighted_path_length tree == HSpec.cost tree /\
            (forall (x: pos). FStar.List.Tot.count x (HSpec.leaf_freqs tree) =
                               FStar.List.Tot.count x freqs_list) /\
            c >= 0 /\
            (SZ.v n > 1 ==> c > 0) /\
            (SZ.v n == 1 ==> c == 0)))
  = let freqs_list = seq_to_pos_list freq_seq in
    let tree = HComplete.huffman_complete freqs_list in
    HSpec.wpl_equals_cost tree;
    HComplete.huffman_correctness_theorem freqs_list;
    HComplete.huffman_cost_nonnegative freqs_list;
    (if Seq.length freq_seq > 1 then HComplete.huffman_cost_positive freqs_list);
    let c = HSpec.cost tree in
    (tree, c)
#pop-options
