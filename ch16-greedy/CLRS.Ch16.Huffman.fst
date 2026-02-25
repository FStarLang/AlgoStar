(*
   Huffman Encoding - Imperative Implementation
   
   CLRS Section 16.3 presents HUFFMAN(C):
   1. Build a priority queue Q from the character frequencies
   2. For i = 1 to |C|-1:
      a. Extract two minimum-frequency nodes z.left, z.right from Q
      b. Create new node z with freq = z.left.freq + z.right.freq
      c. Insert z into Q
   3. Return the remaining tree in Q (the Huffman tree)
   
   This module provides two implementations:
   - huffman_cost: computes just the cost via array-based linear scans
   - huffman_tree: builds the full Huffman tree using Pulse.Lib.PriorityQueue,
     following the CLRS algorithm with imperative extract-min and insert
   
   The postcondition of huffman_tree connects to the specification in
   CLRS.Ch16.Huffman.Spec: weighted path length equals cost, and cost bounds.
   
   NO admits. NO assumes.
*)

module CLRS.Ch16.Huffman
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open Pulse.Lib.PriorityQueue
open Pulse.Lib.TotalOrder
open FStar.SizeT
open FStar.Mul
open FStar.Order

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module PQ = Pulse.Lib.PriorityQueue

module HSpec = CLRS.Ch16.Huffman.Spec

// ========== Total order on htree (structural, frequency-first) ==========

let rec htree_compare (t1 t2: HSpec.htree) : Tot order (decreases t1) =
  match t1, t2 with
  | HSpec.Leaf f1, HSpec.Leaf f2 ->
    if f1 < f2 then Lt else if f1 = f2 then Eq else Gt
  | HSpec.Leaf _, HSpec.Internal _ _ _ -> Lt
  | HSpec.Internal _ _ _, HSpec.Leaf _ -> Gt
  | HSpec.Internal f1 l1 r1, HSpec.Internal f2 l2 r2 ->
    if f1 < f2 then Lt
    else if f1 > f2 then Gt
    else match htree_compare l1 l2 with
         | Lt -> Lt
         | Gt -> Gt
         | Eq -> htree_compare r1 r2

let rec htree_compare_eq (t1 t2: HSpec.htree)
  : Lemma (ensures eq (htree_compare t1 t2) <==> t1 == t2)
          (decreases t1)
  = match t1, t2 with
    | HSpec.Leaf _, HSpec.Leaf _ -> ()
    | HSpec.Leaf _, HSpec.Internal _ _ _
    | HSpec.Internal _ _ _, HSpec.Leaf _ -> ()
    | HSpec.Internal _ l1 r1, HSpec.Internal _ l2 r2 ->
      htree_compare_eq l1 l2;
      htree_compare_eq r1 r2

let rec htree_compare_flip (t1 t2: HSpec.htree)
  : Lemma (ensures htree_compare t1 t2 == flip_order (htree_compare t2 t1))
          (decreases t1)
  = match t1, t2 with
    | HSpec.Leaf _, HSpec.Leaf _ -> ()
    | HSpec.Leaf _, HSpec.Internal _ _ _
    | HSpec.Internal _ _ _, HSpec.Leaf _ -> ()
    | HSpec.Internal _ l1 r1, HSpec.Internal _ l2 r2 ->
      htree_compare_flip l1 l2;
      htree_compare_flip r1 r2

let rec htree_compare_trans (t1 t2 t3: HSpec.htree)
  : Lemma (requires lt (htree_compare t1 t2) /\ lt (htree_compare t2 t3))
          (ensures lt (htree_compare t1 t3))
          (decreases t1)
  = match t1, t2, t3 with
    | HSpec.Leaf _, HSpec.Leaf _, HSpec.Leaf _ -> ()
    | HSpec.Leaf _, HSpec.Leaf _, HSpec.Internal _ _ _ -> ()
    | HSpec.Leaf _, HSpec.Internal _ _ _, _ -> ()
    | HSpec.Internal _ _ _, HSpec.Leaf _, _ -> ()
    | HSpec.Internal _ _ _, HSpec.Internal _ _ _, HSpec.Leaf _ -> ()
    | HSpec.Internal f1 l1 r1, HSpec.Internal f2 l2 r2, HSpec.Internal f3 l3 r3 ->
      if f1 < f2 then ()
      else if f2 > f1 then ()
      else (
        if f2 < f3 then ()
        else if f3 > f2 then ()
        else (
          match htree_compare l1 l2, htree_compare l2 l3 with
          | Lt, Lt -> htree_compare_trans l1 l2 l3
          | Lt, Eq -> htree_compare_eq l2 l3
          | Lt, Gt -> ()
          | Eq, Lt -> htree_compare_eq l1 l2
          | Eq, Eq -> htree_compare_eq l1 l2; htree_compare_eq l2 l3;
                      htree_compare_trans r1 r2 r3
          | Eq, Gt -> ()
          | Gt, _ -> ()
        )
      )

let htree_total_order_proof ()
  : Lemma (
      (forall (x y: HSpec.htree). {:pattern htree_compare x y}
        eq (htree_compare x y) <==> x == y) /\
      (forall (x y z: HSpec.htree). {:pattern htree_compare x y; htree_compare y z}
        lt (htree_compare x y) /\ lt (htree_compare y z) ==> lt (htree_compare x z)) /\
      (forall (x y: HSpec.htree). {:pattern htree_compare x y}
        htree_compare x y == flip_order (htree_compare y x))
    )
  = Classical.forall_intro_2 htree_compare_eq;
    Classical.forall_intro_2 htree_compare_flip;
    Classical.forall_intro_3 (Classical.move_requires_3 htree_compare_trans)

instance htree_order : total_order HSpec.htree = {
  compare = htree_compare;
  properties = htree_total_order_proof ()
}

// ========== Lemma: extends implies length + 1 ==========
// The PQ's `extends` predicate is count-based. We prove it implies length change.

module L = FStar.List.Tot.Base
module SeqP = FStar.Seq.Properties

let rec list_count_pos_mem (#t:eqtype) (x:t) (l:list t)
  : Lemma (requires L.count x l > 0) (ensures L.mem x l)
  = match l with
    | [] -> ()
    | h :: tl -> if h = x then () else list_count_pos_mem x tl

let rec list_remove_first (#t:eqtype) (x:t) (l:list t{L.mem x l})
  : Tot (l':list t{L.length l' == L.length l - 1 /\
                   L.count x l' == L.count x l - 1 /\
                   (forall (y:t). y <> x ==> L.count y l' == L.count y l)})
  = match l with
    | h :: tl -> 
      if h = x then tl
      else h :: list_remove_first x tl

let rec same_list_counts_same_length (#t:eqtype) (l0 l1:list t)
  : Lemma (requires forall (y:t). L.count y l0 == L.count y l1)
          (ensures L.length l0 == L.length l1)
          (decreases (L.length l0))
  = match l0 with
    | [] ->
      (match l1 with
       | [] -> ()
       | h :: _ -> assert (L.count h l1 > 0); assert (L.count h l0 == 0))
    | h :: tl ->
      list_count_pos_mem h l1;
      let l1' = list_remove_first h l1 in
      let aux (y:t) : Lemma (L.count y tl == L.count y l1') = () in
      Classical.forall_intro aux;
      same_list_counts_same_length tl l1'

let extends_length (#t:eqtype) (s0 s1:Seq.seq t) (x:t)
  : Lemma (requires extends s0 s1 x)
          (ensures Seq.length s1 == Seq.length s0 + 1)
  = let l0 = Seq.seq_to_list s0 in
    let l1 = Seq.seq_to_list s1 in
    SeqP.lemma_seq_to_list_permutation s0;
    SeqP.lemma_seq_to_list_permutation s1;
    list_count_pos_mem x l1;
    let l1' = list_remove_first x l1 in
    let aux (y:t) : Lemma (L.count y l1' == L.count y l0) = () in
    Classical.forall_intro aux;
    same_list_counts_same_length l1' l0

// ========== Constants ==========

let infinity : int = 1000000000

// ========== Helper: Find minimum value and its index (for huffman_cost) ==========

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

// ========== Full Huffman Tree Construction (CLRS §16.3) ==========
// Truly imperative: uses Pulse.Lib.PriorityQueue for extract-min and insert.
// Follows the CLRS algorithm line by line:
//   1. Create PQ Q, insert Leaf(freq[i]) for each i
//   2. For i = 1 to n-1:
//      left = EXTRACT-MIN(Q)
//      right = EXTRACT-MIN(Q)
//      z = Internal(left.freq + right.freq, left, right)
//      INSERT(Q, z)
//   3. Return EXTRACT-MIN(Q)

//SNIPPET_START: huffman_tree_sig
```pulse
fn huffman_tree
  (freqs: A.array int)
  (#freq_seq: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires A.pts_to freqs freq_seq ** pure (
    SZ.v n == Seq.length freq_seq /\
    SZ.v n > 0 /\
    SZ.fits (2 * SZ.v n + 2) /\
    (forall (i: nat). i < Seq.length freq_seq ==> Seq.index freq_seq i > 0)
  )
  returns result: HSpec.htree
  ensures A.pts_to freqs freq_seq ** pure (
    HSpec.weighted_path_length result == HSpec.cost result /\
    HSpec.cost result >= 0
  )
//SNIPPET_END: huffman_tree_sig
{
  // Line 2: Q = C — create PQ and insert leaf nodes
  let cap = SZ.add n 1sz;
  let pq = PQ.create #HSpec.htree #htree_order cap;
  
  // Insert all leaf nodes into PQ
  let mut i: SZ.t = 0sz;
  while (
    !i <^ n
  )
  invariant exists* vi pq_seq.
    R.pts_to i vi **
    is_pqueue pq pq_seq (SZ.v cap) **
    A.pts_to freqs freq_seq **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length pq_seq == SZ.v vi
    )
  {
    let vi = !i;
    let f = A.op_Array_Access freqs vi;
    let leaf = HSpec.Leaf f;
    with s_before. assert (is_pqueue pq s_before (SZ.v cap));
    PQ.insert pq leaf;
    with s_after. assert (is_pqueue pq s_after (SZ.v cap));
    extends_length #HSpec.htree s_before s_after leaf;
    i := vi +^ 1sz;
  };
  
  // Lines 3-8: Merge loop — extract two mins, merge, insert  
  let mut pq_len: SZ.t = n;
  while (
    let vlen = !pq_len;
    (vlen >^ 1sz)
  )
  invariant exists* vlen pq_seq.
    R.pts_to pq_len vlen **
    is_pqueue pq pq_seq (SZ.v cap) **
    A.pts_to freqs freq_seq **
    pure (
      SZ.v vlen == Seq.length pq_seq /\
      Seq.length pq_seq > 0 /\
      Seq.length pq_seq <= SZ.v n /\
      SZ.fits (2 * Seq.length pq_seq + 2)
    )
  {
    let vlen = !pq_len;
    with s0. assert (is_pqueue pq s0 (SZ.v cap));
    // Line 5: left = EXTRACT-MIN(Q)
    let left = PQ.extract_min pq;
    with s1. assert (is_pqueue pq s1 (SZ.v cap));
    extends_length #HSpec.htree s1 s0 left;
    // Line 6: right = EXTRACT-MIN(Q)
    let right = PQ.extract_min pq;
    with s2. assert (is_pqueue pq s2 (SZ.v cap));
    extends_length #HSpec.htree s2 s1 right;
    // Line 7: z = merge(left, right)
    let z = HSpec.Internal (HSpec.freq_of left + HSpec.freq_of right) left right;
    // Line 8: INSERT(Q, z)
    PQ.insert pq z;
    with s3. assert (is_pqueue pq s3 (SZ.v cap));
    extends_length #HSpec.htree s2 s3 z;
    pq_len := vlen -^ 1sz;
  };
  
  // Line 9: return EXTRACT-MIN(Q) — PQ has exactly 1 element
  let result = PQ.extract_min pq;
  PQ.free pq;
  HSpec.wpl_equals_cost result;
  result
}
```
