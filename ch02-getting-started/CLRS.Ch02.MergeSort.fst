(*
   Merge Sort - Verified implementation in Pulse
   
   A genuine top-down merge sort that:
   1. Divides the array in half
   2. Recursively sorts each half
   3. Merges the sorted halves

   Proves:
   1. The result is sorted
   2. The result is a permutation of the input
   
   NO admits. NO assumes.
*)

module CLRS.Ch02.MergeSort
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Array.PtsToRange
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open CLRS.Common.SortSpec

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Classical = FStar.Classical

open CLRS.Ch02.MergeSort.Complexity

//SNIPPET_START: seq_merge
// ================================================================
// Pure Merge Function on Sequences
// ================================================================

let rec seq_merge (s1 s2: Seq.seq int) 
  : Tot (Seq.seq int) (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then s2
    else if Seq.length s2 = 0 then s1
    else let h1 = Seq.head s1 in
         let h2 = Seq.head s2 in
         if h1 <= h2 
         then Seq.cons h1 (seq_merge (Seq.tail s1) s2)
         else Seq.cons h2 (seq_merge s1 (Seq.tail s2))
//SNIPPET_END: seq_merge

// ================================================================
// Merge Length Lemma  
// ================================================================

let rec seq_merge_length (s1 s2: Seq.seq int)
  : Lemma (ensures Seq.length (seq_merge s1 s2) == Seq.length s1 + Seq.length s2)
          (decreases (Seq.length s1 + Seq.length s2))
          [SMTPat (Seq.length (seq_merge s1 s2))]
  = if Seq.length s1 = 0 then ()
    else if Seq.length s2 = 0 then ()
    else if Seq.head s1 <= Seq.head s2 then seq_merge_length (Seq.tail s1) s2
    else seq_merge_length s1 (Seq.tail s2)

// ================================================================
// Merge preserves count (=> permutation of append)
// ================================================================

#push-options "--z3rlimit 50 --fuel 3 --ifuel 2"

let count_empty (x: int) (s: Seq.seq int)
  : Lemma (requires Seq.length s = 0)
          (ensures SeqP.count x s == 0)
  = ()

let count_cons (x: int) (h: int) (t: Seq.seq int)
  : Lemma (ensures SeqP.count x (Seq.cons h t) == (if h = x then 1 else 0) + SeqP.count x t)
  = assert (Seq.head (Seq.cons h t) == h);
    assert (Seq.tail (Seq.cons h t) `Seq.equal` t)

let rec seq_merge_count (x: int) (s1 s2: Seq.seq int)
  : Lemma (ensures SeqP.count x (seq_merge s1 s2) == SeqP.count x s1 + SeqP.count x s2)
          (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then (
      count_empty x s1;
      assert (seq_merge s1 s2 == s2)
    )
    else if Seq.length s2 = 0 then (
      count_empty x s2;
      assert (seq_merge s1 s2 == s1)
    )
    else 
      let h1 = Seq.head s1 in
      let h2 = Seq.head s2 in
      if h1 <= h2 then (
        seq_merge_count x (Seq.tail s1) s2;
        count_cons x h1 (seq_merge (Seq.tail s1) s2)
      ) else (
        seq_merge_count x s1 (Seq.tail s2);
        count_cons x h2 (seq_merge s1 (Seq.tail s2))
      )

let seq_merge_permutation (s1 s2: Seq.seq int)
  : Lemma (ensures permutation (Seq.append s1 s2) (seq_merge s1 s2))
  = reveal_opaque (`%permutation) (permutation (Seq.append s1 s2) (seq_merge s1 s2));
    SeqP.lemma_append_count s1 s2;
    Classical.forall_intro (fun x -> seq_merge_count x s1 s2)

#pop-options

// ================================================================
// Merge preserves sortedness
// ================================================================

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"

let all_ge (v: int) (s: Seq.seq int) : prop =
  forall (i: nat). i < Seq.length s ==> v <= Seq.index s i

let rec seq_merge_all_ge (v: int) (s1 s2: Seq.seq int)
  : Lemma (requires all_ge v s1 /\ all_ge v s2)
          (ensures all_ge v (seq_merge s1 s2))
          (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then ()
    else if Seq.length s2 = 0 then ()
    else if Seq.head s1 <= Seq.head s2 then seq_merge_all_ge v (Seq.tail s1) s2
    else seq_merge_all_ge v s1 (Seq.tail s2)

let sorted_all_ge_head (s: Seq.seq int)
  : Lemma (requires Seq.length s > 0 /\ sorted s)
          (ensures all_ge (Seq.head s) s)
  = ()

let sorted_tail (s: Seq.seq int)
  : Lemma (requires Seq.length s > 0 /\ sorted s)
          (ensures sorted (Seq.tail s))
  = ()

let rec seq_merge_sorted (s1 s2: Seq.seq int)
  : Lemma (requires sorted s1 /\ sorted s2)
          (ensures sorted (seq_merge s1 s2))
          (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then ()
    else if Seq.length s2 = 0 then ()
    else
      let h1 = Seq.head s1 in
      let h2 = Seq.head s2 in
      sorted_tail s1;
      sorted_tail s2;
      if h1 <= h2 then (
        seq_merge_sorted (Seq.tail s1) s2;
        sorted_all_ge_head s1;
        sorted_all_ge_head s2;
        // h1 <= all of tail s1, h1 <= h2 <= all of s2
        // so h1 <= all of merge (tail s1) s2
        seq_merge_all_ge h1 (Seq.tail s1) s2;
        // Now sorted (seq_merge (tail s1) s2) and h1 <= all of it
        // so sorted (cons h1 (seq_merge (tail s1) s2))
        ()
      ) else (
        seq_merge_sorted s1 (Seq.tail s2);
        sorted_all_ge_head s1;
        sorted_all_ge_head s2;
        seq_merge_all_ge h2 s1 (Seq.tail s2);
        ()
      )

#pop-options

// ================================================================
// Key lemma: relating seq_merge to head and suffix
// ================================================================

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"

// When left is empty, head of seq_merge is head of right
let seq_merge_head_right (s1 s2: Seq.seq int)
  : Lemma (requires Seq.length s1 = 0 /\ Seq.length s2 > 0)
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s2 /\
                   Seq.tail (seq_merge s1 s2) == Seq.tail s2)
  = ()

// When right is empty, head of seq_merge is head of left
let seq_merge_head_left (s1 s2: Seq.seq int)
  : Lemma (requires Seq.length s1 > 0 /\ Seq.length s2 = 0)
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s1 /\
                   Seq.tail (seq_merge s1 s2) == Seq.tail s1)
  = ()

// When h1 <= h2, head is h1 and tail is merge of tail s1 with s2
let seq_merge_take_left (s1 s2: Seq.seq int)
  : Lemma (requires Seq.length s1 > 0 /\ Seq.length s2 > 0 /\
                     Seq.head s1 <= Seq.head s2)
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s1 /\
                   Seq.tail (seq_merge s1 s2) == seq_merge (Seq.tail s1) s2)
  = assert (Seq.head (Seq.cons (Seq.head s1) (seq_merge (Seq.tail s1) s2)) == Seq.head s1);
    assert (Seq.equal (Seq.tail (Seq.cons (Seq.head s1) (seq_merge (Seq.tail s1) s2)))
                      (seq_merge (Seq.tail s1) s2))

// When h2 < h1, head is h2 and tail is merge of s1 with tail s2
let seq_merge_take_right (s1 s2: Seq.seq int)
  : Lemma (requires Seq.length s1 > 0 /\ Seq.length s2 > 0 /\
                     ~(Seq.head s1 <= Seq.head s2))
          (ensures Seq.length (seq_merge s1 s2) > 0 /\
                   Seq.head (seq_merge s1 s2) == Seq.head s2 /\
                   Seq.tail (seq_merge s1 s2) == seq_merge s1 (Seq.tail s2))
  = assert (Seq.head (Seq.cons (Seq.head s2) (seq_merge s1 (Seq.tail s2))) == Seq.head s2);
    assert (Seq.equal (Seq.tail (Seq.cons (Seq.head s2) (seq_merge s1 (Seq.tail s2))))
                      (seq_merge s1 (Seq.tail s2)))

// Slice decomposition: slice s i len == cons (index s i) (slice s (i+1) len)
let slice_cons (s: Seq.seq int) (i: nat) (len: nat)
  : Lemma (requires i < len /\ len <= Seq.length s)
          (ensures Seq.length (Seq.slice s i len) > 0 /\
                   Seq.head (Seq.slice s i len) == Seq.index s i /\
                   Seq.tail (Seq.slice s i len) == Seq.slice s (i + 1) len)
  = assert (Seq.equal (Seq.tail (Seq.slice s i len)) (Seq.slice s (i + 1) len))

// Index into seq_merge from suffix: 
// If suffix = seq_merge(slice s1 i l1) (slice s2 j l2), 
// then its head is the next value to write at position k in the output.
// After writing, the new suffix equals the tail of this merge.

// Combine: if the suffix invariant holds, and we write the head of the suffix
// into position k, then the invariant holds with the appropriate shift.
let suffix_step_left (s1 s2: Seq.seq int) (i l1 j l2: nat)
  : Lemma (requires i < l1 /\ l1 <= Seq.length s1 /\
                     j <= l2 /\ l2 <= Seq.length s2 /\
                     (Seq.length (Seq.slice s2 j l2) = 0 \/
                      Seq.index s1 i <= Seq.head (Seq.slice s2 j l2)))
          (ensures
            Seq.length (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) > 0 /\
            Seq.head (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) == Seq.index s1 i /\
            seq_merge (Seq.slice s1 (i+1) l1) (Seq.slice s2 j l2) ==
            Seq.tail (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)))
  = slice_cons s1 i l1;
    let sl1 = Seq.slice s1 i l1 in
    let sl2 = Seq.slice s2 j l2 in
    seq_merge_length sl1 sl2;
    if Seq.length sl2 = 0 then
      seq_merge_head_left sl1 sl2
    else (
      assert (Seq.head sl1 == Seq.index s1 i);
      assert (Seq.head sl1 <= Seq.head sl2);
      seq_merge_take_left sl1 sl2;
      assert (Seq.equal (Seq.tail sl1) (Seq.slice s1 (i+1) l1))
    )

let suffix_step_right (s1 s2: Seq.seq int) (i l1 j l2: nat)
  : Lemma (requires i <= l1 /\ l1 <= Seq.length s1 /\
                     j < l2 /\ l2 <= Seq.length s2 /\
                     (Seq.length (Seq.slice s1 i l1) = 0 \/
                      ~(Seq.index s1 i <= Seq.index s2 j)))
          (ensures
            Seq.length (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) > 0 /\
            Seq.head (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) == Seq.index s2 j /\
            seq_merge (Seq.slice s1 i l1) (Seq.slice s2 (j+1) l2) ==
            Seq.tail (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)))
  = slice_cons s2 j l2;
    let sl1 = Seq.slice s1 i l1 in
    let sl2 = Seq.slice s2 j l2 in
    seq_merge_length sl1 sl2;
    if Seq.length sl1 = 0 then
      seq_merge_head_right sl1 sl2
    else (
      assert (Seq.head sl2 == Seq.index s2 j);
      assert (~(Seq.head sl1 <= Seq.head sl2));
      seq_merge_take_right sl1 sl2;
      assert (Seq.equal (Seq.tail sl2) (Seq.slice s2 (j+1) l2))
    )

// Initially, slice s1 0 l1 == s1 and slice s2 0 l2 == s2 (when l1 = length s1, l2 = length s2)
let slice_full (s: Seq.seq int)
  : Lemma (Seq.equal (Seq.slice s 0 (Seq.length s)) s)
          [SMTPat (Seq.slice s 0 (Seq.length s))]
  = ()

// Suffix -> head gives the value at position k in ghost_merged
let suffix_gives_index (merged: Seq.seq int) (k: nat) (suffix: Seq.seq int)
  : Lemma (requires k < Seq.length merged /\
                     Seq.equal suffix (Seq.slice merged k (Seq.length merged)) /\
                     Seq.length suffix > 0)
          (ensures Seq.head suffix == Seq.index merged k)
  = ()

#pop-options

// ================================================================
// Helper: copy range between arrays
// ================================================================

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"

fn copy_range
  (src dst: array int)
  (src_lo dst_lo len: SZ.t)
  (#s_src #s_dst: Ghost.erased (Seq.seq int))
  requires 
    pts_to_range src (SZ.v src_lo) (SZ.v src_lo + SZ.v len) s_src **
    pts_to_range dst (SZ.v dst_lo) (SZ.v dst_lo + SZ.v len) s_dst
  ensures
    pts_to_range src (SZ.v src_lo) (SZ.v src_lo + SZ.v len) s_src **
    pts_to_range dst (SZ.v dst_lo) (SZ.v dst_lo + SZ.v len) s_src
{
  pts_to_range_prop src;
  pts_to_range_prop dst;
  let mut i = 0sz;
  while (!i <^ len)
  invariant exists* vi s_cur.
    R.pts_to i vi **
    pts_to_range src (SZ.v src_lo) (SZ.v src_lo + SZ.v len) s_src **
    pts_to_range dst (SZ.v dst_lo) (SZ.v dst_lo + SZ.v len) s_cur **
    pure (
      SZ.v vi <= SZ.v len /\
      Seq.length s_cur == SZ.v len /\
      Seq.length s_src == SZ.v len /\
      (forall (k: nat). k < SZ.v vi ==> Seq.index s_cur k == Seq.index s_src k) /\
      (forall (k: nat). SZ.v vi <= k /\ k < SZ.v len ==> Seq.index s_cur k == Seq.index s_dst k)
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !i)
  {
    let vi = !i;
    let v = pts_to_range_index src (src_lo +^ vi);
    pts_to_range_upd dst (dst_lo +^ vi) v;
    i := vi +^ 1sz;
  };
  // After loop, s_cur agrees with s_src on all indices
  with s_final. assert (pts_to_range dst (SZ.v dst_lo) (SZ.v dst_lo + SZ.v len) s_final);
  assert (pure (forall (k:nat). k < Seq.length s_final ==> Seq.index s_final k == Seq.index s_src k));
  assert (pure (Seq.equal s_final s_src));
  ()
}

#pop-options

// ================================================================
// Ghost tick counter for complexity tracking
// ================================================================

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// Comparison cost bound: 0 for trivial inputs, merge_sort_ops for n >= 1
let ms_cost (len: int) : nat = if len <= 0 then 0 else merge_sort_ops len

let ms_cost_split (n: int{n >= 2})
  : Lemma (ensures ms_cost (n / 2) + ms_cost (n - n / 2) + n <= ms_cost n)
  = merge_sort_ops_split n

// Complexity bound predicates (avoids BoundedIntegers issues in Pulse ensures)
let merge_complexity_bounded (cf c0: nat) (lo hi: nat) : prop =
  lo <= hi /\ cf >= c0 /\ cf - c0 <= hi - lo

let sort_complexity_bounded (cf c0: nat) (lo hi: nat) : prop =
  lo <= hi /\ cf >= c0 /\ cf - c0 <= ms_cost (hi - lo)

// ================================================================
// Merge Implementation
// ================================================================

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"

// Key lemma: seq_merge (slice s1 0 (i+1)) (slice s2 0 j)
// when s1[i] <= all remaining s2[j..], equals
// (seq_merge (slice s1 0 i) (slice s2 0 j)) ++ [s1[i]]
// This is used in the merge loop invariant maintenance.

// Simpler approach: the merge loop output should match seq_merge s1 s2
// element by element. We prove a lemma that characterizes the next element.

// Helper: seq_merge picks elements in a specific order from s1, s2
// We track which indices have been consumed from each side.

// Even simpler: just prove the output is a permutation + sorted separately.
// The merge loop maintains:
// 1. Elements written so far are sorted
// 2. Elements written are from s1 and s2 (permutation of consumed parts)
// 3. All written elements <= all remaining elements

//SNIPPET_START: merge_sig
fn merge
  (a: array int) (lo mid hi: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  (#s1 #s2: Ghost.erased (Seq.seq int))
  requires 
    pts_to_range a (SZ.v lo) (SZ.v mid) s1 **
    pts_to_range a (SZ.v mid) (SZ.v hi) s2 **
    GR.pts_to ctr c0 **
    pure (SZ.v lo <= SZ.v mid /\ SZ.v mid <= SZ.v hi /\ sorted s1 /\ sorted s2)
  ensures exists* s_out (cf: nat).
    pts_to_range a (SZ.v lo) (SZ.v hi) s_out **
    GR.pts_to ctr cf **
    pure (
      sorted s_out /\ 
      permutation (Seq.append s1 s2) s_out /\
      merge_complexity_bounded cf (reveal c0) (SZ.v lo) (SZ.v hi)
    )
//SNIPPET_END: merge_sig
{
  pts_to_range_prop a #(SZ.v lo) #(SZ.v mid);
  pts_to_range_prop a #(SZ.v mid) #(SZ.v hi);
  
  let l1 = mid -^ lo;
  let l2 = hi -^ mid;
  
  // Allocate temp copies (heap-allocated)
  let tmp1_v = V.alloc 0 l1;
  V.to_array_pts_to tmp1_v;
  let tmp1 = V.vec_to_array tmp1_v;
  rewrite (A.pts_to (V.vec_to_array tmp1_v) (Seq.create (SZ.v l1) 0))
       as (A.pts_to tmp1 (Seq.create (SZ.v l1) 0));
  let tmp2_v = V.alloc 0 l2;
  V.to_array_pts_to tmp2_v;
  let tmp2 = V.vec_to_array tmp2_v;
  rewrite (A.pts_to (V.vec_to_array tmp2_v) (Seq.create (SZ.v l2) 0))
       as (A.pts_to tmp2 (Seq.create (SZ.v l2) 0));
  
  // Copy s1 into tmp1
  pts_to_range_intro tmp1 1.0R (Seq.create (SZ.v l1) 0);
  copy_range a tmp1 lo 0sz l1;
  pts_to_range_elim tmp1 1.0R (reveal s1);
  
  // Copy s2 into tmp2  
  pts_to_range_intro tmp2 1.0R (Seq.create (SZ.v l2) 0);
  copy_range a tmp2 mid 0sz l2;
  pts_to_range_elim tmp2 1.0R (reveal s2);
  
  // Join array range for writing
  pts_to_range_join a (SZ.v lo) (SZ.v mid) (SZ.v hi);
  
  // Ghost: compute the target merged sequence
  let ghost_merged : Ghost.erased (Seq.seq int) = Ghost.hide (seq_merge s1 s2);
  seq_merge_length s1 s2;
  
  // Merge loop: write seq_merge s1 s2 into the array
  let mut i = 0sz;  // index into tmp1
  let mut j = 0sz;  // index into tmp2
  let mut k = 0sz;  // write position (offset from lo)
  
  while (!i <^ l1 || !j <^ l2)
  invariant exists* vi vj vk s_cur (vc: nat).
    R.pts_to i vi **
    R.pts_to j vj **
    R.pts_to k vk **
    A.pts_to tmp1 (reveal s1) **
    A.pts_to tmp2 (reveal s2) **
    pts_to_range a (SZ.v lo) (SZ.v hi) s_cur **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v l1 /\
      SZ.v vj <= SZ.v l2 /\
      SZ.v vk == SZ.v vi + SZ.v vj /\
      Seq.length s_cur == SZ.v l1 + SZ.v l2 /\
      // First k positions match the ghost merged sequence
      (forall (p: nat). p < SZ.v vk ==> 
        Seq.index s_cur p == Seq.index ghost_merged p) /\
      // The remaining elements to merge are the suffixes
      Seq.equal (Seq.slice ghost_merged (SZ.v vk) (Seq.length ghost_merged))
               (seq_merge (Seq.slice s1 (SZ.v vi) (SZ.v l1)) (Seq.slice s2 (SZ.v vj) (SZ.v l2))) /\
      // Complexity: comparisons so far <= elements written
      merge_complexity_bounded vc (reveal c0) 0 (SZ.v vk)
    )
  decreases Prims.op_Addition (SZ.v l1 `Prims.op_Subtraction` SZ.v !i)
                               (SZ.v l2 `Prims.op_Subtraction` SZ.v !j)
  {
    let vi = !i;
    let vj = !j;
    let vk = !k;
    
    if (vi = l1) {
      // Left exhausted, take from right
      suffix_step_right s1 s2 (SZ.v vi) (SZ.v l1) (SZ.v vj) (SZ.v l2);
      let v = tmp2.(vj);
      pts_to_range_upd a (lo +^ vk) v;
      j := vj +^ 1sz;
      k := vk +^ 1sz;
    } else {
     if (vj = l2) {
      // Right exhausted, take from left
      suffix_step_left s1 s2 (SZ.v vi) (SZ.v l1) (SZ.v vj) (SZ.v l2);
      let v = tmp1.(vi);
      pts_to_range_upd a (lo +^ vk) v;
      i := vi +^ 1sz;
      k := vk +^ 1sz;
     } else {
      let v1 = tmp1.(vi);
      let v2 = tmp2.(vj);
      tick ctr;  // one comparison
      if (v1 <= v2) {
        suffix_step_left s1 s2 (SZ.v vi) (SZ.v l1) (SZ.v vj) (SZ.v l2);
        pts_to_range_upd a (lo +^ vk) v1;
        i := vi +^ 1sz;
        k := vk +^ 1sz;
      } else {
        suffix_step_right s1 s2 (SZ.v vi) (SZ.v l1) (SZ.v vj) (SZ.v l2);
        pts_to_range_upd a (lo +^ vk) v2;
        j := vj +^ 1sz;
        k := vk +^ 1sz;
      };
     };
    };
  };
  
  with s_final. assert (pts_to_range a (SZ.v lo) (SZ.v hi) s_final);
  assert (pure (Seq.equal s_final (reveal ghost_merged)));
  
  rewrite (A.pts_to tmp1 (reveal s1))
       as (A.pts_to (V.vec_to_array tmp1_v) (reveal s1));
  V.to_vec_pts_to tmp1_v;
  V.free tmp1_v;
  rewrite (A.pts_to tmp2 (reveal s2))
       as (A.pts_to (V.vec_to_array tmp2_v) (reveal s2));
  V.to_vec_pts_to tmp2_v;
  V.free tmp2_v;
  
  seq_merge_sorted s1 s2;
  seq_merge_permutation s1 s2;
  ()
}

#pop-options

// ================================================================
// Recursive Merge Sort
// ================================================================

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"

fn rec merge_sort_aux
  (a: array int)
  (lo hi: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  (#s: Ghost.erased (Seq.seq int))
  requires 
    pts_to_range a (SZ.v lo) (SZ.v hi) s **
    GR.pts_to ctr c0
  ensures exists* s' (cf: nat).
    pts_to_range a (SZ.v lo) (SZ.v hi) s' **
    GR.pts_to ctr cf **
    pure (sorted s' /\ permutation s s' /\
          sort_complexity_bounded cf (reveal c0) (SZ.v lo) (SZ.v hi))
{
  pts_to_range_prop a;
  let len = hi -^ lo;
  if (len <^ 2sz) {
    singl_sorted s;
    permutation_refl s;
    ()
  } else {
    let mid = lo +^ (len /^ 2sz);
    
    pts_to_range_split a (SZ.v lo) (SZ.v mid) (SZ.v hi);
    with s1. assert (pts_to_range a (SZ.v lo) (SZ.v mid) s1);
    with s2. assert (pts_to_range a (SZ.v mid) (SZ.v hi) s2);
    
    // Sort left half
    merge_sort_aux a lo mid ctr;
    with s1'. assert (pts_to_range a (SZ.v lo) (SZ.v mid) s1');
    
    // Sort right half
    merge_sort_aux a mid hi ctr;
    with s2'. assert (pts_to_range a (SZ.v mid) (SZ.v hi) s2');
    
    // s = s1 ++ s2, s1 ~ s1', s2 ~ s2'
    // So s1 ++ s2 ~ s1' ++ s2'
    append_permutations s1 s2 s1' s2';
    
    // Merge sorted halves
    merge a lo mid hi ctr;
    // Result is seq_merge s1' s2' which is sorted and 
    // permutation (append s1' s2') (seq_merge s1' s2')
    // Compose: s ~ s1++s2 ~ s1'++s2' ~ result
    
    // Complexity: left + right + merge <= ms_cost(len)
    ms_cost_split (SZ.v hi - SZ.v lo);
    ()
  }
}

#pop-options

// ================================================================
// Top-Level Entry Point
// ================================================================

//SNIPPET_START: merge_sort_sig
fn merge_sort
  (a: A.array int)
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  (#s0: erased (Seq.seq int))
requires
  A.pts_to a s0 **
  GR.pts_to ctr c0 **
  pure (
    SZ.v len == Seq.length s0 /\ 
    SZ.v len == A.length a
  )
ensures exists* s (cf: nat).
  A.pts_to a s **
  GR.pts_to ctr cf **
  pure (
    Seq.length s == Seq.length s0 /\
    sorted s /\
    permutation s0 s /\
    sort_complexity_bounded cf (reveal c0) 0 (SZ.v len)
  )
//SNIPPET_END: merge_sort_sig
{
  if (len <=^ 1sz) {
    singl_sorted s0;
    permutation_refl s0;
    ()
  } else {
    pts_to_range_intro a 1.0R (reveal s0);
    
    merge_sort_aux a 0sz len ctr;
    
    with s'. assert (pts_to_range a 0 (SZ.v len) s');
    rewrite (pts_to_range a 0 (SZ.v len) s')
        as (pts_to_range a 0 (A.length a) s');
    pts_to_range_elim a 1.0R s';
    ()
  }
}
