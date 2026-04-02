(*
   Merge Sort - Verified implementation in Pulse
    
   A genuine top-down merge sort that:
   1. Divides the array in half
   2. Recursively sorts each half
   3. Merges the sorted halves

   Proves:
   1. The result is sorted
   2. The result is a permutation of the input
   3. O(n log n) comparison complexity (ghost tick counter linked to merge_sort_ops)
    
   NO admits. NO assumes.
*)

module CLRS.Ch02.MergeSort.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Array.PtsToRange
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open CLRS.Common.SortSpec
open CLRS.Common.Complexity
open CLRS.Ch02.MergeSort.Spec
open CLRS.Ch02.MergeSort.Lemmas
open CLRS.Ch02.MergeSort.Complexity

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ================================================================
// Helper: copy range between arrays
// ================================================================

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"

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
  with s_final. assert (pts_to_range dst (SZ.v dst_lo) (SZ.v dst_lo + SZ.v len) s_final);
  assert (pure (forall (k:nat). k < Seq.length s_final ==> Seq.index s_final k == Seq.index s_src k));
  assert (pure (Seq.equal s_final s_src));
  ()
}

#pop-options

// ================================================================
// Merge Implementation
// ================================================================

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"

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
      if (Prims.op_LessThanOrEqual v1 v2) {
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

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

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
    Seq.length s0 <= A.length a
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
    pts_to_range_prop a;
    
    merge_sort_aux a 0sz len ctr;
    
    with s'. assert (pts_to_range a 0 (SZ.v len) s');
    rewrite (pts_to_range a 0 (SZ.v len) s')
        as (pts_to_range a 0 (A.length a) s');
    pts_to_range_elim a 1.0R s';
    ()
  }
}
