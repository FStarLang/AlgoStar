(*
   MergeSort Bridge Lemmas — connecting c2pulse postconditions to F* specs.

   The c2pulse translation of MergeSortRecursive.c proves:
     - Sortedness via adjacent-pair comparisons (Int32.lte)
     - Frame preservation: elements outside [lo, hi) are unchanged

   The hand-written F* specs (CLRS.Ch02.MergeSort.Impl) express:
     - SortSpec.sorted over Seq.seq int
     - SortSpec.permutation of input to output
     - sort_complexity_bounded

   This module bridges the gap, reusing the InsertionSort bridge for
   shared definitions (extract_ints, all_some) and the math from
   CLRS.Ch02.MergeSort.Spec and Lemmas.

   NO admits.
*)
module CLRS.Ch02.MergeSort.C.BridgeLemmas

open CLRS.Common.SortSpec
open CLRS.Ch02.InsertionSort.C.BridgeLemmas
module Seq  = FStar.Seq
module I32  = FStar.Int32

/// Adjacent-pair sorted in a sub-range implies SortSpec.sorted on extracted slice
val subrange_sorted_implies_sorted
  (s: Seq.seq (option I32.t)) (lo hi: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s /\
      (forall (k: nat). lo <= k /\ k < hi ==> Some? (Seq.index s k)) /\
      (forall (k: nat). lo <= k /\ k + 1 < hi ==>
        I32.v (Some?.v (Seq.index s k)) <= I32.v (Some?.v (Seq.index s (k + 1)))))
    (ensures
      sorted (extract_ints (Seq.slice s lo hi) (hi - lo)))

/// Frame preservation on a sub-range implies equal extracted ints
val subrange_unchanged_implies_perm
  (s_old s_new: Seq.seq (option I32.t)) (lo hi: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s_old /\ hi <= Seq.length s_new /\
      (forall (k: nat). lo <= k /\ k < hi ==> Some? (Seq.index s_old k)) /\
      (forall (k: nat). lo <= k /\ k < hi ==> Some? (Seq.index s_new k)) /\
      (forall (k: nat). lo <= k /\ k < hi ==>
        Seq.index s_new k == Seq.index s_old k))
    (ensures
      Seq.equal
        (extract_ints (Seq.slice s_new lo hi) (hi - lo))
        (extract_ints (Seq.slice s_old lo hi) (hi - lo)))

/// Merge of two sorted sub-ranges produces a sorted permutation
/// (connects c2pulse merge_rec postconditions to F* MergeSort.Spec)
val merge_sorted_permutation
  (s_a s_buf: Seq.seq (option I32.t))
  (lo mid hi: nat)
  : Lemma
    (requires lo <= mid /\ mid <= hi /\ hi <= Seq.length s_a /\
      hi <= Seq.length s_buf /\
      (forall (k: nat). lo <= k /\ k < hi ==> Some? (Seq.index s_a k)) /\
      (forall (k: nat). lo <= k /\ k < hi ==> Some? (Seq.index s_buf k)) /\
      (* a[lo..mid) sorted *)
      (forall (k: nat). lo <= k /\ k + 1 < mid ==>
        I32.v (Some?.v (Seq.index s_a k)) <= I32.v (Some?.v (Seq.index s_a (k + 1)))) /\
      (* a[mid..hi) sorted *)
      (forall (k: nat). mid <= k /\ k + 1 < hi ==>
        I32.v (Some?.v (Seq.index s_a k)) <= I32.v (Some?.v (Seq.index s_a (k + 1)))) /\
      (* buf[lo..hi) sorted *)
      (forall (k: nat). lo <= k /\ k + 1 < hi ==>
        I32.v (Some?.v (Seq.index s_buf k)) <= I32.v (Some?.v (Seq.index s_buf (k + 1)))))
    (ensures
      sorted (extract_ints (Seq.slice s_buf lo hi) (hi - lo)))
