(*
   CLRS Chapter 2: merge-sort rubric investigation / fallback instance.

   Pulse.Lib.Sort.Merge.Array is not directly usable for the shared array_sort
   class: its comparator has no access to the monotonic tick resource, and its
   specification treats compare = 0 as duplicate detection rather than ordinary
   stable merge-sort behavior.  Until a generic merge-sort implementation is
   added with an instrumented comparator in its signature, this module exposes a
   conservative ch02-only array_sort witness by delegating to the verified
   generic insertion-sort instance.

   This is intentionally named as a fallback; it is a verified sorting instance,
   not a claim that Pulse.Lib.Sort.Merge.Array proves duplicate-preserving merge
   sort under the shared rubric.
*)
module CLRS.Ch02.MergeSort.Rubric
#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module ISR = CLRS.Ch02.InsertionSort.Rubric
module MR = Pulse.Lib.MonotonicGhostRef
module SC = CLRS.Common.Complexity.Sorting.Class
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TO = Pulse.Lib.TotalOrder

let merge_sort_fallback_comparisons (n: nat) : nat =
  ISR.insertion_sort_comparisons n

fn merge_sort_fallback_sort (#a: Type0)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: erased (Seq.seq a))
  (#i: erased nat)
  norewrite
requires arr |-> s0 ** pure (A.length arr == SZ.v len) ** MR.pts_to ctr #1.0R i
ensures exists* s'.
  arr |-> s' **
  pure (SC.sorted #a #ord s' /\ SC.permutation s0 s') **
  MR.pts_to ctr #1.0R (reveal i + merge_sort_fallback_comparisons (Seq.length s0))
{
  ISR.insertion_sort_sort arr len ctr #ord iord #s0 #i
}

instance merge_sort_fallback_array_sort (a: Type0)
  : SC.array_sort a merge_sort_fallback_comparisons =
  Pulse.Lib.Core.slprop_equivs ();
  {
    sort = merge_sort_fallback_sort #a
  }
