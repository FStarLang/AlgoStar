(*
   CLRS Chapter 7: Partition — Complexity Signatures

   The Lomuto partition on A[lo..hi) performs exactly hi-lo-1 = n-1
   comparisons for an n-element sub-array.
*)
module CLRS.Ch07.Partition.Complexity

open CLRS.Ch07.Partition.Lemmas

/// Partition performs exactly n-1 comparisons on an n-element sub-array.
/// Starting from counter 0, after n-1 ticks the exact linear bound holds.
val partition_comparisons_linear (n:nat{n > 0})
  : Lemma (ensures complexity_exact_linear (n - 1) 0 (n - 1))
