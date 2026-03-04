(*
   CLRS Chapter 7: Partition — Complexity Proofs

   The Lomuto partition scans all n-1 non-pivot elements exactly once,
   performing one comparison per element. This gives exactly n-1 comparisons
   for an n-element sub-array, captured by complexity_exact_linear.

   This is proved inline in Partition.Impl via ghost tick counting.
   Here we state the standalone mathematical fact.

   NO admits. NO assumes.
*)
module CLRS.Ch07.Partition.Complexity

open CLRS.Ch07.Partition.Lemmas

let partition_comparisons_linear (n:nat{n > 0})
  : Lemma (ensures complexity_exact_linear (n - 1) 0 (n - 1))
  = ()
