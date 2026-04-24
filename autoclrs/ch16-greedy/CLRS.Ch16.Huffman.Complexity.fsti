(*
   Huffman Coding — Complexity Interface

   O(n²) complexity bound for the sorted-list Huffman construction.
   Each of n-1 merge iterations uses O(n) comparisons for sorted insertion.
   Total: ≤ n² comparisons.

   With a min-heap (as in the Pulse implementation), the complexity is
   O(n lg n), but that bound is not formally proven here.
*)
module CLRS.Ch16.Huffman.Complexity

open FStar.List.Tot
open CLRS.Ch16.Huffman.Spec

/// Count comparisons in insert_sorted
val insert_sorted_ticks (t: htree) (l: list htree) : Tot nat

/// insert_sorted_ticks is bounded by list length
val insert_sorted_ticks_bounded (t: htree) (l: list htree)
  : Lemma (ensures insert_sorted_ticks t l <= length l)

/// Build Huffman tree with tick counting (returns tree and total ticks)
val huffman_with_ticks (l: list htree{Cons? l}) : Tot (htree & nat)

/// Extract just the tick count
val huffman_ticks (l: list htree{Cons? l}) : nat

/// Helper: square function
let square (n: nat) : Tot nat = op_Star n n

/// Key lemma: ticks bounded by n²
val huffman_ticks_bounded (l: list htree{Cons? l})
  : Lemma (ensures huffman_ticks l <= square (length l))

/// Main complexity theorem: O(n²) bound
val huffman_complexity (l: list htree{Cons? l})
  : Lemma (ensures huffman_ticks l <= square (length l))

/// Universally quantified form
val huffman_complexity_simple (n: nat{n >= 1})
  : Lemma (ensures (
      forall (l: list htree). 
        Cons? l /\ length l == n ==>
        huffman_ticks l <= square n
    ))

/// The trees built are the same (only ticks added)
val huffman_with_ticks_correct (l: list htree{Cons? l})
  : Lemma (ensures (
      let (tree_with_ticks, _) = huffman_with_ticks l in
      let tree_without_ticks = huffman_from_sorted l in
      tree_with_ticks == tree_without_ticks
    ))

/// Merge-iteration complexity bound for the PQ-based imperative implementation.
/// The Huffman algorithm performs exactly n-1 merge iterations (each merging
/// two minimum-frequency trees). With a min-heap PQ, each iteration does
/// O(log n) work, giving O(n log n) total.
let huffman_merge_bound (cf c0 n: nat) : prop =
  n > 0 /\ cf >= c0 /\ cf - c0 == n - 1
