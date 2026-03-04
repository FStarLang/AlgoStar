(*
   Huffman Optimality — Interface

   Pure F* module for greedy cost infrastructure and the WPL optimality bridge.
   Provides `greedy_cost` (recursive definition) and lemmas connecting it to
   `Huffman.Complete.huffman_complete_optimal`.

   Key exports:
   - `greedy_cost`: Recursive greedy merging cost on a frequency list.
   - `greedy_cost_implies_optimal`: If `cost(ft) == greedy_cost(freqs)`, then
     `ft` is WPL-optimal.
   - `greedy_cost_multiset_invariant`: Greedy cost is invariant under multiset
     equality.
   - `greedy_cost_unfold_with_mins`: Unfolds greedy cost by extracting two minima.
*)
module CLRS.Ch16.Huffman.Optimality

open FStar.List.Tot.Base
open FStar.List.Tot.Properties

module HSpec = CLRS.Ch16.Huffman.Spec
module HComp = CLRS.Ch16.Huffman.Complete

// ========== Comparison and sorting ==========

let pos_compare (a b: pos) : int = a - b

val sortWith_pos_length (l: list pos)
  : Lemma (ensures length (sortWith pos_compare l) = length l)

val sortWith_same_multiset (l1 l2: list pos)
  : Lemma (requires forall (x: pos). count x l1 = count x l2)
          (ensures sortWith pos_compare l1 == sortWith pos_compare l2)

// ========== Greedy cost ==========

val greedy_cost (freqs: list pos) : Tot nat

val greedy_cost_singleton (f: pos)
  : Lemma (greedy_cost [f] == 0)

val greedy_cost_multiset_invariant (l1 l2: list pos)
  : Lemma (requires forall (x: pos). count x l1 = count x l2)
          (ensures greedy_cost l1 == greedy_cost l2)

val greedy_cost_sorted_unfold (freqs: list pos)
  : Lemma (requires length freqs >= 2 /\ HComp.nondecreasing freqs)
          (ensures (let f1 :: f2 :: rest = freqs in
                    greedy_cost freqs == (f1 + f2) + greedy_cost ((f1 + f2) :: rest)))

// ========== Bridge: greedy cost ↔ WPL optimality ==========

val huffman_complete_cost_eq_greedy (freqs: list pos{Cons? freqs})
  : Lemma (ensures HSpec.cost (HComp.huffman_complete freqs) == greedy_cost freqs)

val cost_eq_implies_optimal (ft: HSpec.htree) (freqs: list pos{Cons? freqs})
  : Lemma (requires HSpec.same_frequency_multiset ft freqs /\
                    HSpec.cost ft == HSpec.cost (HComp.huffman_complete freqs))
          (ensures HSpec.is_wpl_optimal ft freqs)

val greedy_cost_implies_optimal (ft: HSpec.htree) (freqs: list pos{Cons? freqs})
  : Lemma (requires HSpec.same_frequency_multiset ft freqs /\
                    HSpec.cost ft == greedy_cost freqs)
          (ensures HSpec.is_wpl_optimal ft freqs)

// ========== Greedy cost merge step ==========

val greedy_cost_unfold_with_mins (freqs: list pos) (f1 f2: pos) (remaining: list pos)
  : Lemma (requires
      length freqs >= 2 /\
      (forall x. mem x freqs ==> f1 <= x) /\
      (forall (x: pos). count x freqs = (if x = f1 then 1 else 0) +
                                    (if x = f2 then 1 else 0) +
                                    count x remaining) /\
      (forall x. mem x remaining ==> f2 <= x))
    (ensures greedy_cost freqs == (f1 + f2) + greedy_cost ((f1 + f2) :: remaining))
