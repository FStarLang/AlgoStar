(*
   Huffman Tree — Bridge Lemmas (Implementation)

   Bridges C-level postconditions to the full F* optimality proof.
   See .fsti for documentation of proof strategy and assumptions.
*)
module CLRS.Ch16.Huffman.C.BridgeLemmas

open FStar.Seq

module HSpec = CLRS.Ch16.Huffman.Spec
module HOpt = CLRS.Ch16.Huffman.Optimality
module HCmplx = CLRS.Ch16.Huffman.Complexity
open CLRS.Ch16.Huffman.Defs

let bridge_c_to_optimal
  (freq_seq: seq int) (ft: HSpec.htree) (n: nat)
  : Lemma
    (requires
      n > 0 /\
      n == Seq.length freq_seq /\
      (forall (i: nat). i < n ==> Seq.index freq_seq i > 0) /\
      Cons? (seq_to_pos_list freq_seq 0) /\
      HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list freq_seq 0) /\
      HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0))
    (ensures
      HSpec.is_wpl_optimal ft (seq_to_pos_list freq_seq 0))
  =
    (* The cost equality and multiset preservation are given as
       preconditions (admitted in the C code, but algorithmically
       correct by the two-queue merge construction).

       The WPL optimality follows from greedy_cost_implies_optimal:
       if cost(ft) == greedy_cost(freqs) and same_frequency_multiset,
       then ft is WPL-optimal. *)
    HOpt.greedy_cost_implies_optimal ft (seq_to_pos_list freq_seq 0)

let bridge_complexity_bound (n c0: nat)
  : Lemma
    (requires n > 0)
    (ensures HCmplx.huffman_merge_bound (c0 + (n - 1)) c0 n)
  =
    (* huffman_merge_bound cf c0 n = n > 0 /\ cf >= c0 /\ cf - c0 == n - 1
       With cf = c0 + (n - 1), this is trivially satisfied. *)
    ()
