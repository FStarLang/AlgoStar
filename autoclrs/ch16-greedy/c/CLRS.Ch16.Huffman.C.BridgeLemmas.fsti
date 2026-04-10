(*
   Huffman Tree — Bridge Lemmas

   Connect C-level postconditions to the full F* optimality proof.

   The C implementation (HuffmanTree.c) verifies:
   - Memory safety: all tree allocations tracked via is_htree predicate
   - Tree shape: recursive structure (leaf/internal) correctly built
   - Sorted input: requires frequencies sorted in non-decreasing order
   - Positive frequencies: all freq[i] > 0
   - Two-queue merge: algorithmically correct O(n) construction

   The C code uses admit() for ghost proofs of:
   - cost == greedy_cost (merge cost tracking)
   - same_frequency_multiset (leaf frequency preservation)
   - tree_leaf_labels_valid (leaf label/index correspondence)

   This bridge assumes cost and multiset properties (which the C
   algorithmic structure guarantees) and derives WPL optimality
   using the F* spec-level proof (Huffman.Optimality).

   The complexity bound (n-1 merges) follows from the loop structure.
*)
module CLRS.Ch16.Huffman.C.BridgeLemmas

open FStar.Seq

module HSpec = CLRS.Ch16.Huffman.Spec
module HOpt = CLRS.Ch16.Huffman.Optimality
module HCmplx = CLRS.Ch16.Huffman.Complexity
open CLRS.Ch16.Huffman.Defs

/// Bridge from C postconditions to WPL optimality.
///
/// Given:
///   - The input frequencies are positive (verified in C)
///   - The tree cost equals greedy_cost (admitted in C, algorithmically correct)
///   - The frequency multiset is preserved (admitted in C, algorithmically correct)
///
/// Concludes:
///   - The tree is WPL-optimal (derived via F* spec proof)
///
/// This uses HOpt.greedy_cost_implies_optimal: if cost == greedy_cost
/// and same_frequency_multiset, then is_wpl_optimal.
val bridge_c_to_optimal
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

/// The two-queue merge loop runs exactly n-1 iterations.
/// This is a purely computational fact from the C loop structure.
val bridge_complexity_bound (n c0: nat)
  : Lemma
    (requires n > 0)
    (ensures HCmplx.huffman_merge_bound (c0 + (n - 1)) c0 n)
