(*
   Huffman Tree Construction — Spec Validation Test

   Validates the Impl.fsti API for CLRS §16.3 HUFFMAN by calling
   huffman_tree on a small concrete instance and proving that the
   postcondition properties (cost, multiset, optimality, complexity)
   are precise and useful.

   Test instance: frequencies [3; 5] (n=2)
     Expected: a tree with cost = 8, same_frequency_multiset, is_wpl_optimal,
     and exactly 1 merge iteration.

   Attribution: Pattern inspired by
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   NO admits. NO assumes.
*)
module CLRS.Ch16.Huffman.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch16.Huffman.Impl
open CLRS.Ch16.Huffman.Defs

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference
module HSpec = CLRS.Ch16.Huffman.Spec
module HOpt = CLRS.Ch16.Huffman.Optimality
module HCmplx = CLRS.Ch16.Huffman.Complexity

(* ---------- Pure helpers ---------- *)

noextract
let freq_seq2 : Seq.seq int = Seq.seq_of_list [3; 5]

(* greedy_cost [3; 5] == 8 *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let greedy_cost_3_5 ()
  : Lemma (HOpt.greedy_cost [3; 5] == 8)
  = HOpt.greedy_cost_singleton 8;
    HOpt.greedy_cost_sorted_unfold [3; 5]
#pop-options

(* seq_to_pos_list has same multiset as [3; 5] when input is [3; 5] *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 40"
let seq_to_pos_list_freqseq2 (x: pos)
  : Lemma (FStar.List.Tot.count x (seq_to_pos_list freq_seq2 0) ==
           FStar.List.Tot.count x [3; 5])
  = seq_to_pos_list_length freq_seq2 0;
    // seq_to_pos_list freq_seq2 0 has length 2
    // Direct computation via normalization of small steps
    assert_norm (Seq.length freq_seq2 == 2);
    assert_norm (Seq.index freq_seq2 0 == 3);
    assert_norm (Seq.index freq_seq2 1 == 5)
#pop-options

(* greedy_cost of seq_to_pos_list is also 8 *)
let greedy_cost_input_8 ()
  : Lemma (HOpt.greedy_cost (seq_to_pos_list freq_seq2 0) == 8)
  = Classical.forall_intro seq_to_pos_list_freqseq2;
    HOpt.greedy_cost_multiset_invariant (seq_to_pos_list freq_seq2 0) [3; 5];
    greedy_cost_3_5 ()

(* The postcondition tells us cost ft == 8 and exactly 1 merge *)
let post_implies_cost_8 (ft: HSpec.htree) (cf: nat)
  : Lemma
    (requires HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list freq_seq2 0) /\
             HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq2 0) /\
             HSpec.is_wpl_optimal ft (seq_to_pos_list freq_seq2 0) /\
             HCmplx.huffman_merge_bound cf 0 2)
    (ensures HSpec.cost ft == 8 /\ cf == 1)
  = greedy_cost_input_8 ()

(* The new tree_leaf_labels_valid postcondition constrains leaf symbols:
   for any leaf (s, f) in the tree, s < 2 and freq_seq2[s] == f.
   Since freq_seq2 = [3; 5], this means:
     - any leaf with freq 3 has sym 0
     - any leaf with freq 5 has sym 1
   This proves the tree correctly maps symbols to frequencies. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let leaf_labels_constrain_syms (ft: HSpec.htree) (s: nat) (f: pos)
  : Lemma
    (requires tree_leaf_labels_valid ft freq_seq2 /\
             FStar.List.Tot.mem (s, f) (HSpec.leaf_labels ft))
    (ensures s < 2 /\ Seq.index freq_seq2 s == f /\
             (f == 3 ==> s == 0) /\
             (f == 5 ==> s == 1))
  = assert_norm (Seq.length freq_seq2 == 2);
    assert_norm (Seq.index freq_seq2 0 == 3);
    assert_norm (Seq.index freq_seq2 1 == 5)
#pop-options

(* ---------- Main Test ---------- *)

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
```pulse
fn test_huffman_2 ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // --- Allocate frequencies = [3; 5] ---
  let fv = V.alloc 0 2sz;
  V.to_array_pts_to fv;
  let freqs = V.vec_to_array fv;
  rewrite (A.pts_to (V.vec_to_array fv) (Seq.create 2 0))
       as (A.pts_to freqs (Seq.create 2 0));
  freqs.(0sz) <- 3;
  freqs.(1sz) <- 5;

  // --- Ghost counter ---
  let ctr = GR.alloc #nat 0;
  
  // --- Bind ghost sequence ---
  with s0. assert (A.pts_to freqs s0);

  // --- Call huffman_tree ---
  let tree_ptr = huffman_tree freqs 2sz ctr;

  // --- Read postcondition ---
  with ft (cf: nat). assert (
    is_htree tree_ptr ft **
    GR.pts_to ctr cf **
    pure (HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list s0 0) /\
          HSpec.same_frequency_multiset ft (seq_to_pos_list s0 0) /\
          HSpec.is_wpl_optimal ft (seq_to_pos_list s0 0) /\
          HCmplx.huffman_merge_bound cf 0 2 /\
          tree_leaf_labels_valid ft s0)
  );

  // --- Prove cost == 8 and merge count == 1 ---
  post_implies_cost_8 ft cf;
  assert (pure (HSpec.cost ft == 8));
  assert (pure (cf == 1));

  // --- Prove leaf symbol mapping is correct ---
  assert (pure (tree_leaf_labels_valid ft s0));

  // --- Drop tree (ghost ft prevents calling free_htree) ---
  drop_ (is_htree tree_ptr ft);
  
  // --- Runtime check: verify input array is preserved (survives extraction) ---
  let f0 = freqs.(0sz);
  let f1 = freqs.(1sz);
  assert (pure (f0 == 3));
  assert (pure (f1 == 5));
  let pass = (f0 = 3) && (f1 = 5);

  with s_final. assert (A.pts_to freqs s_final);
  rewrite (A.pts_to freqs s_final) as (A.pts_to (V.vec_to_array fv) s_final);
  V.to_vec_pts_to fv;
  V.free fv;

  GR.free ctr;
  pass
}
```
#pop-options
