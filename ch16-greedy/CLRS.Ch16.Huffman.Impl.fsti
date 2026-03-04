(*
   Huffman Coding — Implementation Interface

   Public API signature for the verified Huffman tree construction
   algorithm (CLRS §16.3, HUFFMAN).

   Postconditions guarantee:
   - Functional correctness: same_frequency_multiset
   - Optimality: is_wpl_optimal (weighted path length)
   - Cost equality: cost == greedy_cost of input frequencies
*)
module CLRS.Ch16.Huffman.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Box = Pulse.Lib.Box
module HSpec = CLRS.Ch16.Huffman.Spec
module HOpt = CLRS.Ch16.Huffman.Optimality
open CLRS.Ch16.Huffman.Defs

/// Recursive separation logic predicate: relates a heap-allocated tree to a spec tree.
val is_htree (p: hnode_ptr) (ft: HSpec.htree) : Tot slprop

/// Free a heap-allocated Huffman tree, reclaiming all memory.
fn free_htree (p: hnode_ptr) (ft: HSpec.htree)
  requires is_htree p ft
  ensures emp

//SNIPPET_START: huffman_tree_iface
/// Build an optimal Huffman tree from an array of positive frequencies.
/// The result is a heap-allocated tree satisfying WPL-optimality.
fn huffman_tree
  (freqs: A.array int)
  (#freq_seq: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires A.pts_to freqs freq_seq ** pure (
    SZ.v n == Seq.length freq_seq /\
    SZ.v n > 0 /\
    SZ.fits (2 * SZ.v n + 2) /\
    (forall (i: nat). i < Seq.length freq_seq ==> Seq.index freq_seq i > 0))
  returns result: hnode_ptr
  ensures A.pts_to freqs freq_seq **
          (exists* ft. is_htree result ft **
                  pure (HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list freq_seq 0) /\
                        HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0) /\
                        HSpec.is_wpl_optimal ft (seq_to_pos_list freq_seq 0)))
//SNIPPET_END: huffman_tree_iface
