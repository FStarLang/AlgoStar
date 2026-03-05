(*
   Huffman Codec — Pulse Implementation Interface

   Imperative decode on heap-allocated Huffman trees,
   with proofs connecting to the pure Codec specifications.

   NO admits. NO assumes.
*)
module CLRS.Ch16.Huffman.Codec.Impl
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Box = Pulse.Lib.Box
module G = FStar.Ghost
module HSpec = CLRS.Ch16.Huffman.Spec
module HCodec = CLRS.Ch16.Huffman.Codec
open CLRS.Ch16.Huffman.Defs
open CLRS.Ch16.Huffman.Impl

// Convert a contiguous slice [lo..hi) of a bool sequence to a list.
let rec bits_as_list (s: Seq.seq bool) (lo hi: nat)
  : Tot (list bool) (decreases (if hi > lo && lo < Seq.length s then hi - lo else 0))
  = if lo >= hi || lo >= Seq.length s then []
    else Seq.index s lo :: bits_as_list s (lo + 1) hi

val bits_as_list_cons (s: Seq.seq bool) (lo hi: nat)
  : Lemma (requires lo < hi /\ hi <= Seq.length s)
          (ensures bits_as_list s lo hi == Seq.index s lo :: bits_as_list s (lo + 1) hi)

val bits_as_list_length (s: Seq.seq bool) (lo hi: nat)
  : Lemma (requires hi <= Seq.length s /\ lo <= hi)
          (ensures FStar.List.Tot.length (bits_as_list s lo hi) == hi - lo)

/// Decode one symbol by walking the heap tree from `cur` to a leaf.
/// The tree is preserved (read-only).  Returns (symbol, new_bit_position).
fn decode_step_impl
  (cur: hnode_ptr) (ft: HSpec.htree)
  (bits: A.array bool) (pos bit_len: SZ.t)
  (#bits_seq: G.erased (Seq.seq bool))
  requires is_htree cur ft ** A.pts_to bits bits_seq **
           pure (SZ.v pos <= SZ.v bit_len /\
                 SZ.v bit_len <= Seq.length bits_seq /\
                 Some? (HCodec.decode_step ft (bits_as_list bits_seq (SZ.v pos) (SZ.v bit_len))))
  returns result: (int & SZ.t)
  ensures is_htree cur ft ** A.pts_to bits bits_seq **
          pure (Some? (HCodec.decode_step ft (bits_as_list bits_seq (SZ.v pos) (SZ.v bit_len))) /\
                (let ds = Some?.v (HCodec.decode_step ft (bits_as_list bits_seq (SZ.v pos) (SZ.v bit_len))) in
                 fst result == fst ds /\
                 SZ.v pos <= SZ.v (snd result) /\ SZ.v (snd result) <= SZ.v bit_len /\
                 snd ds == bits_as_list bits_seq (SZ.v (snd result)) (SZ.v bit_len)))
