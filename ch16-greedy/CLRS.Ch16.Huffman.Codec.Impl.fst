(*
   Huffman Codec — Pulse Implementation

   Imperative encode/decode on heap-allocated Huffman trees,
   with proofs connecting to the pure Codec round-trip theorems.

   The tree is read-only during encode/decode (preserved via is_htree).

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
module R = Pulse.Lib.Reference
module L = FStar.List.Tot
module HSpec = CLRS.Ch16.Huffman.Spec
module HCodec = CLRS.Ch16.Huffman.Codec
open CLRS.Ch16.Huffman.Defs
open CLRS.Ch16.Huffman.Impl

// ========== Seq-to-list bridge ==========

// bits_as_list defined in .fsti

let bits_as_list_cons (s: Seq.seq bool) (lo hi: nat)
  : Lemma (requires lo < hi /\ hi <= Seq.length s)
          (ensures bits_as_list s lo hi == Seq.index s lo :: bits_as_list s (lo + 1) hi)
  = ()

let rec bits_as_list_length (s: Seq.seq bool) (lo hi: nat)
  : Lemma (requires hi <= Seq.length s /\ lo <= hi)
          (ensures L.length (bits_as_list s lo hi) == hi - lo)
          (decreases hi - lo)
  = if lo >= hi then () else bits_as_list_length s (lo + 1) hi

// ========== decode_step_impl ==========

// Decode one symbol by walking the heap tree from `cur` to a leaf.
// `ft` is the spec-level tree (needed for proof; erased at extraction).
// Returns (symbol, new_bit_position).
#push-options "--z3rlimit 40 --split_queries always"
fn rec decode_step_impl
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
  decreases ft
{
  match ft {
    HSpec.Leaf s f -> {
      elim_is_htree_leaf cur s f;
      let node = Box.op_Bang cur;
      intro_is_htree_leaf cur s f;
      rewrite (is_htree cur (HSpec.Leaf s f)) as (is_htree cur ft);
      HCodec.decode_step_leaf s f (bits_as_list bits_seq (SZ.v pos) (SZ.v bit_len));
      (node.sym, pos)
    }
    HSpec.Internal f l r -> {
      elim_is_htree_internal cur f l r;
      with lp rp. _;
      let node = Box.op_Bang cur;
      // Prove pos < bit_len (decode_step on Internal needs non-empty bits)
      bits_as_list_length bits_seq (SZ.v pos) (SZ.v bit_len);
      HCodec.decode_step_internal_nil f l r;
      let b = A.op_Array_Access bits pos;
      bits_as_list_cons bits_seq (SZ.v pos) (SZ.v bit_len);
      HCodec.decode_step_internal f l r b (bits_as_list bits_seq (SZ.v pos + 1) (SZ.v bit_len));
      let new_pos = pos +^ 1sz;
      if b {
        let lp_rt = Some?.v node.left;
        rewrite (is_htree lp l) as (is_htree lp_rt l);
        let result = decode_step_impl lp_rt l bits new_pos bit_len;
        rewrite (is_htree lp_rt l) as (is_htree lp l);
        intro_is_htree_internal cur lp rp f l r;
        rewrite (is_htree cur (HSpec.Internal f l r)) as (is_htree cur ft);
        result
      } else {
        let rp_rt = Some?.v node.right;
        rewrite (is_htree rp r) as (is_htree rp_rt r);
        let result = decode_step_impl rp_rt r bits new_pos bit_len;
        rewrite (is_htree rp_rt r) as (is_htree rp r);
        intro_is_htree_internal cur lp rp f l r;
        rewrite (is_htree cur (HSpec.Internal f l r)) as (is_htree cur ft);
        result
      }
    }
  }
}
#pop-options
