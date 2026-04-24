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

/// Full decoder: decode entire bitstring into an output array.
/// Postcondition: output matches pure decode result.
fn decode_impl
  (root: hnode_ptr) (ft: HSpec.htree)
  (bits: A.array bool) (bit_len: SZ.t)
  (output: A.array int) (out_len: SZ.t)
  (#bits_seq: G.erased (Seq.seq bool))
  (#out_seq0: G.erased (Seq.seq int))
  requires is_htree root ft ** A.pts_to bits bits_seq ** A.pts_to output out_seq0 **
           pure (HSpec.Internal? ft /\
                 SZ.v bit_len <= Seq.length bits_seq /\
                 Seq.length out_seq0 == SZ.v out_len /\
                 Some? (HCodec.decode ft (bits_as_list bits_seq 0 (SZ.v bit_len))) /\
                 FStar.List.Tot.length (Some?.v (HCodec.decode ft (bits_as_list bits_seq 0 (SZ.v bit_len)))) <= SZ.v out_len)
  returns msg_len: SZ.t
  ensures is_htree root ft ** A.pts_to bits bits_seq **
          (exists* out_seq'. A.pts_to output out_seq' **
          pure (let d = HCodec.decode ft (bits_as_list bits_seq 0 (SZ.v bit_len)) in
                Some? d /\
                (let msg = Some?.v d in
                 SZ.v msg_len == FStar.List.Tot.length msg /\
                 Seq.length out_seq' == SZ.v out_len /\
                 SZ.v msg_len <= SZ.v out_len /\
                 (forall (i: nat). i < FStar.List.Tot.length msg ==> Seq.index out_seq' i == FStar.List.Tot.index msg i))))

/// Height of a Huffman tree (maximum depth from root to leaf).
let rec tree_height (t: HSpec.htree) : nat =
  match t with
  | HSpec.Leaf _ _ -> 0
  | HSpec.Internal _ l r ->
    let lh = tree_height l in
    let rh = tree_height r in
    1 + (if lh >= rh then lh else rh)

/// Find the codeword for a given symbol by walking the heap tree.
/// Writes codeword bits into cw_buf starting at position depth.
/// Returns (found, codeword_length).
fn codeword_impl
  (cur: hnode_ptr) (ft: HSpec.htree) (sym: nat)
  (cw_buf: A.array bool) (depth: SZ.t) (max_depth: SZ.t)
  (#cw_seq: G.erased (Seq.seq bool))
  requires is_htree cur ft ** A.pts_to cw_buf cw_seq **
           pure (SZ.v depth + tree_height ft <= SZ.v max_depth /\
                 SZ.v max_depth <= Seq.length cw_seq)
  returns result: (bool & SZ.t)
  ensures is_htree cur ft **
          (exists* cw_seq'. A.pts_to cw_buf cw_seq' **
          pure (Seq.length cw_seq' == Seq.length cw_seq /\
                (forall (j: nat). j < SZ.v depth /\ j < Seq.length cw_seq ==> Seq.index cw_seq' j == Seq.index cw_seq j) /\
                (if fst result then
                   Some? (HCodec.codeword ft sym) /\
                   (let cw = Some?.v (HCodec.codeword ft sym) in
                    SZ.v (snd result) == FStar.List.Tot.length cw /\
                    SZ.v depth + FStar.List.Tot.length cw <= SZ.v max_depth /\
                    SZ.v depth + FStar.List.Tot.length cw <= Seq.length cw_seq' /\
                    (forall (i: nat). i < FStar.List.Tot.length cw ==> Seq.index cw_seq' (SZ.v depth + i) == FStar.List.Tot.index cw i))
                 else
                   None? (HCodec.codeword ft sym))))

/// Convert a contiguous slice [lo..hi) of a nat sequence to a list.
let rec syms_as_list (s: Seq.seq nat) (lo hi: nat)
  : Tot (list nat) (decreases (hi - lo))
  = if lo >= hi || lo >= Seq.length s then []
    else Seq.index s lo :: syms_as_list s (lo + 1) hi

/// Encode: for each symbol, look up codeword and write to output.
fn encode_impl
  (root: hnode_ptr) (ft: HSpec.htree)
  (msg: A.array nat) (msg_len: SZ.t)
  (output: A.array bool) (out_capacity: SZ.t)
  (#msg_seq: G.erased (Seq.seq nat))
  (#out_seq0: G.erased (Seq.seq bool))
  requires is_htree root ft ** A.pts_to msg msg_seq ** A.pts_to output out_seq0 **
           pure (SZ.v msg_len <= Seq.length msg_seq /\
                 Seq.length out_seq0 == SZ.v out_capacity /\
                 Some? (HCodec.encode ft (syms_as_list msg_seq 0 (SZ.v msg_len))) /\
                 FStar.List.Tot.length (Some?.v (HCodec.encode ft (syms_as_list msg_seq 0 (SZ.v msg_len)))) + tree_height ft <= SZ.v out_capacity)
  returns bit_count: SZ.t
  ensures is_htree root ft ** A.pts_to msg msg_seq **
          (exists* out_seq'. A.pts_to output out_seq' **
          pure (let d = HCodec.encode ft (syms_as_list msg_seq 0 (SZ.v msg_len)) in
                Some? d /\
                (let enc = Some?.v d in
                 SZ.v bit_count == FStar.List.Tot.length enc /\
                 Seq.length out_seq' == SZ.v out_capacity /\
                 SZ.v bit_count <= SZ.v out_capacity /\
                 (forall (i: nat). i < FStar.List.Tot.length enc ==> Seq.index out_seq' i == FStar.List.Tot.index enc i))))

