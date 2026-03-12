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

// ========== decode_impl: full decoder ==========

#push-options "--z3rlimit 80"
// Helper: after decoding one symbol, the suffix invariant is maintained
let decode_suffix_step
  (ft: HSpec.htree)
  (bits_seq: Seq.seq bool)
  (pos bit_len: nat)
  (out_v: nat)
  (sym: nat) (new_pos: nat)
  : Lemma
    (requires pos < bit_len /\ bit_len <= Seq.length bits_seq /\
              HSpec.Internal? ft /\
              Some? (HCodec.decode ft (bits_as_list bits_seq pos bit_len)) /\
              Some? (HCodec.decode_step ft (bits_as_list bits_seq pos bit_len)) /\
              (let ds = Some?.v (HCodec.decode_step ft (bits_as_list bits_seq pos bit_len)) in
               fst ds == sym /\ new_pos <= bit_len /\
               snd ds == bits_as_list bits_seq new_pos bit_len) /\
              Some? (HCodec.decode ft (bits_as_list bits_seq 0 bit_len)) /\
              (let remaining = Some?.v (HCodec.decode ft (bits_as_list bits_seq pos bit_len)) in
               let full_msg = Some?.v (HCodec.decode ft (bits_as_list bits_seq 0 bit_len)) in
               Cons? remaining /\
               out_v + L.length remaining == L.length full_msg /\
               (forall (i: nat). i < L.length remaining ==>
                 L.index remaining i == L.index full_msg (out_v + i))))
    (ensures
      Some? (HCodec.decode ft (bits_as_list bits_seq new_pos bit_len)) /\
      (let remaining = Some?.v (HCodec.decode ft (bits_as_list bits_seq pos bit_len)) in
       let full_msg = Some?.v (HCodec.decode ft (bits_as_list bits_seq 0 bit_len)) in
       let new_remaining = Some?.v (HCodec.decode ft (bits_as_list bits_seq new_pos bit_len)) in
       sym == L.index full_msg out_v /\
       (out_v + 1) + L.length new_remaining == L.length full_msg /\
       (forall (i: nat). i < L.length new_remaining ==>
         L.index new_remaining i == L.index full_msg ((out_v + 1) + i))))
  = let bits_l = bits_as_list bits_seq pos bit_len in
    bits_as_list_length bits_seq pos bit_len;
    HCodec.decode_step_progress ft bits_l;
    HCodec.decode_cons ft bits_l;
    let ds = Some?.v (HCodec.decode_step ft bits_l) in
    // decode_cons gives: decode ft bits_l == Some (sym :: rest_msg)  
    // where rest_msg comes from decode ft (snd ds) == decode ft (bits_as_list bits_seq new_pos bit_len)
    let remaining = Some?.v (HCodec.decode ft bits_l) in
    let full_msg = Some?.v (HCodec.decode ft (bits_as_list bits_seq 0 bit_len)) in
    // Connect snd ds to new_pos bits
    assert (snd ds == bits_as_list bits_seq new_pos bit_len);
    // remaining == sym :: decode_result_at_new_pos
    assert (Some? (HCodec.decode ft (bits_as_list bits_seq new_pos bit_len)));
    let new_rem = Some?.v (HCodec.decode ft (bits_as_list bits_seq new_pos bit_len)) in
    assert (remaining == sym :: new_rem);
    // sym is the head
    HCodec.list_index_zero #nat sym new_rem;
    // from requires forall with i=0
    assert (L.index remaining 0 == L.index full_msg (out_v + 0));
    // forall for new_rem
    let aux (i: nat{i < L.length new_rem})
      : Lemma (L.index new_rem i == L.index full_msg ((out_v + 1) + i))
      = HCodec.list_index_succ #nat sym new_rem i;
        assert (L.index (sym :: new_rem) (i + 1) == L.index new_rem i);
        assert (L.index remaining (i + 1) == L.index new_rem i);
        assert (i + 1 < L.length remaining)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

// Full decoder: decode entire bitstring into an output array.
// Postcondition: output matches pure decode.
#push-options "--z3rlimit 160 --split_queries always"
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
                 L.length (Some?.v (HCodec.decode ft (bits_as_list bits_seq 0 (SZ.v bit_len)))) <= SZ.v out_len)
  returns msg_len: SZ.t
  ensures is_htree root ft ** A.pts_to bits bits_seq **
          (exists* out_seq'. A.pts_to output out_seq' **
          pure (let d = HCodec.decode ft (bits_as_list bits_seq 0 (SZ.v bit_len)) in
                Some? d /\
                (let msg = Some?.v d in
                 SZ.v msg_len == L.length msg /\
                 Seq.length out_seq' == SZ.v out_len /\
                 SZ.v msg_len <= SZ.v out_len /\
                 (forall (i: nat). i < L.length msg ==> Seq.index out_seq' i == L.index msg i))))
{
  let mut pos: SZ.t = 0sz;
  let mut out_idx: SZ.t = 0sz;

  HCodec.decode_nil ft;

  while (
    let p = !pos;
    (p <^ bit_len)
  )
  invariant exists* pos_v out_v out_seq.
    R.pts_to pos pos_v **
    R.pts_to out_idx out_v **
    A.pts_to output out_seq **
    is_htree root ft **
    A.pts_to bits bits_seq **
    pure (
      SZ.v pos_v <= SZ.v bit_len /\
      SZ.v out_v <= SZ.v out_len /\
      Seq.length out_seq == SZ.v out_len /\
      Some? (HCodec.decode ft (bits_as_list bits_seq (SZ.v pos_v) (SZ.v bit_len))) /\
      (let remaining = Some?.v (HCodec.decode ft (bits_as_list bits_seq (SZ.v pos_v) (SZ.v bit_len))) in
       let full_msg = Some?.v (HCodec.decode ft (bits_as_list bits_seq 0 (SZ.v bit_len))) in
       SZ.v out_v + L.length remaining == L.length full_msg /\
       L.length full_msg <= SZ.v out_len /\
       (forall (i: nat). i < SZ.v out_v ==> Seq.index out_seq i == L.index full_msg i) /\
       (forall (i: nat). i < L.length remaining ==> L.index remaining i == L.index full_msg (SZ.v out_v + i)))
    )
  decreases (SZ.v bit_len - SZ.v !pos)
  {
    let p = !pos;
    let ov = !out_idx;

    // Prove decode_step succeeds
    bits_as_list_length bits_seq (SZ.v p) (SZ.v bit_len);
    HCodec.decode_some_implies_step ft (bits_as_list bits_seq (SZ.v p) (SZ.v bit_len));

    // Decode one symbol
    let result = decode_step_impl root ft bits p bit_len;
    let sym = fst result;
    let new_pos = snd result;

    // Prove remaining is non-empty (Cons?) so out_v < out_len
    HCodec.decode_cons ft (bits_as_list bits_seq (SZ.v p) (SZ.v bit_len));

    // Write symbol to output
    A.op_Array_Assignment output ov sym;

    // Prove suffix invariant is maintained
    decode_suffix_step ft bits_seq (SZ.v p) (SZ.v bit_len) (SZ.v ov) sym (SZ.v new_pos);

    pos := new_pos;
    out_idx := ov +^ 1sz;
  };

  !out_idx
}
#pop-options

// ========== codeword_impl: find codeword by tree walk ==========

let tree_height_internal (f: pos) (l r: HSpec.htree)
  : Lemma (tree_height (HSpec.Internal f l r) >= 1 + tree_height l /\
           tree_height (HSpec.Internal f l r) >= 1 + tree_height r)
  = ()

// Walk the tree to find the codeword for a given symbol.
// Writes codeword bits into cw_buf starting at position depth.
// Returns (found, codeword_length).
#push-options "--z3rlimit 200 --split_queries always --fuel 1 --ifuel 1"
fn rec codeword_impl
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
                    SZ.v (snd result) == L.length cw /\
                    SZ.v depth + L.length cw <= SZ.v max_depth /\
                    SZ.v depth + L.length cw <= Seq.length cw_seq' /\
                    (forall (i: nat). i < L.length cw ==> Seq.index cw_seq' (SZ.v depth + i) == L.index cw i))
                 else
                   None? (HCodec.codeword ft sym))))
  decreases ft
{
  match ft {
    HSpec.Leaf s f -> {
      elim_is_htree_leaf cur s f;
      let node = Box.op_Bang cur;
      intro_is_htree_leaf cur s f;
      rewrite (is_htree cur (HSpec.Leaf s f)) as (is_htree cur ft);
      if (node.sym = sym) {
        HCodec.codeword_leaf_match sym f;
        (true, 0sz)
      } else {
        HCodec.codeword_leaf_mismatch sym s f;
        (false, 0sz)
      }
    }
    HSpec.Internal f l r -> {
      tree_height_internal f l r;
      elim_is_htree_internal cur f l r;
      with lp rp. _;
      let node = Box.op_Bang cur;

      // Write true at depth, try left subtree
      A.op_Array_Assignment cw_buf depth true;
      let lp_rt = Some?.v node.left;
      rewrite (is_htree lp l) as (is_htree lp_rt l);
      let left_result = codeword_impl lp_rt l sym cw_buf (depth +^ 1sz) max_depth;
      rewrite (is_htree lp_rt l) as (is_htree lp l);

      if (fst left_result) {
        // Found in left subtree — codeword = true :: left_cw
        HCodec.codeword_internal f l r sym;
        intro_is_htree_internal cur lp rp f l r;
        rewrite (is_htree cur (HSpec.Internal f l r)) as (is_htree cur ft);
        (true, snd left_result +^ 1sz)
      } else {
        // Not in left, try right with false
        A.op_Array_Assignment cw_buf depth false;
        let rp_rt = Some?.v node.right;
        rewrite (is_htree rp r) as (is_htree rp_rt r);
        let right_result = codeword_impl rp_rt r sym cw_buf (depth +^ 1sz) max_depth;
        rewrite (is_htree rp_rt r) as (is_htree rp r);

        if (fst right_result) {
          // Found in right subtree — codeword = false :: right_cw
          HCodec.codeword_internal f l r sym;
          intro_is_htree_internal cur lp rp f l r;
          rewrite (is_htree cur (HSpec.Internal f l r)) as (is_htree cur ft);
          (true, snd right_result +^ 1sz)
        } else {
          // Not found anywhere
          HCodec.codeword_internal f l r sym;
          intro_is_htree_internal cur lp rp f l r;
          rewrite (is_htree cur (HSpec.Internal f l r)) as (is_htree cur ft);
          (false, 0sz)
        }
      }
    }
  }
}
#pop-options

// ========== encode_impl: encoder using codeword_impl ==========

let rec syms_as_list_length (s: Seq.seq nat) (lo hi: nat)
  : Lemma (requires hi <= Seq.length s /\ lo <= hi)
          (ensures L.length (syms_as_list s lo hi) == hi - lo)
          (decreases hi - lo)
  = if lo >= hi then () else syms_as_list_length s (lo + 1) hi

let syms_as_list_cons (s: Seq.seq nat) (lo hi: nat)
  : Lemma (requires lo < hi /\ hi <= Seq.length s)
          (ensures syms_as_list s lo hi == Seq.index s lo :: syms_as_list s (lo + 1) hi)
  = ()

#push-options "--z3rlimit 20"
let rec append_index_left (l1 l2: list bool) (i: nat)
  : Lemma (requires i < L.length l1)
          (ensures L.length (l1 @ l2) == L.length l1 + L.length l2 /\
                   L.index (l1 @ l2) i == L.index l1 i)
          (decreases l1)
  = L.append_length l1 l2;
    match l1 with
    | _ :: tl -> if i = 0 then () else append_index_left tl l2 (i - 1)

let rec append_index_right (l1 l2: list bool) (i: nat)
  : Lemma (requires i < L.length l2)
          (ensures L.length (l1 @ l2) == L.length l1 + L.length l2 /\
                   L.index (l1 @ l2) (L.length l1 + i) == L.index l2 i)
          (decreases l1)
  = L.append_length l1 l2;
    match l1 with
    | [] -> ()
    | _ :: tl -> append_index_right tl l2 i
#pop-options

// After one encode step: remaining-suffix index invariant is maintained (list-only, no Seq)
#push-options "--z3rlimit 80"
let encode_suffix_step
  (ft: HSpec.htree)
  (msg_seq: Seq.seq nat)
  (si msg_len bp: nat) (s: nat)
  : Lemma
    (requires
      si < msg_len /\ msg_len <= Seq.length msg_seq /\
      s == Seq.index msg_seq si /\
      Some? (HCodec.encode ft (syms_as_list msg_seq si msg_len)) /\
      Some? (HCodec.encode ft (syms_as_list msg_seq 0 msg_len)) /\
      Some? (HCodec.codeword ft s) /\
      (let remaining_enc = Some?.v (HCodec.encode ft (syms_as_list msg_seq si msg_len)) in
       let full_enc = Some?.v (HCodec.encode ft (syms_as_list msg_seq 0 msg_len)) in
       bp + L.length remaining_enc == L.length full_enc /\
       (forall (j: nat). j < L.length remaining_enc ==>
         L.index remaining_enc j == L.index full_enc (bp + j))))
    (ensures
      Some? (HCodec.encode ft (syms_as_list msg_seq (si + 1) msg_len)) /\
      (let cw = Some?.v (HCodec.codeword ft s) in
       let new_remaining = Some?.v (HCodec.encode ft (syms_as_list msg_seq (si + 1) msg_len)) in
       let full_enc = Some?.v (HCodec.encode ft (syms_as_list msg_seq 0 msg_len)) in
       let new_bp = bp + L.length cw in
       new_bp + L.length new_remaining == L.length full_enc /\
       (forall (k: nat). k < L.length cw ==> L.index cw k == L.index full_enc (bp + k)) /\
       (forall (j: nat). j < L.length new_remaining ==>
         L.index new_remaining j == L.index full_enc (new_bp + j))))
  = syms_as_list_cons msg_seq si msg_len;
    HCodec.encode_cons ft s (syms_as_list msg_seq (si + 1) msg_len);
    let remaining_enc = Some?.v (HCodec.encode ft (syms_as_list msg_seq si msg_len)) in
    let full_enc = Some?.v (HCodec.encode ft (syms_as_list msg_seq 0 msg_len)) in
    let cw = Some?.v (HCodec.codeword ft s) in
    let new_remaining = Some?.v (HCodec.encode ft (syms_as_list msg_seq (si + 1) msg_len)) in
    assert (remaining_enc == cw @ new_remaining);
    L.append_length cw new_remaining;
    let aux_cw (k: nat{k < L.length cw})
      : Lemma (L.index cw k == L.index full_enc (bp + k))
      = append_index_left cw new_remaining k
    in
    Classical.forall_intro (Classical.move_requires aux_cw);
    let aux_suffix (j: nat{j < L.length new_remaining})
      : Lemma (L.index new_remaining j == L.index full_enc (bp + L.length cw + j))
      = append_index_right cw new_remaining j
    in
    Classical.forall_intro (Classical.move_requires aux_suffix)
#pop-options

// Encode: for each symbol in msg, look up codeword and write to output.
// Uses suffix-based invariant: tracks encode of remaining symbols.
#restart-solver
#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
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
                 L.length (Some?.v (HCodec.encode ft (syms_as_list msg_seq 0 (SZ.v msg_len)))) + tree_height ft <= SZ.v out_capacity)
  returns bit_count: SZ.t
  ensures is_htree root ft ** A.pts_to msg msg_seq **
          (exists* out_seq'. A.pts_to output out_seq' **
          pure (let d = HCodec.encode ft (syms_as_list msg_seq 0 (SZ.v msg_len)) in
                Some? d /\
                (let enc = Some?.v d in
                 SZ.v bit_count == L.length enc /\
                 Seq.length out_seq' == SZ.v out_capacity /\
                 SZ.v bit_count <= SZ.v out_capacity /\
                 (forall (i: nat). i < L.length enc ==> Seq.index out_seq' i == L.index enc i))))
{
  let mut sym_idx: SZ.t = 0sz;
  let mut bit_pos: SZ.t = 0sz;

  HCodec.encode_nil ft;

  while (
    let si = !sym_idx;
    (si <^ msg_len)
  )
  invariant exists* si_v bp_v out_seq.
    R.pts_to sym_idx si_v **
    R.pts_to bit_pos bp_v **
    A.pts_to output out_seq **
    is_htree root ft **
    A.pts_to msg msg_seq **
    pure (
      SZ.v si_v <= SZ.v msg_len /\
      Seq.length out_seq == SZ.v out_capacity /\
      Some? (HCodec.encode ft (syms_as_list msg_seq (SZ.v si_v) (SZ.v msg_len))) /\
      (let remaining_enc = Some?.v (HCodec.encode ft (syms_as_list msg_seq (SZ.v si_v) (SZ.v msg_len))) in
       let full_enc = Some?.v (HCodec.encode ft (syms_as_list msg_seq 0 (SZ.v msg_len))) in
       SZ.v bp_v + L.length remaining_enc == L.length full_enc /\
       SZ.v bp_v + tree_height ft <= SZ.v out_capacity /\
       (forall (i: nat). i < SZ.v bp_v ==> Seq.index out_seq i == L.index full_enc i) /\
       (forall (j: nat). j < L.length remaining_enc ==>
         L.index remaining_enc j == L.index full_enc (SZ.v bp_v + j)))
    )
  decreases (SZ.v msg_len - SZ.v !sym_idx)
  {
    let si = !sym_idx;
    let bp = !bit_pos;

    // Read the symbol
    let s = A.op_Array_Access msg si;

    // Decompose: syms_as_list si msg_len = s :: syms_as_list (si+1) msg_len
    syms_as_list_cons msg_seq (SZ.v si) (SZ.v msg_len);
    HCodec.encode_cons ft s (syms_as_list msg_seq (SZ.v si + 1) (SZ.v msg_len));

    // Find codeword and write to output
    let result = codeword_impl root ft s output bp out_capacity;
    with cw_out. assert (A.pts_to output cw_out);

    let cw_len = snd result;

    // Prove the suffix invariant is maintained (list-level facts)
    encode_suffix_step ft msg_seq (SZ.v si) (SZ.v msg_len) (SZ.v bp) s;

    // Update indices
    bit_pos := bp +^ cw_len;
    sym_idx := si +^ 1sz;
  };

  !bit_pos
}
#pop-options
