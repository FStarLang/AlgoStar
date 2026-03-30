(*
   Huffman Codec — Spec Validation Test

   Validates the Codec.Impl.fsti API by building a known Huffman tree
   manually, encoding a message, and decoding it, proving the
   postconditions determine the correct output.

   Test tree: Internal 8 (Leaf 0 3) (Leaf 1 5)
     Symbol 0 -> codeword [true]   (go left)
     Symbol 1 -> codeword [false]  (go right)
   
   Test message: [0; 1]
   Expected encoding: [true; false]
   Expected decoding of [true; false]: [0; 1]

   Attribution: Pattern inspired by
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   NO admits. NO assumes.
*)
module CLRS.Ch16.Huffman.Codec.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch16.Huffman.Impl
open CLRS.Ch16.Huffman.Defs
open CLRS.Ch16.Huffman.Codec.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Box = Pulse.Lib.Box
module G = FStar.Ghost
module GR = Pulse.Lib.GhostReference
module HSpec = CLRS.Ch16.Huffman.Spec
module HCodec = CLRS.Ch16.Huffman.Codec
module L = FStar.List.Tot

(* ---------- The known test tree ---------- *)

let test_tree : HSpec.htree = HSpec.Internal 8 (HSpec.Leaf 0 3) (HSpec.Leaf 1 5)

(* ---------- Pure codec facts about the test tree ---------- *)

(* codeword for symbol 0 is [true] *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let codeword_0 () : Lemma (HCodec.codeword test_tree 0 == Some [true])
  = HCodec.codeword_internal 8 (HSpec.Leaf 0 3) (HSpec.Leaf 1 5) 0;
    HCodec.codeword_leaf_match 0 3

(* codeword for symbol 1 is [false] *)
let codeword_1 () : Lemma (HCodec.codeword test_tree 1 == Some [false])
  = HCodec.codeword_internal 8 (HSpec.Leaf 0 3) (HSpec.Leaf 1 5) 1;
    HCodec.codeword_leaf_mismatch 1 0 3;
    HCodec.codeword_leaf_match 1 5

(* encode [0; 1] == Some [true; false] *)
let encode_0_1 () : Lemma (HCodec.encode test_tree [0; 1] == Some [true; false])
  = codeword_0 ();
    codeword_1 ();
    HCodec.encode_cons test_tree 0 [1];
    HCodec.encode_cons test_tree 1 [];
    HCodec.encode_nil test_tree

(* decode [true; false] == Some [0; 1] *)
let decode_tf () : Lemma (HCodec.decode test_tree [true; false] == Some [0; 1])
  = // decode_step on Internal with [true; ...] goes left
    HCodec.decode_step_internal 8 (HSpec.Leaf 0 3) (HSpec.Leaf 1 5) true [false];
    HCodec.decode_step_leaf 0 3 [false];
    // After first decode_step: symbol = 0, remaining = [false]
    HCodec.decode_cons test_tree [true; false];
    // decode_step on Internal with [false; ...] goes right
    HCodec.decode_step_internal 8 (HSpec.Leaf 0 3) (HSpec.Leaf 1 5) false [];
    HCodec.decode_step_leaf 1 5 [];
    HCodec.decode_cons test_tree [false];
    HCodec.decode_nil test_tree

(* The postcondition of decode_impl is precise enough to give output [0; 1] *)
let decode_post_implies_0_1 (out_seq: Seq.seq int) (msg_len: SZ.t)
  : Lemma
    (requires
      (let d = HCodec.decode test_tree (bits_as_list (Seq.seq_of_list [true; false]) 0 2) in
       Some? d /\
       (let msg = Some?.v d in
        SZ.v msg_len == L.length msg /\
        Seq.length out_seq == 4 /\
        SZ.v msg_len <= 4 /\
        (forall (i: nat). i < L.length msg ==> Seq.index out_seq i == L.index msg i))))
    (ensures
      SZ.v msg_len == 2 /\
      Seq.index out_seq 0 == 0 /\
      Seq.index out_seq 1 == 1)
  = // bits_as_list [true; false] 0 2 == [true; false]
    bits_as_list_cons (Seq.seq_of_list [true; false]) 0 2;
    bits_as_list_cons (Seq.seq_of_list [true; false]) 1 2;
    assert_norm (Seq.index (Seq.seq_of_list [true; false]) 0 == true);
    assert_norm (Seq.index (Seq.seq_of_list [true; false]) 1 == false);
    decode_tf ()

(* encode test: postcondition is precise enough to produce [true; false] *)
let encode_post_implies_tf (out_seq: Seq.seq bool) (bit_count: SZ.t)
  : Lemma
    (requires
      (let d = HCodec.encode test_tree (syms_as_list (Seq.seq_of_list [0; 1]) 0 2) in
       Some? d /\
       (let enc = Some?.v d in
        SZ.v bit_count == L.length enc /\
        Seq.length out_seq == 4 /\
        SZ.v bit_count <= 4 /\
        (forall (i: nat). i < L.length enc ==> Seq.index out_seq i == L.index enc i))))
    (ensures
      SZ.v bit_count == 2 /\
      Seq.index out_seq 0 == true /\
      Seq.index out_seq 1 == false)
  = // syms_as_list [0; 1] 0 2 == [0; 1]
    assert_norm (Seq.index (Seq.seq_of_list [0; 1]) 0 == 0);
    assert_norm (Seq.index (Seq.seq_of_list [0; 1]) 1 == 1);
    encode_0_1 ()
#pop-options

(* Helper: build a heap-allocated test tree and get is_htree *)
#push-options "--z3rlimit 20"
```pulse
fn build_test_tree ()
  requires emp
  returns p: hnode_ptr
  ensures is_htree p test_tree
{
  // Allocate left leaf: Leaf 0 3
  let left_node : hnode = { sym = 0; freq = 3; left = None #(Box.box hnode); right = None #(Box.box hnode) };
  let lp = Box.alloc left_node;
  intro_is_htree_leaf lp 0 3;

  // Allocate right leaf: Leaf 1 5
  let right_node : hnode = { sym = 1; freq = 5; left = None #(Box.box hnode); right = None #(Box.box hnode) };
  let rp = Box.alloc right_node;
  intro_is_htree_leaf rp 1 5;

  // Allocate internal node: Internal 8 (Leaf 0 3) (Leaf 1 5)
  let root_node : hnode = { sym = 0; freq = 8; left = Some lp; right = Some rp };
  let root = Box.alloc root_node;
  intro_is_htree_internal root lp rp 8 (HSpec.Leaf 0 3) (HSpec.Leaf 1 5);
  root
}
```
#pop-options

(* ---------- Decode Test ---------- *)

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
```pulse
fn test_decode ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // Build test tree
  let root = build_test_tree ();

  // Allocate bits array = [true; false]
  let bv = V.alloc false 2sz;
  V.to_array_pts_to bv;
  let bits = V.vec_to_array bv;
  rewrite (A.pts_to (V.vec_to_array bv) (Seq.create 2 false))
       as (A.pts_to bits (Seq.create 2 false));
  bits.(0sz) <- true;
  bits.(1sz) <- false;

  // Allocate output array (capacity 4)
  let ov = V.alloc 0 4sz;
  V.to_array_pts_to ov;
  let output = V.vec_to_array ov;
  rewrite (A.pts_to (V.vec_to_array ov) (Seq.create 4 0))
       as (A.pts_to output (Seq.create 4 0));

  // Prove precondition
  with bits_seq. assert (A.pts_to bits bits_seq);
  
  // Need: decode test_tree (bits_as_list bits_seq 0 2) == Some [0; 1]
  bits_as_list_cons bits_seq 0 2;
  bits_as_list_cons bits_seq 1 2;
  decode_tf ();

  // Call decode_impl
  let msg_len = decode_impl root test_tree bits 2sz output 4sz;

  // Read postcondition
  with out_seq'. assert (A.pts_to output out_seq');

  // Prove output is [0; 1]
  decode_post_implies_0_1 out_seq' msg_len;
  assert (pure (SZ.v msg_len == 2));

  // Read and verify
  let v0 = output.(0sz);
  let v1 = output.(1sz);
  assert (pure (v0 == 0));
  assert (pure (v1 == 1));

  // Runtime check (survives extraction to C)
  let pass = (v0 = 0) && (v1 = 1);

  // Cleanup — free tree properly
  free_htree root test_tree;
  
  with s1. assert (A.pts_to bits s1);
  rewrite (A.pts_to bits s1) as (A.pts_to (V.vec_to_array bv) s1);
  V.to_vec_pts_to bv;
  V.free bv;

  with s2. assert (A.pts_to output s2);
  rewrite (A.pts_to output s2) as (A.pts_to (V.vec_to_array ov) s2);
  V.to_vec_pts_to ov;
  V.free ov;
  pass
}
```
#pop-options

(* ---------- Encode Test ---------- *)

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
```pulse
fn test_encode ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // Build test tree
  let root = build_test_tree ();

  // Allocate message array = [0; 1] as nat
  let zero_nat : nat = 0;
  let mv = V.alloc zero_nat 2sz;
  V.to_array_pts_to mv;
  let msg = V.vec_to_array mv;
  rewrite (A.pts_to (V.vec_to_array mv) (Seq.create 2 zero_nat))
       as (A.pts_to msg (Seq.create 2 zero_nat));
  msg.(0sz) <- 0;
  msg.(1sz) <- 1;

  // Allocate output bits array (capacity 4)
  let ov = V.alloc false 4sz;
  V.to_array_pts_to ov;
  let output = V.vec_to_array ov;
  rewrite (A.pts_to (V.vec_to_array ov) (Seq.create 4 false))
       as (A.pts_to output (Seq.create 4 false));

  // Prove precondition: need syms_as_list msg_seq 0 2 == [0; 1] 
  // and Some? (HCodec.encode test_tree [0; 1])
  with msg_seq. assert (A.pts_to msg msg_seq);
  encode_0_1 ();

  // tree_height test_tree == 1
  assert (pure (tree_height test_tree == 1));

  // Call encode_impl
  let bit_count = encode_impl root test_tree msg 2sz output 4sz;

  // Read postcondition
  with out_seq'. assert (A.pts_to output out_seq');

  // Prove output is [true; false]
  encode_post_implies_tf out_seq' bit_count;
  assert (pure (SZ.v bit_count == 2));

  // Read and verify
  let v0 = output.(0sz);
  let v1 = output.(1sz);
  assert (pure (v0 == true));
  assert (pure (v1 == false));

  // Runtime check (survives extraction to C)
  let pass = (v0 = true) && (v1 = false);

  // Cleanup — free tree properly
  free_htree root test_tree;
  
  with s1. assert (A.pts_to msg s1);
  rewrite (A.pts_to msg s1) as (A.pts_to (V.vec_to_array mv) s1);
  V.to_vec_pts_to mv;
  V.free mv;

  with s2. assert (A.pts_to output s2);
  rewrite (A.pts_to output s2) as (A.pts_to (V.vec_to_array ov) s2);
  V.to_vec_pts_to ov;
  V.free ov;
  pass
}
```
#pop-options
