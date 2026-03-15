(*
   Test for CLRS.Ch16.Huffman.Impl
   
   Example from CLRS: frequencies [5; 9; 12; 13; 16; 45]
   Builds a Huffman tree (verified optimal) and drops it.
*)

module TestHuffman
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
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

#push-options "--z3rlimit 20"
fn test_huffman_simple ()
  requires emp
  returns _:unit
  ensures emp
{
  // Create test array with frequencies
  let fv = V.alloc 5 6sz;
  V.to_array_pts_to fv;
  let freqs = V.vec_to_array fv;
  rewrite (A.pts_to (V.vec_to_array fv) (Seq.create 6 5)) as (A.pts_to freqs (Seq.create 6 5));
  A.op_Array_Assignment freqs 0sz 5;
  A.op_Array_Assignment freqs 1sz 9;
  A.op_Array_Assignment freqs 2sz 12;
  A.op_Array_Assignment freqs 3sz 13;
  A.op_Array_Assignment freqs 4sz 16;
  A.op_Array_Assignment freqs 5sz 45;
  
  // Build Huffman tree (verified optimal) — drop result for test
  let ghost_ctr = GR.alloc #nat 0;
  let tree_ptr = huffman_tree freqs 6sz ghost_ctr;
  with s_final. assert (A.pts_to freqs s_final);
  drop_ (exists* ft (cf: nat). is_htree tree_ptr ft **
                   GR.pts_to ghost_ctr cf **
                   pure (HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list s_final 0) /\
                         HSpec.same_frequency_multiset ft (seq_to_pos_list s_final 0) /\
                         HSpec.is_wpl_optimal ft (seq_to_pos_list s_final 0) /\
                         HCmplx.huffman_merge_bound cf 0 6));
  
  // Free the array
  rewrite (A.pts_to freqs s_final) as (A.pts_to (V.vec_to_array fv) s_final);
  V.to_vec_pts_to fv;
  V.free fv;
}
#pop-options
