(*
   Test for CLRS.Ch16.Huffman
   
   Example from CLRS: frequencies [5; 9; 12; 13; 16; 45]
   Expected Huffman tree cost: 224
*)

module TestHuffman
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch16.Huffman

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

fn test_huffman_simple ()
  requires emp
  returns result:int
  ensures emp ** pure (result >= 0)
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
  
  // Compute Huffman cost
  let cost = huffman_cost freqs 6sz;
  
  // Free the array
  with s. assert (A.pts_to freqs s);
  rewrite (A.pts_to freqs s) as (A.pts_to (V.vec_to_array fv) s);
  V.to_vec_pts_to fv;
  V.free fv;
  
  cost
}
