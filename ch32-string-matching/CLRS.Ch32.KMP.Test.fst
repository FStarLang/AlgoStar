(*
   Test the KMP prefix function computation
   
   Examples from CLRS Chapter 32:
   - Pattern "ababaca" should produce π = [0,0,1,2,3,0,1]
*)

module CLRS.Ch32.KMP.Test
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch32.KMP

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

#push-options "--z3rlimit 50"

// Test with a simple pattern
fn test_kmp_simple ()
  requires emp
  returns _: unit
  ensures emp
{
  // Pattern: "aba" (as integers)
  let pv = V.alloc 97 3sz;
  V.to_array_pts_to pv;
  let pattern_arr = V.vec_to_array pv;
  with sp0. assert (A.pts_to (V.vec_to_array pv) sp0);
  rewrite (A.pts_to (V.vec_to_array pv) sp0) as (A.pts_to pattern_arr sp0);
  A.op_Array_Assignment pattern_arr 0sz 97;
  A.op_Array_Assignment pattern_arr 1sz 98;
  A.op_Array_Assignment pattern_arr 2sz 97;
  
  // Allocate output array
  let piv = V.alloc 0sz 3sz;
  V.to_array_pts_to piv;
  let pi_arr = V.vec_to_array piv;
  with spi0. assert (A.pts_to (V.vec_to_array piv) spi0);
  rewrite (A.pts_to (V.vec_to_array piv) spi0) as (A.pts_to pi_arr spi0);
  
  // Compute prefix function
  compute_prefix_function pattern_arr pi_arr 3sz;
  
  // Read results
  let pi0 = A.op_Array_Access pi_arr 0sz;
  let pi1 = A.op_Array_Access pi_arr 1sz;
  let pi2 = A.op_Array_Access pi_arr 2sz;
  
  // Clean up
  with sp. assert (A.pts_to pattern_arr sp);
  rewrite (A.pts_to pattern_arr sp) as (A.pts_to (V.vec_to_array pv) sp);
  V.to_vec_pts_to pv;
  V.free pv;
  with spi. assert (A.pts_to pi_arr spi);
  rewrite (A.pts_to pi_arr spi) as (A.pts_to (V.vec_to_array piv) spi);
  V.to_vec_pts_to piv;
  V.free piv;
  
  ()
}

// Test with CLRS example pattern "ababaca"
fn test_kmp_clrs ()
  requires emp
  returns _: unit
  ensures emp
{
  // Pattern: "ababaca" (as integers: 0,1,0,1,0,2,0)
  let pv = V.alloc 0 7sz;
  V.to_array_pts_to pv;
  let pattern_arr = V.vec_to_array pv;
  with sp0. assert (A.pts_to (V.vec_to_array pv) sp0);
  rewrite (A.pts_to (V.vec_to_array pv) sp0) as (A.pts_to pattern_arr sp0);
  A.op_Array_Assignment pattern_arr 0sz 0;
  A.op_Array_Assignment pattern_arr 1sz 1;
  A.op_Array_Assignment pattern_arr 2sz 0;
  A.op_Array_Assignment pattern_arr 3sz 1;
  A.op_Array_Assignment pattern_arr 4sz 0;
  A.op_Array_Assignment pattern_arr 5sz 2;
  A.op_Array_Assignment pattern_arr 6sz 0;
  
  // Allocate output array
  let piv = V.alloc 0sz 7sz;
  V.to_array_pts_to piv;
  let pi_arr = V.vec_to_array piv;
  with spi0. assert (A.pts_to (V.vec_to_array piv) spi0);
  rewrite (A.pts_to (V.vec_to_array piv) spi0) as (A.pts_to pi_arr spi0);
  
  // Compute prefix function
  compute_prefix_function pattern_arr pi_arr 7sz;
  
  // Read results (expected: [0,0,1,2,3,0,1])
  let pi0 = A.op_Array_Access pi_arr 0sz;
  let pi1 = A.op_Array_Access pi_arr 1sz;
  let pi2 = A.op_Array_Access pi_arr 2sz;
  let pi3 = A.op_Array_Access pi_arr 3sz;
  let pi4 = A.op_Array_Access pi_arr 4sz;
  let pi5 = A.op_Array_Access pi_arr 5sz;
  let pi6 = A.op_Array_Access pi_arr 6sz;
  
  // Clean up
  with sp. assert (A.pts_to pattern_arr sp);
  rewrite (A.pts_to pattern_arr sp) as (A.pts_to (V.vec_to_array pv) sp);
  V.to_vec_pts_to pv;
  V.free pv;
  with spi. assert (A.pts_to pi_arr spi);
  rewrite (A.pts_to pi_arr spi) as (A.pts_to (V.vec_to_array piv) spi);
  V.to_vec_pts_to piv;
  V.free piv;
  
  ()
}

#pop-options
