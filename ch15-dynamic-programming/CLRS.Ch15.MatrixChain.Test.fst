(*
   Test for Matrix Chain Multiplication
   
   Example from CLRS: matrices with dimensions
   30×35, 35×15, 15×5, 5×10, 10×20, 20×25
   
   Represented as p = [30, 35, 15, 5, 10, 20, 25]
   
   Optimal cost should be 15,125 multiplications
*)

module CLRS.Ch15.MatrixChain.Test
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch15.MatrixChain

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

fn test_matrix_chain ()
  requires emp
  returns result: int
  ensures pure (result >= 0)
{
  let dv = V.alloc 30 7sz;
  V.to_array_pts_to dv;
  let dims = V.vec_to_array dv;
  rewrite (A.pts_to (V.vec_to_array dv) (Seq.create 7 30)) as (A.pts_to dims (Seq.create 7 30));
  
  A.op_Array_Assignment dims 0sz 30;
  A.op_Array_Assignment dims 1sz 35;
  A.op_Array_Assignment dims 2sz 15;
  A.op_Array_Assignment dims 3sz 5;
  A.op_Array_Assignment dims 4sz 10;
  A.op_Array_Assignment dims 5sz 20;
  A.op_Array_Assignment dims 6sz 25;
  
  // n = 6 (number of matrices)
  let n = 6sz;
  
  // Compute optimal cost
  let cost = matrix_chain_order dims n;
  
  // Free the array
  with s. assert (A.pts_to dims s);
  rewrite (A.pts_to dims s) as (A.pts_to (V.vec_to_array dv) s);
  V.to_vec_pts_to dv;
  V.free dv;
  
  cost
}
