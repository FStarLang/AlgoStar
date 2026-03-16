(*
   Test for Longest Common Subsequence implementation

   Example: x = "ABCBDAB" (as ints [65,66,67,66,68,65,66])
            y = "BDCABA"  (as ints [66,68,67,65,66,65])
   
   LCS length should be 4 (e.g., "BCBA")
*)

module CLRS.Ch15.LCS.Test
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch15.LCS.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

fn test_lcs_example ()
  requires emp
  returns result: int
  ensures emp
{
  // x = "ABCBDAB" as ASCII ints
  let xv = V.alloc 65 7sz;
  V.to_array_pts_to xv;
  let x_arr = V.vec_to_array xv;
  rewrite (A.pts_to (V.vec_to_array xv) (Seq.create 7 65)) as (A.pts_to x_arr (Seq.create 7 65));

  A.op_Array_Assignment x_arr 0sz 65;  // A
  A.op_Array_Assignment x_arr 1sz 66;  // B
  A.op_Array_Assignment x_arr 2sz 67;  // C
  A.op_Array_Assignment x_arr 3sz 66;  // B
  A.op_Array_Assignment x_arr 4sz 68;  // D
  A.op_Array_Assignment x_arr 5sz 65;  // A
  A.op_Array_Assignment x_arr 6sz 66;  // B

  // y = "BDCABA" as ASCII ints
  let yv = V.alloc 66 6sz;
  V.to_array_pts_to yv;
  let y_arr = V.vec_to_array yv;
  rewrite (A.pts_to (V.vec_to_array yv) (Seq.create 6 66)) as (A.pts_to y_arr (Seq.create 6 66));

  A.op_Array_Assignment y_arr 0sz 66;  // B
  A.op_Array_Assignment y_arr 1sz 68;  // D
  A.op_Array_Assignment y_arr 2sz 67;  // C
  A.op_Array_Assignment y_arr 3sz 65;  // A
  A.op_Array_Assignment y_arr 4sz 66;  // B
  A.op_Array_Assignment y_arr 5sz 65;  // A

  // Compute LCS length for m=7, n=6
  let ctr = GR.alloc #nat 0;
  let lcs_len = lcs x_arr y_arr 7sz 6sz ctr;
  GR.free ctr;

  // Free the arrays
  with sx. assert (A.pts_to x_arr sx);
  rewrite (A.pts_to x_arr sx) as (A.pts_to (V.vec_to_array xv) sx);
  V.to_vec_pts_to xv;
  V.free xv;

  with sy. assert (A.pts_to y_arr sy);
  rewrite (A.pts_to y_arr sy) as (A.pts_to (V.vec_to_array yv) sy);
  V.to_vec_pts_to yv;
  V.free yv;

  lcs_len
}
