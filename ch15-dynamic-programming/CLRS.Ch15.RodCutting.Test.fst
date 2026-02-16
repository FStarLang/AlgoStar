(*
   Test for Rod Cutting implementation
   
   Example from CLRS: Given prices [1, 5, 8, 9, 10, 17, 17, 20, 24, 30]
   for rod lengths 1-10, the maximum revenue for a rod of length 10 is 30.
*)

module CLRS.Ch15.RodCutting.Test
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch15.RodCutting

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

fn test_rod_cutting_example ()
  requires emp
  returns result: nat
  ensures emp
{
  // Create price array for lengths 1-10
  let pv = V.alloc (1 <: nat) 10sz;
  V.to_array_pts_to pv;
  let prices_arr = V.vec_to_array pv;
  rewrite (A.pts_to (V.vec_to_array pv) (Seq.create 10 (1 <: nat))) as (A.pts_to prices_arr (Seq.create 10 (1 <: nat)));
  
  A.op_Array_Assignment prices_arr 0sz (1 <: nat);
  A.op_Array_Assignment prices_arr 1sz (5 <: nat);
  A.op_Array_Assignment prices_arr 2sz (8 <: nat);
  A.op_Array_Assignment prices_arr 3sz (9 <: nat);
  A.op_Array_Assignment prices_arr 4sz (10 <: nat);
  A.op_Array_Assignment prices_arr 5sz (17 <: nat);
  A.op_Array_Assignment prices_arr 6sz (17 <: nat);
  A.op_Array_Assignment prices_arr 7sz (20 <: nat);
  A.op_Array_Assignment prices_arr 8sz (24 <: nat);
  A.op_Array_Assignment prices_arr 9sz (30 <: nat);
  
  // Compute maximum revenue for rod of length 10
  let revenue = rod_cutting prices_arr 10sz;
  
  // Free the array
  with s. assert (A.pts_to prices_arr s);
  rewrite (A.pts_to prices_arr s) as (A.pts_to (V.vec_to_array pv) s);
  V.to_vec_pts_to pv;
  V.free pv;
  
  revenue
}
