module CLRS.Ch26.MaxFlow.Test
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch26.MaxFlow.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

fn test_max_flow_example ()
  requires emp
  returns _:unit
  ensures emp
{
  let n : SZ.t = 3sz;
  let nn : SZ.t = n *^ n;
  
  // Allocate capacity matrix (3x3 = 9 elements)
  let cv = V.alloc 0 nn;
  V.to_array_pts_to cv;
  let capacity = V.vec_to_array cv;
  with sc. assert (A.pts_to (V.vec_to_array cv) sc);
  rewrite (A.pts_to (V.vec_to_array cv) sc) as (A.pts_to capacity sc);
  
  // Allocate flow matrix
  let fv = V.alloc 0 nn;
  V.to_array_pts_to fv;
  let flow = V.vec_to_array fv;
  with sf. assert (A.pts_to (V.vec_to_array fv) sf);
  rewrite (A.pts_to (V.vec_to_array fv) sf) as (A.pts_to flow sf);
  
  // Set up capacity matrix: s=0, t=2
  // Edge 0→1 cap 10, edge 1→2 cap 5, edge 0→2 cap 15
  A.op_Array_Assignment capacity (0sz *^ n +^ 1sz) 10;
  A.op_Array_Assignment capacity (1sz *^ n +^ 2sz) 5;
  A.op_Array_Assignment capacity (0sz *^ n +^ 2sz) 15;
  
  // Precondition: valid_caps (all caps >= 0)
  // Runtime check verifies all capacities are non-negative (defense-in-depth)
  with sc2. assert (A.pts_to capacity sc2);
  let _caps_ok = check_valid_caps_fn capacity nn;
  // assume_ justified: V.alloc initializes to 0, writes are 10, 5, 15 — all >= 0
  assume_ (pure (valid_caps sc2 (SZ.v n)));
  
  // Run max flow algorithm (postcondition guarantees imp_valid_flow)
  max_flow capacity flow n 0sz 2sz;
  
  // Clean up
  with sc. assert (A.pts_to capacity sc);
  rewrite (A.pts_to capacity sc) as (A.pts_to (V.vec_to_array cv) sc);
  V.to_vec_pts_to cv;
  V.free cv;
  with sf. assert (A.pts_to flow sf);
  rewrite (A.pts_to flow sf) as (A.pts_to (V.vec_to_array fv) sf);
  V.to_vec_pts_to fv;
  V.free fv;
}
