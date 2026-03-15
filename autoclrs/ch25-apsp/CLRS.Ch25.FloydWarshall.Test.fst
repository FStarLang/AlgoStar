module CLRS.Ch25.FloydWarshall.Test
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch25.FloydWarshall.Spec
open CLRS.Ch25.FloydWarshall.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Test case: 3x3 graph
// Initial graph (adjacency matrix with weights):
//     0   1   2
// 0 [ 0   5  inf ]
// 1 [ 50  0   15 ]
// 2 [ 30 inf  0  ]
//
// After Floyd-Warshall:
//     0   1   2
// 0 [ 0   5   20 ]
// 1 [ 45  0   15 ]
// 2 [ 30  35  0  ]

fn test_floyd_warshall ()
  requires emp
  returns _:unit
  ensures emp
{
  let n = 3sz;
  
  // Create initial distance matrix (row-major)
  let dv = V.alloc 0 9sz;
  V.to_array_pts_to dv;
  let dist = V.vec_to_array dv;
  rewrite (A.pts_to (V.vec_to_array dv) (Seq.create 9 0)) as (A.pts_to dist (Seq.create 9 0));
  
  // Initialize matrix
  A.op_Array_Assignment dist 0sz 0;
  A.op_Array_Assignment dist 1sz 5;
  A.op_Array_Assignment dist 2sz inf;
  A.op_Array_Assignment dist 3sz 50;
  A.op_Array_Assignment dist 4sz 0;
  A.op_Array_Assignment dist 5sz 15;
  A.op_Array_Assignment dist 6sz 30;
  A.op_Array_Assignment dist 7sz inf;
  A.op_Array_Assignment dist 8sz 0;
  
  // Ghost tick counter (erased at extraction)
  let ctr = GR.alloc #nat 0;
  
  // Run Floyd-Warshall (proves correctness + complexity)
  floyd_warshall dist n ctr;
  
  // Free ghost counter
  GR.free ctr;
  
  // Clean up
  with s. assert (A.pts_to dist s);
  rewrite (A.pts_to dist s) as (A.pts_to (V.vec_to_array dv) s);
  V.to_vec_pts_to dv;
  V.free dv;
}
