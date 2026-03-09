(*
   Test file for verified binary search
*)

module Test.BinarySearch
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch04.BinarySearch.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Test helper: create a sorted array [1, 2, 3, 4, 5]
fn test_binary_search_found ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 1 5sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 5 1)) as (A.pts_to arr (Seq.create 5 1));
  arr.(0sz) <- 1;
  arr.(1sz) <- 2;
  arr.(2sz) <- 3;
  arr.(3sz) <- 4;
  arr.(4sz) <- 5;
  
  // Search for 3 - should find it at index 2
  let ctr = GR.alloc #nat 0;
  let result = binary_search arr 5sz 3 ctr;
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  
  // Clean up
  with s. assert (A.pts_to arr s);
  rewrite (A.pts_to arr s) as (A.pts_to (V.vec_to_array v) s);
  V.to_vec_pts_to v;
  V.free v;
  ()
}

// Test: search for element not in array
fn test_binary_search_not_found ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 10 5sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 5 10)) as (A.pts_to arr (Seq.create 5 10));
  arr.(0sz) <- 10;
  arr.(1sz) <- 20;
  arr.(2sz) <- 30;
  arr.(3sz) <- 40;
  arr.(4sz) <- 50;
  
  // Search for 25 - should not find it (return 5)
  let ctr = GR.alloc #nat 0;
  let result = binary_search arr 5sz 25 ctr;
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  
  // Clean up
  with s. assert (A.pts_to arr s);
  rewrite (A.pts_to arr s) as (A.pts_to (V.vec_to_array v) s);
  V.to_vec_pts_to v;
  V.free v;
  ()
}
