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

(** Test 1: 3-vertex graph with two paths (original smoke test).
    s=0, t=2. Edges: 0→1 cap 10, 1→2 cap 5, 0→2 cap 15.
    Expected max flow = 20 (15 via 0→2 + 5 via 0→1→2). *)
fn test_max_flow_3v ()
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

  // Prove valid_caps via runtime check + intro lemma (no assume_)
  with sc2. assert (A.pts_to capacity sc2);
  let caps_ok = check_valid_caps_fn capacity nn;
  if caps_ok {
    valid_caps_intro sc2 (SZ.v n);
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
  } else {
    // Caps are valid by construction; this branch is unreachable
    with sc. assert (A.pts_to capacity sc);
    rewrite (A.pts_to capacity sc) as (A.pts_to (V.vec_to_array cv) sc);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf. assert (A.pts_to flow sf);
    rewrite (A.pts_to flow sf) as (A.pts_to (V.vec_to_array fv) sf);
    V.to_vec_pts_to fv;
    V.free fv;
  }
}

(** Test 2: Disconnected graph — no path from source to sink.
    s=0, t=2. No edges. Expected max flow = 0. *)
fn test_max_flow_disconnected ()
  requires emp
  returns _:unit
  ensures emp
{
  let n : SZ.t = 3sz;
  let nn : SZ.t = n *^ n;

  let cv = V.alloc 0 nn;
  V.to_array_pts_to cv;
  let capacity = V.vec_to_array cv;
  with sc. assert (A.pts_to (V.vec_to_array cv) sc);
  rewrite (A.pts_to (V.vec_to_array cv) sc) as (A.pts_to capacity sc);

  let fv = V.alloc 0 nn;
  V.to_array_pts_to fv;
  let flow = V.vec_to_array fv;
  with sf. assert (A.pts_to (V.vec_to_array fv) sf);
  rewrite (A.pts_to (V.vec_to_array fv) sf) as (A.pts_to flow sf);

  // No edges — all capacities remain 0 (disconnected graph)
  with sc2. assert (A.pts_to capacity sc2);
  let caps_ok = check_valid_caps_fn capacity nn;
  if caps_ok {
    valid_caps_intro sc2 (SZ.v n);
    max_flow capacity flow n 0sz 2sz;
    with sc. assert (A.pts_to capacity sc);
    rewrite (A.pts_to capacity sc) as (A.pts_to (V.vec_to_array cv) sc);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf. assert (A.pts_to flow sf);
    rewrite (A.pts_to flow sf) as (A.pts_to (V.vec_to_array fv) sf);
    V.to_vec_pts_to fv;
    V.free fv;
  } else {
    with sc. assert (A.pts_to capacity sc);
    rewrite (A.pts_to capacity sc) as (A.pts_to (V.vec_to_array cv) sc);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf. assert (A.pts_to flow sf);
    rewrite (A.pts_to flow sf) as (A.pts_to (V.vec_to_array fv) sf);
    V.to_vec_pts_to fv;
    V.free fv;
  }
}

(** Test 3: Single edge network.
    s=0, t=1. Edge 0→1 cap 7. Expected max flow = 7. *)
fn test_max_flow_single_edge ()
  requires emp
  returns _:unit
  ensures emp
{
  let n : SZ.t = 2sz;
  let nn : SZ.t = n *^ n;

  let cv = V.alloc 0 nn;
  V.to_array_pts_to cv;
  let capacity = V.vec_to_array cv;
  with sc. assert (A.pts_to (V.vec_to_array cv) sc);
  rewrite (A.pts_to (V.vec_to_array cv) sc) as (A.pts_to capacity sc);

  let fv = V.alloc 0 nn;
  V.to_array_pts_to fv;
  let flow = V.vec_to_array fv;
  with sf. assert (A.pts_to (V.vec_to_array fv) sf);
  rewrite (A.pts_to (V.vec_to_array fv) sf) as (A.pts_to flow sf);

  // Edge 0→1 cap 7
  A.op_Array_Assignment capacity 1sz 7;

  with sc2. assert (A.pts_to capacity sc2);
  let caps_ok = check_valid_caps_fn capacity nn;
  if caps_ok {
    valid_caps_intro sc2 (SZ.v n);
    max_flow capacity flow n 0sz 1sz;
    with sc. assert (A.pts_to capacity sc);
    rewrite (A.pts_to capacity sc) as (A.pts_to (V.vec_to_array cv) sc);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf. assert (A.pts_to flow sf);
    rewrite (A.pts_to flow sf) as (A.pts_to (V.vec_to_array fv) sf);
    V.to_vec_pts_to fv;
    V.free fv;
  } else {
    with sc. assert (A.pts_to capacity sc);
    rewrite (A.pts_to capacity sc) as (A.pts_to (V.vec_to_array cv) sc);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf. assert (A.pts_to flow sf);
    rewrite (A.pts_to flow sf) as (A.pts_to (V.vec_to_array fv) sf);
    V.to_vec_pts_to fv;
    V.free fv;
  }
}

(** Test 4: Diamond graph with 4 vertices, multiple paths.
    s=0, t=3. Edges: 0→1 cap 10, 0→2 cap 10, 1→3 cap 10, 2→3 cap 10.
    Expected max flow = 20 (10 via 0→1→3 + 10 via 0→2→3). *)
fn test_max_flow_diamond ()
  requires emp
  returns _:unit
  ensures emp
{
  let n : SZ.t = 4sz;
  let nn : SZ.t = n *^ n;

  let cv = V.alloc 0 nn;
  V.to_array_pts_to cv;
  let capacity = V.vec_to_array cv;
  with sc. assert (A.pts_to (V.vec_to_array cv) sc);
  rewrite (A.pts_to (V.vec_to_array cv) sc) as (A.pts_to capacity sc);

  let fv = V.alloc 0 nn;
  V.to_array_pts_to fv;
  let flow = V.vec_to_array fv;
  with sf. assert (A.pts_to (V.vec_to_array fv) sf);
  rewrite (A.pts_to (V.vec_to_array fv) sf) as (A.pts_to flow sf);

  // 0→1 cap 10, 0→2 cap 10, 1→3 cap 10, 2→3 cap 10
  A.op_Array_Assignment capacity (0sz *^ n +^ 1sz) 10;
  A.op_Array_Assignment capacity (0sz *^ n +^ 2sz) 10;
  A.op_Array_Assignment capacity (1sz *^ n +^ 3sz) 10;
  A.op_Array_Assignment capacity (2sz *^ n +^ 3sz) 10;

  with sc2. assert (A.pts_to capacity sc2);
  let caps_ok = check_valid_caps_fn capacity nn;
  if caps_ok {
    valid_caps_intro sc2 (SZ.v n);
    max_flow capacity flow n 0sz 3sz;
    with sc. assert (A.pts_to capacity sc);
    rewrite (A.pts_to capacity sc) as (A.pts_to (V.vec_to_array cv) sc);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf. assert (A.pts_to flow sf);
    rewrite (A.pts_to flow sf) as (A.pts_to (V.vec_to_array fv) sf);
    V.to_vec_pts_to fv;
    V.free fv;
  } else {
    with sc. assert (A.pts_to capacity sc);
    rewrite (A.pts_to capacity sc) as (A.pts_to (V.vec_to_array cv) sc);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf. assert (A.pts_to flow sf);
    rewrite (A.pts_to flow sf) as (A.pts_to (V.vec_to_array fv) sf);
    V.to_vec_pts_to fv;
    V.free fv;
  }
}

(** Test 5: Bottleneck graph — capacity limited by middle edge.
    s=0, t=2. Edges: 0→1 cap 100, 1→2 cap 1. Expected max flow = 1. *)
fn test_max_flow_bottleneck ()
  requires emp
  returns _:unit
  ensures emp
{
  let n : SZ.t = 3sz;
  let nn : SZ.t = n *^ n;

  let cv = V.alloc 0 nn;
  V.to_array_pts_to cv;
  let capacity = V.vec_to_array cv;
  with sc. assert (A.pts_to (V.vec_to_array cv) sc);
  rewrite (A.pts_to (V.vec_to_array cv) sc) as (A.pts_to capacity sc);

  let fv = V.alloc 0 nn;
  V.to_array_pts_to fv;
  let flow = V.vec_to_array fv;
  with sf. assert (A.pts_to (V.vec_to_array fv) sf);
  rewrite (A.pts_to (V.vec_to_array fv) sf) as (A.pts_to flow sf);

  // 0→1 cap 100, 1→2 cap 1
  A.op_Array_Assignment capacity (0sz *^ n +^ 1sz) 100;
  A.op_Array_Assignment capacity (1sz *^ n +^ 2sz) 1;

  with sc2. assert (A.pts_to capacity sc2);
  let caps_ok = check_valid_caps_fn capacity nn;
  if caps_ok {
    valid_caps_intro sc2 (SZ.v n);
    max_flow capacity flow n 0sz 2sz;
    with sc. assert (A.pts_to capacity sc);
    rewrite (A.pts_to capacity sc) as (A.pts_to (V.vec_to_array cv) sc);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf. assert (A.pts_to flow sf);
    rewrite (A.pts_to flow sf) as (A.pts_to (V.vec_to_array fv) sf);
    V.to_vec_pts_to fv;
    V.free fv;
  } else {
    with sc. assert (A.pts_to capacity sc);
    rewrite (A.pts_to capacity sc) as (A.pts_to (V.vec_to_array cv) sc);
    V.to_vec_pts_to cv;
    V.free cv;
    with sf. assert (A.pts_to flow sf);
    rewrite (A.pts_to flow sf) as (A.pts_to (V.vec_to_array fv) sf);
    V.to_vec_pts_to fv;
    V.free fv;
  }
}
