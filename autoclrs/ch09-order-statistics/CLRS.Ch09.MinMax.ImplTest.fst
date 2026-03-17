(*
   CLRS Chapter 9.1: MINIMUM / MAXIMUM — Spec Validation Test

   Tests find_minimum and find_maximum on a small concrete array [5, 2, 8].
   Proves:
   - Preconditions are satisfiable
   - Postconditions are precise enough to determine the exact output
     (min_val == 2, max_val == 8) for the given input

   Adapted from: https://github.com/microsoft/intent-formalization/blob/main/
     eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.MinMax.fst

   NO admits. NO assumes.
*)
module CLRS.Ch09.MinMax.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch09.MinMax.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

```pulse
fn test_find_minimum ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 5;
  arr.(1sz) <- 2;
  arr.(2sz) <- 8;

  // Bind input ghost state (pattern from working ch07 test)
  with s0. assert (A.pts_to arr s0);

  let ctr = GR.alloc #nat 0;
  let min_val = find_minimum arr 3sz ctr #(hide 0);
  // Postcondition: min_val exists in array AND min_val <= all elements
  // For [5, 2, 8], min = 2
  assert (pure (min_val == 2));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

```pulse
fn test_find_maximum ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 5;
  arr.(1sz) <- 2;
  arr.(2sz) <- 8;

  // Bind input ghost state
  with s0. assert (A.pts_to arr s0);

  let ctr = GR.alloc #nat 0;
  let max_val = find_maximum arr 3sz ctr #(hide 0);
  // Postcondition: max_val exists in array AND max_val >= all elements
  // For [5, 2, 8], max = 8
  assert (pure (max_val == 8));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
