(*
   CLRS Chapter 9.1: Simultaneous Min and Max — Spec Validation Test

   Tests find_minmax and find_minmax_pairs on a small concrete array [5, 2, 8].

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ min_val == 2 and max_val == 8 proved from postcondition
     2. RUNTIME (computational, survives extraction to C):
        ✓ Concrete bool comparisons returned from each test function

   NO admits. NO assumes.
*)
module CLRS.Ch09.SimultaneousMinMax.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch09.SimultaneousMinMax.Impl
open CLRS.Ch09.SimultaneousMinMax.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference

inline_for_extraction
let int_eq (a b: int) : bool =
  not (Prims.op_LessThan a b || Prims.op_LessThan b a)

let int_eq_correct (a b: int)
  : Lemma (int_eq a b <==> a = b) = ()

#push-options "--z3rlimit 5 --fuel 8 --ifuel 4"

```pulse
fn test_find_minmax ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 5;
  arr.(1sz) <- 2;
  arr.(2sz) <- 8;

  with s0. assert (A.pts_to arr s0);

  let ctr = GR.alloc #nat 0;
  let result = find_minmax arr 3sz ctr #(hide 0);
  assert (pure (result.min_val == 2));
  assert (pure (result.max_val == 8));

  int_eq_correct result.min_val 2;
  int_eq_correct result.max_val 8;
  let ok = int_eq result.min_val 2 && int_eq result.max_val 8;

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  ok
}
```

```pulse
fn test_find_minmax_pairs ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 5;
  arr.(1sz) <- 2;
  arr.(2sz) <- 8;

  with s0. assert (A.pts_to arr s0);

  let ctr = GR.alloc #nat 0;
  let result = find_minmax_pairs arr 3sz ctr #(hide 0);
  assert (pure (result.min_val == 2));
  assert (pure (result.max_val == 8));

  int_eq_correct result.min_val 2;
  int_eq_correct result.max_val 8;
  let ok = int_eq result.min_val 2 && int_eq result.max_val 8;

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  ok
}
```

#pop-options
