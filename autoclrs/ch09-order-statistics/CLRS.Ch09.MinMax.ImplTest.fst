(*
   CLRS Chapter 9.1: MINIMUM / MAXIMUM — Spec Validation Test

   Tests find_minimum and find_maximum on a small concrete array [5, 2, 8].

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ Postcondition proves min_val == 2, max_val == 8
     2. RUNTIME (computational, survives extraction to C):
        ✓ Concrete bool comparisons returned from each test function

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

(* Concrete int equality — survives extraction to C *)
inline_for_extraction
let int_eq (a b: int) : bool =
  not (Prims.op_LessThan a b || Prims.op_LessThan b a)

let int_eq_correct (a b: int)
  : Lemma (int_eq a b <==> a = b) = ()

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

```pulse
fn test_find_minimum ()
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
  let min_val = find_minimum arr 3sz ctr #(hide 0);
  // Ghost proof: min_val == 2 (erased at extraction)
  assert (pure (min_val == 2));

  // Concrete check: survives extraction to C
  int_eq_correct min_val 2;
  let ok = int_eq min_val 2;

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
fn test_find_maximum ()
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
  let max_val = find_maximum arr 3sz ctr #(hide 0);
  // Ghost proof: max_val == 8 (erased at extraction)
  assert (pure (max_val == 8));

  // Concrete check: survives extraction to C
  int_eq_correct max_val 8;
  let ok = int_eq max_val 8;

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
