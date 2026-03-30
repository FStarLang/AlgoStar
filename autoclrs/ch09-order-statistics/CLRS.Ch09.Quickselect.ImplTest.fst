(*
   CLRS Chapter 9.2: Quickselect — Spec Validation Test

   Tests quickselect on a small concrete array [5, 2, 8].
   - test_quickselect_min: finds 0th smallest (k=0), expects 2
   - test_quickselect_max: finds 2nd smallest (k=2), expects 8

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ result == select_spec s0 k uniquely determines the result
     2. RUNTIME (computational, survives extraction to C):
        ✓ Concrete bool comparisons returned from each test function

   NO admits. NO assumes.
*)
module CLRS.Ch09.Quickselect.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch09.Quickselect.Impl
open CLRS.Ch09.PartialSelectionSort.Spec

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

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

let select_spec_0 () : Lemma (select_spec (Seq.seq_of_list [5; 2; 8]) 0 == 2) =
  assert_norm (select_spec (Seq.seq_of_list [5; 2; 8]) 0 == 2)
let select_spec_2 () : Lemma (select_spec (Seq.seq_of_list [5; 2; 8]) 2 == 8) =
  assert_norm (select_spec (Seq.seq_of_list [5; 2; 8]) 2 == 8)

```pulse
fn test_quickselect_min ()
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
  let result = quickselect arr 3sz 0sz ctr #(hide 0);
  select_spec_0 ();
  assert (pure (result == 2));

  int_eq_correct result 2;
  let ok = int_eq result 2;

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
fn test_quickselect_max ()
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
  let result = quickselect arr 3sz 2sz ctr #(hide 0);
  select_spec_2 ();
  assert (pure (result == 8));

  int_eq_correct result 8;
  let ok = int_eq result 8;

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
