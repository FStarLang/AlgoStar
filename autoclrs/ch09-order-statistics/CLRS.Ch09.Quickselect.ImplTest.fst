(*
   CLRS Chapter 9.2: Quickselect — Spec Validation Test

   Tests quickselect on a small concrete array [5, 2, 8].
   - test_quickselect_min: finds 0th smallest (k=0), expects 2
   - test_quickselect_max: finds 2nd smallest (k=2), expects 8
   Proves:
   - Preconditions are satisfiable
   - Postconditions are precise enough: the `result == select_spec s0 k`
     clause uniquely determines the result for concrete inputs

   Adapted from: https://github.com/microsoft/intent-formalization/blob/main/
     eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.Quickselect.fst

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

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

let select_spec_0 () : Lemma (select_spec (Seq.seq_of_list [5; 2; 8]) 0 == 2) =
  assert_norm (select_spec (Seq.seq_of_list [5; 2; 8]) 0 == 2)
let select_spec_2 () : Lemma (select_spec (Seq.seq_of_list [5; 2; 8]) 2 == 8) =
  assert_norm (select_spec (Seq.seq_of_list [5; 2; 8]) 2 == 8)

```pulse
fn test_quickselect_min ()
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

  with s0. assert (A.pts_to arr s0);

  let ctr = GR.alloc #nat 0;
  let result = quickselect arr 3sz 0sz ctr #(hide 0);
  // Postcondition: result == select_spec s0 k = select_spec [5;2;8] 0 = 2
  select_spec_0 ();
  assert (pure (result == 2));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

```pulse
fn test_quickselect_max ()
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

  with s0. assert (A.pts_to arr s0);

  let ctr = GR.alloc #nat 0;
  let result = quickselect arr 3sz 2sz ctr #(hide 0);
  select_spec_2 ();
  assert (pure (result == 8));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
