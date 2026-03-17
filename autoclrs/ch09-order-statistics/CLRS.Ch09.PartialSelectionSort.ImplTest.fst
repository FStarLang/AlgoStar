(*
   CLRS Chapter 9: Partial Selection Sort — Spec Validation Test

   Tests select on a small concrete array [5, 2, 8] with k=1, k=2, k=3
   (1-indexed), expecting results 2, 5, 8 respectively.

   The strengthened postcondition of select includes
   result == select_spec s0 (k-1), which directly links the result to the
   sorted input, making spec validation trivial via assert_norm.

   Adapted from: https://github.com/microsoft/intent-formalization/blob/main/
     eval-autoclrs-specs/intree-tests/ch09-order-statistics/Test.PartialSelectionSort.fst

   NO admits. NO assumes.
*)
module CLRS.Ch09.PartialSelectionSort.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch09.PartialSelectionSort.Impl
open CLRS.Ch09.PartialSelectionSort.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

let select_spec_0 () : Lemma (select_spec (Seq.seq_of_list [5; 2; 8]) 0 == 2) =
  assert_norm (select_spec (Seq.seq_of_list [5; 2; 8]) 0 == 2)
let select_spec_1 () : Lemma (select_spec (Seq.seq_of_list [5; 2; 8]) 1 == 5) =
  assert_norm (select_spec (Seq.seq_of_list [5; 2; 8]) 1 == 5)
let select_spec_2 () : Lemma (select_spec (Seq.seq_of_list [5; 2; 8]) 2 == 8) =
  assert_norm (select_spec (Seq.seq_of_list [5; 2; 8]) 2 == 8)

```pulse
fn test_select_k1 ()
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
  let result = select arr 3sz 1sz ctr #(hide 0);
  // Postcondition: result == select_spec s0 (k-1) = select_spec [5;2;8] 0 = 2
  select_spec_0 ();
  assert (pure (result == 2));

  with s_final cf. assert (A.pts_to arr s_final ** GR.pts_to ctr cf);
  GR.free ctr;
  rewrite (A.pts_to arr s_final) as (A.pts_to (V.vec_to_array v) s_final);
  V.to_vec_pts_to v;
  V.free v;
}
```

```pulse
fn test_select_k2 ()
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
  let result = select arr 3sz 2sz ctr #(hide 0);
  // Postcondition: result == select_spec s0 (k-1) = select_spec [5;2;8] 1 = 5
  select_spec_1 ();
  assert (pure (result == 5));

  with s_final cf. assert (A.pts_to arr s_final ** GR.pts_to ctr cf);
  GR.free ctr;
  rewrite (A.pts_to arr s_final) as (A.pts_to (V.vec_to_array v) s_final);
  V.to_vec_pts_to v;
  V.free v;
}
```

```pulse
fn test_select_k3 ()
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
  let result = select arr 3sz 3sz ctr #(hide 0);
  // Postcondition: result == select_spec s0 (k-1) = select_spec [5;2;8] 2 = 8
  select_spec_2 ();
  assert (pure (result == 8));

  with s_final cf. assert (A.pts_to arr s_final ** GR.pts_to ctr cf);
  GR.free ctr;
  rewrite (A.pts_to arr s_final) as (A.pts_to (V.vec_to_array v) s_final);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
