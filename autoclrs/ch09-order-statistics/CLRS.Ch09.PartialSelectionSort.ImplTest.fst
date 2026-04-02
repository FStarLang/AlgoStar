(*
   CLRS Chapter 9: Partial Selection Sort — Spec Validation Test

   Tests select on a small concrete array [5, 2, 8] with k=1, k=2, k=3
   (1-indexed), expecting results 2, 5, 8 respectively.

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ result == select_spec s0 (k-1) links result to sorted input
     2. RUNTIME (computational, survives extraction to C):
        ✓ Concrete bool comparisons returned from each test function

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

inline_for_extraction
let int_eq (a b: int) : bool =
  not (Prims.op_LessThan a b || Prims.op_LessThan b a)

let int_eq_correct (a b: int)
  : Lemma (int_eq a b <==> a = b) = ()

#push-options "--z3rlimit 5 --fuel 8 --ifuel 4"

let select_spec_0 () : Lemma (select_spec (Seq.seq_of_list [5; 2; 8]) 0 == 2) =
  assert_norm (select_spec (Seq.seq_of_list [5; 2; 8]) 0 == 2)
let select_spec_1 () : Lemma (select_spec (Seq.seq_of_list [5; 2; 8]) 1 == 5) =
  assert_norm (select_spec (Seq.seq_of_list [5; 2; 8]) 1 == 5)
let select_spec_2 () : Lemma (select_spec (Seq.seq_of_list [5; 2; 8]) 2 == 8) =
  assert_norm (select_spec (Seq.seq_of_list [5; 2; 8]) 2 == 8)

```pulse
fn test_select_k1 ()
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
  let result = select arr 3sz 1sz ctr #(hide 0);
  select_spec_0 ();
  assert (pure (result == 2));

  int_eq_correct result 2;
  let ok = int_eq result 2;

  with s_final cf. assert (A.pts_to arr s_final ** GR.pts_to ctr cf);
  GR.free ctr;
  rewrite (A.pts_to arr s_final) as (A.pts_to (V.vec_to_array v) s_final);
  V.to_vec_pts_to v;
  V.free v;
  ok
}
```

```pulse
fn test_select_k2 ()
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
  let result = select arr 3sz 2sz ctr #(hide 0);
  select_spec_1 ();
  assert (pure (result == 5));

  int_eq_correct result 5;
  let ok = int_eq result 5;

  with s_final cf. assert (A.pts_to arr s_final ** GR.pts_to ctr cf);
  GR.free ctr;
  rewrite (A.pts_to arr s_final) as (A.pts_to (V.vec_to_array v) s_final);
  V.to_vec_pts_to v;
  V.free v;
  ok
}
```

```pulse
fn test_select_k3 ()
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
  let result = select arr 3sz 3sz ctr #(hide 0);
  select_spec_2 ();
  assert (pure (result == 8));

  int_eq_correct result 8;
  let ok = int_eq result 8;

  with s_final cf. assert (A.pts_to arr s_final ** GR.pts_to ctr cf);
  GR.free ctr;
  rewrite (A.pts_to arr s_final) as (A.pts_to (V.vec_to_array v) s_final);
  V.to_vec_pts_to v;
  V.free v;
  ok
}
```

#pop-options
