(*
   Counting Sort — Spec Validation Tests (CLRS §8.2)

   Tests for CLRS.Ch08.CountingSort.Impl.fsti:
   1. counting_sort_inplace: Input [3;1;2] → Output [1;2;3]
   2. counting_sort_impl: Input [3;1;2] → Output [1;2;3] (CLRS-faithful, separate I/O)

   Proves:
   - Preconditions are satisfiable (concrete inputs accepted)
   - Postconditions are precise (sorted + permutation uniquely determines output)

   Adapted from:
   https://github.com/microsoft/intent-formalization/blob/main/
   eval-autoclrs-specs/intree-tests/ch08-linear-sorting/Test.CountingSort.fst

   NO admits. NO assumes.
*)
module CLRS.Ch08.CountingSort.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch08.CountingSort.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module S = CLRS.Ch08.CountingSort.Spec

// ========== Pure Helper Lemmas ==========

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

(* A sorted nat-permutation of [3;1;2] must be [1;2;3].
   Proved via element counts: each of {1,2,3} appears exactly once,
   and neither 0 nor 4 appear, so sorted order is forced. *)
let std_sort3_nat (s: Seq.seq nat)
  : Lemma
    (requires Seq.length s == 3 /\
              (forall (i j:nat). Prims.op_LessThanOrEqual i j /\
                                 Prims.op_LessThan j 3 ==>
                                 Prims.op_LessThanOrEqual (Seq.index s i) (Seq.index s j)) /\
              SP.permutation nat (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= SP.perm_len (Seq.seq_of_list [3; 1; 2]) s;
  assert_norm (SP.count 1 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 2 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 3 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count #nat 0 (Seq.seq_of_list [3; 1; 2]) == 0);
  assert_norm (SP.count #nat 4 (Seq.seq_of_list [3; 1; 2]) == 0)

(* Concrete sequence with known element values equals seq_of_list [3;1;2] *)
let input_is_sort3 (s0: Seq.seq nat)
  : Lemma
    (requires Seq.length s0 == 3 /\
              Seq.index s0 0 == 3 /\
              Seq.index s0 1 == 1 /\
              Seq.index s0 2 == 2)
    (ensures Seq.equal s0 (Seq.seq_of_list [3; 1; 2]))
= assert_norm (Seq.length (Seq.seq_of_list [3; 1; 2]) == 3);
  Seq.lemma_eq_intro s0 (Seq.seq_of_list [3; 1; 2])

(* Completeness for counting_sort_inplace:
   postcondition gives S.permutation s0 s (input → output) *)
let completeness_inplace (s0 s: Seq.seq nat)
  : Lemma
    (requires Seq.length s0 == 3 /\
              Seq.index s0 0 == 3 /\
              Seq.index s0 1 == 1 /\
              Seq.index s0 2 == 2 /\
              Seq.length s == 3 /\
              S.sorted s /\
              S.permutation s0 s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= input_is_sort3 s0;
  Seq.lemma_eq_elim s0 (Seq.seq_of_list [3; 1; 2]);
  reveal_opaque (`%S.permutation) (S.permutation s0 s);
  assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (x y:nat). (x <= y) == Prims.op_LessThanOrEqual x y);
  std_sort3_nat s

(* Completeness for counting_sort_impl:
   postcondition gives S.permutation sa sb' (input → output) *)
let completeness_impl (sa sb': Seq.seq nat)
  : Lemma
    (requires Seq.length sa == 3 /\
              Seq.index sa 0 == 3 /\
              Seq.index sa 1 == 1 /\
              Seq.index sa 2 == 2 /\
              Seq.length sb' == 3 /\
              S.sorted sb' /\
              S.permutation sa sb')
    (ensures Seq.index sb' 0 == 1 /\ Seq.index sb' 1 == 2 /\ Seq.index sb' 2 == 3)
= input_is_sort3 sa;
  Seq.lemma_eq_elim sa (Seq.seq_of_list [3; 1; 2]);
  reveal_opaque (`%S.permutation) (S.permutation sa sb');
  assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (x y:nat). (x <= y) == Prims.op_LessThanOrEqual x y);
  std_sort3_nat sb'

// ========== Test 1: counting_sort_inplace ==========

```pulse
fn test_counting_sort_inplace ()
  requires emp
  returns _: unit
  ensures emp
{
  // Allocate input array [3;1;2]
  let v = V.alloc #nat 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0))
       as (A.pts_to arr (Seq.create #nat 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  with s0. assert (A.pts_to arr s0);
  A.pts_to_len arr;
  assert (pure (A.length arr == SZ.v 3sz));
  assert (pure (Seq.length s0 == 3));

  // Sort in place: precondition satisfied with k_val=4, all elements ≤ 4
  counting_sort_inplace arr 3sz 4sz;

  // Verify postcondition uniquely determines output [1;2;3]
  with s. assert (A.pts_to arr s);
  A.pts_to_len arr;
  assert (pure (Seq.length s == 3));
  completeness_inplace s0 s;

  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 3));

  // Verify in_range postcondition: all output elements ≤ k_val=4
  assert (pure (S.in_range s 4));
  assert (pure (v0 <= 4 /\ v1 <= 4 /\ v2 <= 4));

  // Cleanup
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

// ========== Test 2: counting_sort_impl (CLRS-faithful, separate I/O) ==========

```pulse
fn test_counting_sort_impl ()
  requires emp
  returns _: unit
  ensures emp
{
  // Allocate input array [3;1;2]
  let va = V.alloc #nat 0 3sz;
  V.to_array_pts_to va;
  let a = V.vec_to_array va;
  rewrite (A.pts_to (V.vec_to_array va) (Seq.create 3 0))
       as (A.pts_to a (Seq.create #nat 3 0));
  a.(0sz) <- 3;
  a.(1sz) <- 1;
  a.(2sz) <- 2;

  // Allocate output array [0;0;0]
  let vb = V.alloc #nat 0 3sz;
  V.to_array_pts_to vb;
  let b = V.vec_to_array vb;
  rewrite (A.pts_to (V.vec_to_array vb) (Seq.create 3 0))
       as (A.pts_to b (Seq.create #nat 3 0));

  with sa. assert (A.pts_to a sa);
  with sb. assert (A.pts_to b sb);
  A.pts_to_len a;
  A.pts_to_len b;

  // Share input array for half permission (counting_sort_impl requires #0.5R)
  A.share a;

  // Sort a into b with k_val=3 (tightest valid bound: max element is 3)
  counting_sort_impl a b 3sz 3sz;

  // Gather input array back to full permission
  A.gather a;

  // Verify output in b uniquely determined as [1;2;3]
  with sb'. assert (A.pts_to b sb');
  A.pts_to_len b;
  completeness_impl sa sb';

  let v0 = b.(0sz);
  let v1 = b.(1sz);
  let v2 = b.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 3));

  // Verify in_range postcondition: all output elements ≤ k_val=3
  assert (pure (S.in_range sb' 3));
  assert (pure (v0 <= 3 /\ v1 <= 3 /\ v2 <= 3));

  // Cleanup: free both arrays
  with sa2. assert (A.pts_to a sa2);
  rewrite (A.pts_to a sa2) as (A.pts_to (V.vec_to_array va) sa2);
  V.to_vec_pts_to va;
  V.free va;

  with sb2. assert (A.pts_to b sb2);
  rewrite (A.pts_to b sb2) as (A.pts_to (V.vec_to_array vb) sb2);
  V.to_vec_pts_to vb;
  V.free vb;
}
```

#pop-options
