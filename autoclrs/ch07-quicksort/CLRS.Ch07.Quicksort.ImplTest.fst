(*
   CLRS Chapter 7: Quicksort — Spec Validation Test

   Adapted from:
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   Tests that the quicksort API's postcondition (sorted + permutation)
   is satisfiable and sufficiently precise to determine the output
   for a concrete 3-element input [3; 1; 2] -> [1; 2; 3].

   Also tests quicksort_with_complexity (O(n²) bound) and
   quicksort_bounded (sub-range sorting with bounds preservation).
*)
module CLRS.Ch07.Quicksort.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch07.Quicksort.Impl
open CLRS.Ch07.Partition.Lemmas
open CLRS.Ch07.Quicksort.Lemmas

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module GR = Pulse.Lib.GhostReference
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module SS = CLRS.Common.SortSpec

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

(* Pure helper: sorted + permutation of [3;1;2] uniquely determines [1;2;3].
   Uses explicit Prims operators so Z3 can reason about element ordering. *)
let std_sort3 (s: Seq.seq int)
  : Lemma
    (requires (forall (i j:nat). Prims.op_LessThanOrEqual i j /\
                                 Prims.op_LessThan j (Seq.length s) ==>
                                 Prims.op_LessThanOrEqual (Seq.index s i) (Seq.index s j)) /\
              SP.permutation int (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= SP.perm_len (Seq.seq_of_list [3; 1; 2]) s;
  assert_norm (SP.count 1 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 2 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 3 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 0 (Seq.seq_of_list [3; 1; 2]) == 0);
  assert_norm (SP.count 4 (Seq.seq_of_list [3; 1; 2]) == 0)

(* Completeness lemma: bridges BoundedIntegers typeclass operators in SS.sorted
   to standard Prims operators for Z3 reasoning *)
let completeness_sort3 (s: Seq.seq int)
  : Lemma
    (requires SS.sorted s /\ SP.permutation int (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (i j:nat). (i < j) == Prims.op_LessThan i j);
  assert (forall (x y:int). (x <= y) == Prims.op_LessThanOrEqual x y);
  assert (forall (x y:int). (x < y) == Prims.op_LessThan x y);
  std_sort3 s

```pulse
(* Completeness: y = quicksort(x); assert(y == expected) *)
fn test_quicksort_3 ()
  requires emp
  returns _: unit
  ensures emp
{
  // Input: [3; 1; 2]
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  // Bind input ghost
  with s0. assert (A.pts_to arr s0);

  // y = quicksort(x)
  quicksort arr 3sz;

  // assert(y == expected)
  with s. assert (A.pts_to arr s);
  // Reveal opaque CLRS.permutation to get SP.permutation
  reveal_opaque (`%SS.permutation) (SS.permutation s0 s);
  // Now Z3 sees: SP.permutation int s0 s, and knows s0 == [3;1;2] from array writes
  completeness_sort3 s;

  // Read and verify each element
  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 3));

  // cleanup
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  ()
}
```

(* Completeness: quicksort_with_complexity exposes O(n²) bound via ghost counter *)
```pulse
fn test_quicksort_with_complexity ()
  requires emp
  returns _: unit
  ensures emp
{
  // Input: [3; 1; 2]
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  with s0. assert (A.pts_to arr s0);

  // Create ghost counter starting at 0
  let ctr = GR.alloc #nat 0;

  // y = quicksort_with_complexity(x)
  quicksort_with_complexity arr 3sz ctr #(hide 0);

  // Bind existential witnesses
  with s. assert (A.pts_to arr s);
  with cf. assert (GR.pts_to ctr cf);

  // === Verify postcondition properties ===

  // 1. Sorted output
  assert (pure (SS.sorted s));

  // 2. Permutation of input
  assert (pure (SS.permutation s0 s));

  // 3. Complexity bound: cf <= n*(n-1)/2 = 3*2/2 = 3
  assert (pure (complexity_bounded_quadratic cf 0 3));

  // 4. Completeness: output is uniquely [1; 2; 3]
  reveal_opaque (`%SS.permutation) (SS.permutation s0 s);
  completeness_sort3 s;
  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 3));

  // Cleanup
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  ()
}
```

(* Completeness: quicksort_bounded preserves between_bounds in postcondition *)
```pulse
fn test_quicksort_bounded ()
  requires emp
  returns _: unit
  ensures emp
{
  // Input: [3; 1; 2]
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  // Convert pts_to -> pts_to_range for bounded API
  with s0. assert (A.pts_to arr s0);
  A.pts_to_range_intro arr 1.0R s0;

  // Call quicksort_bounded: lo=0, hi=3, bounds [1, 3]
  quicksort_bounded arr 0 3 (hide 1) (hide 3);

  // Bind existential witnesses
  with s. assert (A.pts_to_range arr 0 3 s);

  // === Verify postcondition properties ===

  // 1. Sorted output
  assert (pure (SS.sorted s));

  // 2. Permutation of input
  assert (pure (SS.permutation s0 s));

  // 3. Bounds preservation: output elements remain in [1, 3]
  assert (pure (between_bounds s 1 3));

  // 4. Completeness: output is [1; 2; 3]
  reveal_opaque (`%SS.permutation) (SS.permutation s0 s);
  completeness_sort3 s;

  // Convert back and cleanup
  A.pts_to_range_elim arr 1.0R s;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  ()
}
```

#pop-options
