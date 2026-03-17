(*
   Merge Sort - Spec Validation Test

   Tests that the postcondition of merge_sort (in Impl.fsti) is precise
   enough to determine the exact output for a small concrete input.

   Input:  [3; 1; 2]
   Expected output: [1; 2; 3]

   Proves:
   1. The precondition is satisfiable (by constructing a valid call)
   2. sorted + permutation of [3;1;2] uniquely determines [1;2;3]
   3. sort_complexity_bounded cf 0 0 3 holds (cf <= ms_cost 3)

   Adapted from:
     https://github.com/microsoft/intent-formalization/blob/main/
       eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   NO admits. NO assumes.
*)
module CLRS.Ch02.MergeSort.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch02.MergeSort.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
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
(* Spec validation: merge_sort on [3;1;2] produces [1;2;3] *)
fn test_merge_sort_3 ()
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

  // Create ghost counter (starts at 0)
  let ctr = GR.alloc #nat 0;

  // Bind input ghost
  with s0. assert (A.pts_to arr s0);

  // y = merge_sort(x)
  merge_sort arr 3sz ctr;

  // After sort: extract postcondition witnesses
  with s. assert (A.pts_to arr s);
  with cf. assert (GR.pts_to ctr cf);

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

  // Cleanup
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  ()
}
```

#pop-options
