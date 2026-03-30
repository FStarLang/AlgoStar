(*
   Merge Sort - Spec Validation Test

   Tests that the postcondition of merge_sort (in Impl.fsti) is precise
   enough to determine the exact output for a small concrete input.

   Input:  [3; 1; 2]
   Expected output: [1; 2; 3]

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ sorted + permutation uniquely determines [1;2;3]
        ✓ sort_complexity_bounded cf 0 0 3 holds (cf <= ms_cost 3)
        ✓ ensures (r == true): proof guarantees the runtime check passes

     2. RUNTIME (computational, survives extraction to C):
        ✓ Reads array elements after sorting and compares to expected values
        ✓ Returns bool — caller can verify at runtime

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

#push-options "--z3rlimit 200 --fuel 6 --ifuel 2"

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
(* Spec validation: merge_sort on [3;1;2] produces [1;2;3].
   Returns bool with runtime checks that survive extraction to C. *)
fn test_merge_sort_3 ()
  requires emp
  returns r: bool
  ensures pure (r == true)
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

  // Verify complexity bound: at most ms_cost(3) = merge_sort_ops(3) = 7 comparisons
  assert (pure (cf <= 7));

  // Runtime check (survives extraction to C)
  let pass = (v0 = 1) && (v1 = 2) && (v2 = 3);

  // Cleanup
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  pass
}
```

```pulse
(* Edge case: merge_sort on empty array (len=0) does zero comparisons.
   Returns true — nothing to check at runtime for an empty array. *)
fn test_merge_sort_empty ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let v = V.alloc 0 0sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 0 0)) as (A.pts_to arr (Seq.create 0 0));

  let ctr = GR.alloc #nat 0;
  with s0. assert (A.pts_to arr s0);
  merge_sort arr 0sz ctr;

  with s. assert (A.pts_to arr s);
  with cf. assert (GR.pts_to ctr cf);

  // Zero comparisons for empty input
  assert (pure (cf == 0));

  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  true
}
```

```pulse
(* Edge case: merge_sort on single element (len=1) does zero comparisons.
   Reads the element and checks it is unchanged. *)
fn test_merge_sort_single ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let v = V.alloc 42 1sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 1 42)) as (A.pts_to arr (Seq.create 1 42));

  let ctr = GR.alloc #nat 0;
  with s0. assert (A.pts_to arr s0);
  merge_sort arr 1sz ctr;

  with s. assert (A.pts_to arr s);
  with cf. assert (GR.pts_to ctr cf);

  // Zero comparisons for single-element input
  assert (pure (cf == 0));

  // Reveal opaque permutation so Z3 can reason about the single element
  reveal_opaque (`%SS.permutation) (SS.permutation s0 s);
  SP.perm_len (reveal s0) (reveal s);

  // Read and verify element is unchanged
  let v0 = arr.(0sz);
  assert (pure (v0 == 42));
  let pass = (v0 = 42);

  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  pass
}
```

#pop-options
