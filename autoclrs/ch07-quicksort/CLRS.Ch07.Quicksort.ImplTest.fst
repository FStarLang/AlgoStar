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

(* Runtime integer equality check that survives KaRaMeL extraction to C *)
inline_for_extraction
let int_eq (a b: int) : (r:bool{r <==> a = b}) = a = b

(* Completeness lemma: sorted + permutation of [3;1;2] uniquely determines [1;2;3].
   Bridges BoundedIntegers typeclass operators (used in SS.sorted) to Prims operators,
   and uses Prims.op_Equality in assert_norm so the normalizer can reduce SP.count.
   Uses pointwise sorted assertions instead of quantifier bridging for efficiency. *)
#push-options "--fuel 8 --z3rlimit 20"
let completeness_sort3 (s: Seq.seq int)
  : Lemma
    (requires SS.sorted s /\ SP.permutation int (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= // Permutation preserves length
  SP.perm_len (Seq.seq_of_list [3; 1; 2]) s;
  // Bridge BoundedIntegers <= to Prims <= so Z3 can use sorted pointwise
  assert (forall (x y:int). (x <= y) == Prims.op_LessThanOrEqual x y);
  assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (i j:nat). (i < j) == Prims.op_LessThan i j);
  // Instantiate sorted at specific index pairs (avoids expensive quantifier chaining)
  assert (Prims.op_LessThanOrEqual (Seq.index s 0) (Seq.index s 1));
  assert (Prims.op_LessThanOrEqual (Seq.index s 0) (Seq.index s 2));
  assert (Prims.op_LessThanOrEqual (Seq.index s 1) (Seq.index s 2));
  // Use Prims.op_Equality so the normalizer can reduce SP.count on concrete input
  assert_norm (Prims.op_Equality #int (SP.count 1 (Seq.seq_of_list [3; 1; 2])) 1);
  assert_norm (Prims.op_Equality #int (SP.count 2 (Seq.seq_of_list [3; 1; 2])) 1);
  assert_norm (Prims.op_Equality #int (SP.count 3 (Seq.seq_of_list [3; 1; 2])) 1);
  assert_norm (Prims.op_Equality #int (SP.count 0 (Seq.seq_of_list [3; 1; 2])) 0);
  assert_norm (Prims.op_Equality #int (SP.count 4 (Seq.seq_of_list [3; 1; 2])) 0)
#pop-options

// Pulse test functions need modest fuel/rlimit for connecting array writes
// to Seq.seq_of_list [3;1;2] when proving completeness_sort3 precondition.
#push-options "--fuel 4 --z3rlimit 15"

```pulse
(* Completeness: y = quicksort(x); assert(y == expected) *)
fn test_quicksort_3 ()
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

  // Read and verify each element (runtime checks that survive extraction)
  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 3));
  let ok = int_eq v0 1 && int_eq v1 2 && int_eq v2 3;

  // cleanup
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  ok
}
```

(* Completeness: quicksort_with_complexity exposes O(n²) bound via ghost counter *)
```pulse
fn test_quicksort_with_complexity ()
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
  let ok = int_eq v0 1 && int_eq v1 2 && int_eq v2 3;

  // Cleanup
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  ok
}
```

(* Completeness: quicksort_bounded preserves between_bounds in postcondition *)
```pulse
fn test_quicksort_bounded ()
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

  // Convert back so we can read elements
  A.pts_to_range_elim arr 1.0R s;

  // Read and verify each element (runtime checks that survive extraction)
  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 3));
  let ok = int_eq v0 1 && int_eq v1 2 && int_eq v2 3;

  // cleanup
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  ok
}
```

#pop-options
