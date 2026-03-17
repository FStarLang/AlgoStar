(*
   CLRS Chapter 6: Heapsort — Specification Validation Test

   Adapted from Test.Quicksort.fst in the intent-formalization repository:
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   Tests the heapsort Impl.fsti API by:
   1. Sorting a small concrete array [3; 1; 2]
   2. Proving the precondition is satisfiable
   3. Proving the postcondition (sorted_upto + permutation) is precise enough
      to determine the output is exactly [1; 2; 3]

   NO admits. NO assumes.
*)

module CLRS.Ch06.Heap.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch06.Heap.Impl
open CLRS.Ch06.Heap.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"

(* Pure helper: sorted + permutation of [3;1;2] uniquely determines [1;2;3].
   Uses SP.count to prove that each element appears exactly once, then
   the sorted constraint pins each position. *)
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

(* Completeness lemma: bridges from heapsort's postcondition predicates
   (sorted_upto, permutation) to the uniqueness proof.

   Unlike the quicksort test which needs a BoundedIntegers-to-Prims bridge,
   sorted_upto already uses standard Prims comparison operators, so the
   connection to std_sort3 is direct.

   The s0 parameter carries the concrete input sequence; we establish
   Seq.equal s0 (Seq.seq_of_list [3;1;2]) so Z3 can use the count facts. *)
let completeness_sort3 (s0 s: Seq.seq int)
  : Lemma
    (requires Seq.length s0 == 3 /\
              Seq.index s0 0 == 3 /\
              Seq.index s0 1 == 1 /\
              Seq.index s0 2 == 2 /\
              sorted_upto s 3 /\
              SP.permutation int s0 s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= let l = Seq.seq_of_list [3; 1; 2] in
  assert_norm (Seq.length l == 3);
  assert_norm (Seq.index l 0 == 3);
  assert_norm (Seq.index l 1 == 1);
  assert_norm (Seq.index l 2 == 2);
  assert (Seq.equal s0 l);
  std_sort3 s

```pulse
(* Completeness: y = heapsort([3,1,2]); assert(y == [1,2,3]) *)
fn test_heapsort_3 ()
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

  // Allocate ghost counter
  let ctr = GR.alloc #nat 0;

  // y = heapsort(x)
  heapsort arr 3sz ctr;

  // assert(y == expected)
  with s. assert (A.pts_to arr s);
  // Reveal opaque CLRS.Ch06.Heap.Spec.permutation to get SP.permutation
  reveal_opaque (`%permutation) (permutation s0 s);
  // Now Z3 sees: SP.permutation int s0 s, and knows s0 == [3;1;2] from array writes
  completeness_sort3 s0 s;

  // Read and verify each element
  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 3));

  // Cleanup
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
  ()
}
```

#pop-options
