(*
   CLRS Chapter 6: Heapsort — Specification Validation Tests

   Adapted from Test.Quicksort.fst in the intent-formalization repository:
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   Tests the heapsort Impl.fsti API by:
   1. Sorting a small concrete array [3; 1; 2] — postcondition completeness
   2. Building a max-heap from [3; 1; 2] — root = max completeness
   3. Sorting with n=0 — identity behavior
   4. Prefix sorting [7; 5; 3] with n=2 — element preservation
   5. Sorting with duplicates [2; 1; 2] — duplicate handling

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
open CLRS.Ch06.Heap.Lemmas

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module CB = CLRS.Ch06.Heap.CostBound

// ========== Test 1: heapsort completeness on [3;1;2] ==========

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

// ========== Test 2: build_max_heap completeness — root = max ==========

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"

(* Pure helper: max-heap + permutation of [3;1;2] determines root == 3.
   root_ge_element gives s[0] >= s[i] for all i < 3, and count reasoning
   shows the only element >= both others in {1,2,3} is 3. *)
let heap_root3 (s0 s: Seq.seq int)
  : Lemma
    (requires Seq.length s0 == 3 /\
              Seq.index s0 0 == 3 /\
              Seq.index s0 1 == 1 /\
              Seq.index s0 2 == 2 /\
              Seq.length s == Seq.length s0 /\
              is_max_heap s 3 /\
              SP.permutation int s0 s)
    (ensures Seq.index s 0 == 3)
= let l = Seq.seq_of_list [3; 1; 2] in
  assert_norm (Seq.length l == 3);
  assert_norm (Seq.index l 0 == 3);
  assert_norm (Seq.index l 1 == 1);
  assert_norm (Seq.index l 2 == 2);
  assert (Seq.equal s0 l);
  SP.perm_len l s;
  assert_norm (SP.count 3 l == 1);
  assert_norm (SP.count 1 l == 1);
  assert_norm (SP.count 2 l == 1);
  assert_norm (SP.count 0 l == 0);
  assert_norm (SP.count 4 l == 0);
  root_ge_element s 3 1;
  root_ge_element s 3 2

```pulse
(* build_max_heap completeness: build_max_heap([3,1,2]); assert(root == 3) *)
fn test_build_max_heap_3 ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  with s0. assert (A.pts_to arr s0);
  let ctr = GR.alloc #nat 0;

  build_max_heap arr 3sz ctr;

  with s. assert (A.pts_to arr s);
  reveal_opaque (`%permutation) (permutation s0 s);
  heap_root3 s0 s;

  // Root is the maximum
  let v0 = arr.(0sz);
  assert (pure (v0 == 3));

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

// ========== Test 3: heapsort n=0 — identity (array unchanged) ==========

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"

```pulse
(* Identity: heapsort with n=0 leaves the array unchanged.
   Exercises the forall k. 0 <= k < length s ==> s[k] == s0[k] clause. *)
fn test_heapsort_0 ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 5;
  arr.(1sz) <- 3;
  arr.(2sz) <- 7;

  with s0. assert (A.pts_to arr s0);
  let ctr = GR.alloc #nat 0;

  heapsort arr 0sz ctr;

  with s. assert (A.pts_to arr s);
  // n=0: forall k. 0 <= k < 3 ==> s[k] == s0[k], so array unchanged
  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 5));
  assert (pure (v1 == 3));
  assert (pure (v2 == 7));

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

// ========== Test 4: heapsort prefix sorting (n < array length) ==========

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"

(* Pure helper: sorted_upto 2 + permutation of [7;5;3] with s[2]==3
   determines s[0]==5 /\ s[1]==7.  The preservation clause gives s[2]==3,
   so {s[0],s[1]} = {5,7}, and sorted_upto pins their order. *)
let completeness_prefix2 (s0 s: Seq.seq int)
  : Lemma
    (requires Seq.length s0 == 3 /\
              Seq.index s0 0 == 7 /\
              Seq.index s0 1 == 5 /\
              Seq.index s0 2 == 3 /\
              Seq.length s == 3 /\
              sorted_upto s 2 /\
              SP.permutation int s0 s /\
              Seq.index s 2 == Seq.index s0 2)
    (ensures Seq.index s 0 == 5 /\ Seq.index s 1 == 7 /\ Seq.index s 2 == 3)
= let l = Seq.seq_of_list [7; 5; 3] in
  assert_norm (Seq.length l == 3);
  assert_norm (Seq.index l 0 == 7);
  assert_norm (Seq.index l 1 == 5);
  assert_norm (Seq.index l 2 == 3);
  assert (Seq.equal s0 l);
  SP.perm_len l s;
  assert_norm (SP.count 7 l == 1);
  assert_norm (SP.count 5 l == 1);
  assert_norm (SP.count 3 l == 1);
  assert_norm (SP.count 0 l == 0);
  assert_norm (SP.count 8 l == 0)

```pulse
(* Prefix sort: heapsort([7,5,3], n=2); assert first 2 sorted, third unchanged *)
fn test_heapsort_prefix ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 7;
  arr.(1sz) <- 5;
  arr.(2sz) <- 3;

  with s0. assert (A.pts_to arr s0);
  let ctr = GR.alloc #nat 0;

  heapsort arr 2sz ctr;

  with s. assert (A.pts_to arr s);
  reveal_opaque (`%permutation) (permutation s0 s);
  // s[2] == s0[2] from preservation clause (n=2, k=2)
  completeness_prefix2 s0 s;

  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 5));
  assert (pure (v1 == 7));
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

// ========== Test 5: heapsort with duplicates [2;1;2] ==========

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"

(* Pure helper: sorted + permutation of [2;1;2] determines [1;2;2].
   count(1)=1, count(2)=2 pins the unique sorted output. *)
let completeness_sort_dupes (s0 s: Seq.seq int)
  : Lemma
    (requires Seq.length s0 == 3 /\
              Seq.index s0 0 == 2 /\
              Seq.index s0 1 == 1 /\
              Seq.index s0 2 == 2 /\
              sorted_upto s 3 /\
              SP.permutation int s0 s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 2)
= let l = Seq.seq_of_list [2; 1; 2] in
  assert_norm (Seq.length l == 3);
  assert_norm (Seq.index l 0 == 2);
  assert_norm (Seq.index l 1 == 1);
  assert_norm (Seq.index l 2 == 2);
  assert (Seq.equal s0 l);
  SP.perm_len l s;
  assert_norm (SP.count 1 l == 1);
  assert_norm (SP.count 2 l == 2);
  assert_norm (SP.count 0 l == 0);
  assert_norm (SP.count 3 l == 0)

```pulse
(* Duplicates: heapsort([2,1,2]); assert output == [1,2,2] *)
fn test_heapsort_duplicates ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 2;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  with s0. assert (A.pts_to arr s0);
  let ctr = GR.alloc #nat 0;

  heapsort arr 3sz ctr;

  with s. assert (A.pts_to arr s);
  reveal_opaque (`%permutation) (permutation s0 s);
  completeness_sort_dupes s0 s;

  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 2));

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
