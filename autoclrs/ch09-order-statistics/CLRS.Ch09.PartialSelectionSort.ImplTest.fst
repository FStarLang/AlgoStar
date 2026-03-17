(*
   CLRS Chapter 9: Partial Selection Sort — Spec Validation Test

   Tests select on a small concrete array [5, 2, 8] with k=1 (1-indexed),
   expecting result == 2 (the minimum).

   The postcondition of select provides:
   - permutation s0 s_final (opaque)
   - sorted_prefix s_final k
   - prefix_leq_suffix s_final k
   - result == s_final[k-1]

   Since permutation is opaque_to_smt, we reveal it and use a completeness
   lemma with count-based reasoning to prove result == 2.

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

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

(* Completeness lemma: if s_final is a permutation of [5;2;8] and its first
   element is ≤ all others (prefix_leq_suffix with bound=1), then s_final[0] == 2.
   Uses count-based reasoning with Prims operators for Z3 compatibility. *)
let completeness_select_k1 (s: Seq.seq int)
  : Lemma
    (requires
      Seq.length s == 3 /\
      SP.permutation int (Seq.seq_of_list [5; 2; 8]) s /\
      (forall (j:nat). 1 <= j /\ j < 3 ==> Seq.index s 0 <= Seq.index s j))
    (ensures Seq.index s 0 == 2)
= SP.perm_len (Seq.seq_of_list [5; 2; 8]) s;
  assert_norm (SP.count 2 (Seq.seq_of_list [5; 2; 8]) == 1);
  assert_norm (SP.count 5 (Seq.seq_of_list [5; 2; 8]) == 1);
  assert_norm (SP.count 8 (Seq.seq_of_list [5; 2; 8]) == 1);
  assert_norm (SP.count 1 (Seq.seq_of_list [5; 2; 8]) == 0);
  assert_norm (SP.count 3 (Seq.seq_of_list [5; 2; 8]) == 0);
  assert_norm (SP.count 4 (Seq.seq_of_list [5; 2; 8]) == 0);
  assert_norm (SP.count 6 (Seq.seq_of_list [5; 2; 8]) == 0);
  assert_norm (SP.count 7 (Seq.seq_of_list [5; 2; 8]) == 0);
  assert_norm (SP.count 9 (Seq.seq_of_list [5; 2; 8]) == 0);
  assert_norm (SP.count 0 (Seq.seq_of_list [5; 2; 8]) == 0)

```pulse
fn test_select ()
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

  // Bind input ghost state
  with s0. assert (A.pts_to arr s0);

  let ctr = GR.alloc #nat 0;
  let result = select arr 3sz 1sz ctr #(hide 0);

  // Bind output existentials
  with s_final cf. assert (A.pts_to arr s_final ** GR.pts_to ctr cf);

  // Reveal opaque permutation so Z3 sees Seq.Properties.permutation
  reveal_opaque (`%CLRS.Ch09.PartialSelectionSort.Impl.permutation)
    (permutation s0 s_final);

  // Apply completeness lemma: sorted_prefix + permutation => s_final[0] == 2
  completeness_select_k1 s_final;

  // k=1: result == s_final[k-1] == s_final[0] == 2
  assert (pure (result == 2));

  GR.free ctr;
  rewrite (A.pts_to arr s_final) as (A.pts_to (V.vec_to_array v) s_final);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
