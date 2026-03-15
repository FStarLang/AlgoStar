(*
   Activity Selection — Implementation Interface

   Public API signature for the verified greedy activity selection
   algorithm (CLRS §16.1, GREEDY-ACTIVITY-SELECTOR).

   Postconditions guarantee:
   - Functional correctness: selected activities are pairwise compatible
   - Optimality: count == max_compatible_count (maximum cardinality)
   - Complexity: exactly n-1 comparisons (O(n) for presorted input)
*)
module CLRS.Ch16.ActivitySelection.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference
module L = CLRS.Ch16.ActivitySelection.Lemmas
module S = CLRS.Ch16.ActivitySelection.Spec

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

let complexity_bounded_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1

let out_matches_sel (out_seq: Seq.seq SZ.t) (sel: Seq.seq nat) (count: nat) (n: nat) : prop =
  count <= Seq.length out_seq /\
  Seq.length sel == count /\
  (forall (j: nat). j < count ==> SZ.v (Seq.index out_seq j) == Seq.index sel j /\
                                    Seq.index sel j < n)

let activity_selection_pre (n: SZ.t) (ss sf: Seq.seq int) (sout0: Seq.seq SZ.t)
  (start_times finish_times: A.array int) (out: A.array SZ.t) : prop =
  SZ.v n == Seq.length ss /\ 
  SZ.v n == Seq.length sf /\
  SZ.v n == A.length start_times /\ 
  SZ.v n == A.length finish_times /\
  SZ.v n == A.length out /\
  SZ.v n == Seq.length sout0 /\
  L.finish_sorted sf /\
  (forall (i:nat). i < Seq.length ss ==> L.valid_activity ss sf i)

let activity_selection_post
  (count: SZ.t) (n: SZ.t) (sout: Seq.seq SZ.t) (cf: nat) (c0: nat) (ss sf: Seq.seq int)
: prop =
  SZ.v count <= SZ.v n /\
  Seq.length sout == SZ.v n /\
  cf >= c0 /\
  SZ.v count == S.max_compatible_count ss sf (SZ.v n) /\
  (SZ.v n == 0 ==> SZ.v count == 0 /\ cf == c0) /\
  (SZ.v n > 0 ==>
    SZ.v count >= 1 /\
    complexity_bounded_linear cf c0 (SZ.v n) /\
    (exists (sel: Seq.seq nat).
      Seq.length sel == SZ.v count /\
      out_matches_sel sout sel (SZ.v count) (SZ.v n) /\
      L.all_valid_indices sel (SZ.v n) /\
      L.strictly_increasing sel /\
      L.pairwise_compatible sel ss sf /\
      Seq.index sel 0 == 0 /\
      L.earliest_compatible sel ss sf (SZ.v n) (SZ.v n)))

//SNIPPET_START: activity_selection_sig
fn activity_selection 
  (#p: perm)
  (start_times finish_times: A.array int) 
  (out: A.array SZ.t)
  (n: SZ.t)
  (#ss #sf: Ghost.erased (Seq.seq int))
  (#sout0: Ghost.erased (Seq.seq SZ.t))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires 
    A.pts_to start_times #p ss ** A.pts_to finish_times #p sf **
    A.pts_to out sout0 **
    GR.pts_to ctr c0 **
    pure (activity_selection_pre n ss sf sout0 start_times finish_times out)
  returns count: SZ.t
  ensures exists* sout (cf: nat).
    A.pts_to start_times #p ss ** 
    A.pts_to finish_times #p sf **
    A.pts_to out sout **
    GR.pts_to ctr cf **
    pure (activity_selection_post count n sout cf (reveal c0) ss sf)
//SNIPPET_END: activity_selection_sig
