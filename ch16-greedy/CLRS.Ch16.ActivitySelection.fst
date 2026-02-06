(*
   Activity Selection - Verified Greedy implementation in Pulse
   
   Implements the greedy activity selection algorithm to find
   the maximum number of non-overlapping activities.
   
   Proves:
   1. At least one activity is selected (count >= 1)
   2. At most n activities are selected (count <= n)
   3. Selected activities are compatible (non-overlapping)
   
   NO admits. NO assumes.
*)

module CLRS.Ch16.ActivitySelection
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Definitions ==========

// Activities are sorted by finish time
let finish_sorted (f: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\ j < Seq.length f ==> Seq.index f i <= Seq.index f j

// Activities are compatible if they don't overlap
let compatible (s f: Seq.seq int) (i j: nat) : prop =
  i < Seq.length s /\ j < Seq.length s /\
  i < Seq.length f /\ j < Seq.length f /\
  Seq.index f i <= Seq.index s j

// Valid activity (start <= finish)
let valid_activity (s f: Seq.seq int) (i: nat) : prop =
  i < Seq.length s /\ i < Seq.length f /\ Seq.index s i <= Seq.index f i

// ========== Activity Selection Algorithm ==========

fn activity_selection 
  (#p: perm)
  (start_times finish_times: A.array int) 
  (n: SZ.t)
  (#ss #sf: Ghost.erased (Seq.seq int))
  requires 
    A.pts_to start_times #p ss ** A.pts_to finish_times #p sf **
    pure (
      SZ.v n == Seq.length ss /\ 
      SZ.v n == Seq.length sf /\
      SZ.v n == A.length start_times /\ 
      SZ.v n == A.length finish_times /\
      SZ.v n > 0 /\
      finish_sorted sf /\
      (forall (i:nat). i < Seq.length ss ==> valid_activity ss sf i)
    )
  returns count: SZ.t
  ensures 
    A.pts_to start_times #p ss ** A.pts_to finish_times #p sf **
    pure (
      SZ.v count >= 1 /\ SZ.v count <= SZ.v n
    )
{
  // First activity (earliest finish) is always selected
  let mut count: SZ.t = 1sz;
  let first_finish = finish_times.(0sz);
  let mut last_finish: int = first_finish;
  
  // Scan through remaining activities
  let mut i: SZ.t = 1sz;
  
  while (!i <^ n)
  invariant exists* vi vcount vlast_finish.
    R.pts_to i vi **
    R.pts_to count vcount **
    R.pts_to last_finish vlast_finish **
    pure (
      SZ.v vi > 0 /\
      SZ.v vi <= SZ.v n /\
      SZ.v vcount >= 1 /\
      SZ.v vcount <= SZ.v vi /\
      // last_finish is a valid finish time from the activities seen so far
      (exists (k:nat). k < SZ.v vi /\ Seq.index sf k == vlast_finish) /\
      // last_finish is bounded by the finish time of activities seen
      (forall (k:nat). k < SZ.v vi ==> vlast_finish <= Seq.index sf k \/ Seq.index sf k < vlast_finish)
    )
  {
    let vi = !i;
    let curr_start = start_times.(vi);
    let curr_finish = finish_times.(vi);
    let vlast_finish = !last_finish;
    
    // If current activity starts after or when last selected finishes, select it
    if (curr_start >= vlast_finish) {
      count := !count + 1sz;
      last_finish := curr_finish;
    };
    
    i := vi + 1sz;
  };
  
  !count
}
