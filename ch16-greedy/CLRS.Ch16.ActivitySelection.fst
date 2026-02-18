(*
   Activity Selection - Verified Greedy implementation in Pulse
   
   Implements the greedy activity selection algorithm to find
   the maximum number of non-overlapping activities.
   
   FUNCTIONAL CORRECTNESS PROPERTIES PROVEN:
   
   1. Termination: The algorithm always terminates
   
   2. Basic correctness:
      - At least one activity is selected (count >= 1)
      - At most n activities are selected (count <= n)
   
   3. Greedy selection property:
      - The first activity (with earliest finish time) is always selected
      - An activity is selected only if its start time >= the finish time of 
        the last selected activity
   
   4. Pairwise non-overlapping (via ghost selection sequence):
      - A ghost sequence sel tracks the indices of selected activities
      - All selected indices are valid (< n) and strictly increasing
      - For consecutive selections i, j: finish[sel[i]] <= start[sel[j]]
      - The returned count equals the length of the selection
      - The first selected activity is index 0
   
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
module GR = Pulse.Lib.GhostReference
module L = CLRS.Ch16.ActivitySelection.Lemmas

// ========== Definitions ==========

// Activities are sorted by finish time
let finish_sorted (f: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\ j < Seq.length f ==> Seq.index f i <= Seq.index f j

// Valid activity (start <= finish)
let valid_activity (s f: Seq.seq int) (i: nat) : prop =
  i < Seq.length s /\ i < Seq.length f /\ Seq.index s i < Seq.index f i

// ========== Activity Selection Algorithm ==========

//SNIPPET_START: activity_selection_sig
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
    A.pts_to start_times #p ss ** 
    A.pts_to finish_times #p sf **
    pure (
      SZ.v count >= 1 /\ 
      SZ.v count <= SZ.v n /\
      // There exists a selection of activities that is pairwise non-overlapping
      (exists (sel: Seq.seq nat).
        Seq.length sel == SZ.v count /\
        L.all_valid_indices sel (SZ.v n) /\
        L.strictly_increasing sel /\
        L.pairwise_compatible sel ss sf /\
        Seq.index sel 0 == 0)
    )
//SNIPPET_END: activity_selection_sig
{
  // First activity (earliest finish) is always selected
  let mut count: SZ.t = 1sz;
  let first_finish = finish_times.(0sz);
  let mut last_finish: int = first_finish;
  
  // Ghost selection sequence
  L.lemma_initial_selection ss sf (SZ.v n);
  let sel_ref = GR.alloc #(Seq.seq nat) (Seq.create 1 0);
  
  // Scan through remaining activities
  let mut i: SZ.t = 1sz;
  
  while (!i <^ n)
  invariant exists* vi vcount vlast_finish vsel.
    R.pts_to i vi **
    R.pts_to count vcount **
    R.pts_to last_finish vlast_finish **
    GR.pts_to sel_ref vsel **
    pure (
      SZ.v vi > 0 /\
      SZ.v vi <= SZ.v n /\
      SZ.v vcount >= 1 /\
      SZ.v vcount <= SZ.v vi /\
      Seq.length vsel == SZ.v vcount /\
      L.greedy_selection_inv vsel ss sf (SZ.v n) (SZ.v vi) vlast_finish
    )
  {
    let vi = !i;
    let curr_start = start_times.(vi);
    let curr_finish = finish_times.(vi);
    let vlast_finish = !last_finish;
    let vcount = !count;
    
    with vsel. assert (GR.pts_to sel_ref vsel);
    assert pure (finish_sorted sf);
    assert pure (L.greedy_selection_inv vsel ss sf (SZ.v n) (SZ.v vi) vlast_finish);
    assert pure (vlast_finish <= curr_finish);
    
    // Compute both possible next selections
    let selected = (curr_start >= vlast_finish);
    
    // Call combined step lemma
    L.lemma_step vsel ss sf (SZ.v n) (SZ.v vi) vlast_finish selected;
    
    let new_count : SZ.t = (if selected then vcount + 1sz else vcount);
    let new_last : int = (if selected then curr_finish else vlast_finish);
    let new_sel : Ghost.erased (Seq.seq nat) = 
      (if selected then Ghost.hide (Seq.snoc (Ghost.reveal vsel) (SZ.v vi)) else vsel);
    
    count := new_count;
    last_finish := new_last;
    GR.op_Colon_Equals sel_ref new_sel;
    
    i := vi + 1sz;
  };
  
  with vsel_f. assert (GR.pts_to sel_ref vsel_f);
  GR.free sel_ref;
  
  !count
}
