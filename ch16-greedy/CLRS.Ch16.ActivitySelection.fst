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
   
   5. Optimality: count == max_compatible_count (maximum cardinality
      of any pairwise-compatible selection). No valid selection can
      contain more activities.
   
   6. Output: the first `count` entries of the output array contain
      the selected activity indices, matching the ghost sequence.
   
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
module S = CLRS.Ch16.ActivitySelection.Spec

// ========== Definitions ==========

// The first `count` entries of out_seq match sel (as SZ.t values)
let out_matches_sel (out_seq: Seq.seq SZ.t) (sel: Seq.seq nat) (count: nat) (n: nat) : prop =
  count <= Seq.length out_seq /\
  Seq.length sel == count /\
  (forall (j: nat). j < count ==> SZ.v (Seq.index out_seq j) == Seq.index sel j /\
                                    Seq.index sel j < n)

// ========== Activity Selection Algorithm ==========

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
//SNIPPET_START: activity_selection_sig
fn activity_selection 
  (#p: perm)
  (start_times finish_times: A.array int) 
  (out: A.array SZ.t)
  (n: SZ.t)
  (#ss #sf: Ghost.erased (Seq.seq int))
  (#sout0: Ghost.erased (Seq.seq SZ.t))
  requires 
    A.pts_to start_times #p ss ** A.pts_to finish_times #p sf **
    A.pts_to out sout0 **
    pure (
      SZ.v n == Seq.length ss /\ 
      SZ.v n == Seq.length sf /\
      SZ.v n == A.length start_times /\ 
      SZ.v n == A.length finish_times /\
      SZ.v n == A.length out /\
      SZ.v n == Seq.length sout0 /\
      SZ.v n > 0 /\
      L.finish_sorted sf /\
      (forall (i:nat). i < Seq.length ss ==> L.valid_activity ss sf i)
    )
  returns count: SZ.t
  ensures exists* sout.
    A.pts_to start_times #p ss ** 
    A.pts_to finish_times #p sf **
    A.pts_to out sout **
    pure (
      SZ.v count >= 1 /\ 
      SZ.v count <= SZ.v n /\
      Seq.length sout == SZ.v n /\
      // The first count entries of out are the selected activity indices
      (exists (sel: Seq.seq nat).
        Seq.length sel == SZ.v count /\
        out_matches_sel sout sel (SZ.v count) (SZ.v n) /\
        L.all_valid_indices sel (SZ.v n) /\
        L.strictly_increasing sel /\
        L.pairwise_compatible sel ss sf /\
        Seq.index sel 0 == 0 /\
        L.earliest_compatible sel ss sf (SZ.v n) (SZ.v n) /\
        // Optimality: the selection has maximum cardinality
        SZ.v count == S.max_compatible_count ss sf (SZ.v n))
    )
//SNIPPET_END: activity_selection_sig
{
  // First activity (earliest finish) is always selected
  out.(0sz) <- 0sz;
  let mut count: SZ.t = 1sz;
  let first_finish = finish_times.(0sz);
  let mut last_finish: int = first_finish;
  
  // Ghost selection sequence (mirrors the concrete out array prefix)
  L.lemma_initial_selection ss sf (SZ.v n);
  let sel_ref = GR.alloc #(Seq.seq nat) (Seq.create 1 0);
  
  // Scan through remaining activities
  let mut i: SZ.t = 1sz;
  
  while (!i <^ n)
  invariant exists* vi vcount vlast_finish vsel sout_cur.
    R.pts_to i vi **
    R.pts_to count vcount **
    R.pts_to last_finish vlast_finish **
    GR.pts_to sel_ref vsel **
    A.pts_to out sout_cur **
    pure (
      SZ.v vi > 0 /\
      SZ.v vi <= SZ.v n /\
      SZ.v vcount >= 1 /\
      SZ.v vcount <= SZ.v vi /\
      Seq.length vsel == SZ.v vcount /\
      Seq.length sout_cur == SZ.v n /\
      out_matches_sel sout_cur vsel (SZ.v vcount) (SZ.v n) /\
      L.greedy_selection_inv vsel ss sf (SZ.v n) (SZ.v vi) vlast_finish
    )
  {
    let vi = !i;
    let curr_start = start_times.(vi);
    let curr_finish = finish_times.(vi);
    let vlast_finish = !last_finish;
    let vcount = !count;
    
    with vsel. assert (GR.pts_to sel_ref vsel);
    with sout_cur. assert (A.pts_to out sout_cur);
    assert pure (L.finish_sorted sf);
    assert pure (L.greedy_selection_inv vsel ss sf (SZ.v n) (SZ.v vi) vlast_finish);
    assert pure (vlast_finish <= curr_finish);
    
    // Compute both possible next selections
    let selected = (curr_start >= vlast_finish);
    
    // Call combined step lemma
    L.lemma_step vsel ss sf (SZ.v n) (SZ.v vi) vlast_finish selected;
    
    if selected {
      // Write selected index to out array
      out.(vcount) <- vi;
      count := vcount + 1sz;
      last_finish := curr_finish;
      let new_sel : Ghost.erased (Seq.seq nat) = 
        Ghost.hide (Seq.snoc (Ghost.reveal vsel) (SZ.v vi));
      GR.op_Colon_Equals sel_ref new_sel;
      i := vi + 1sz;
    } else {
      i := vi + 1sz;
    };
  };
  
  with vsel_f. assert (GR.pts_to sel_ref vsel_f);
  with sout_f. assert (A.pts_to out sout_f);
  // Call optimality theorem: the greedy selection achieves maximum cardinality
  S.corollary_greedy_count_is_maximum_l ss sf (SZ.v n) (Ghost.reveal vsel_f);
  GR.free sel_ref;
  
  !count
}
#pop-options
