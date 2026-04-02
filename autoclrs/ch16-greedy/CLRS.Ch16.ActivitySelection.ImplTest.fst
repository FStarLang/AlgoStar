(*
   Activity Selection — Spec Validation Test

   Validates the Impl.fsti API for CLRS §16.1 GREEDY-ACTIVITY-SELECTOR
   by calling the algorithm on a small concrete instance and proving
   that the postcondition is precise enough to determine the output.

   Test instance:
     3 activities, sorted by finish time:
       Activity 0: start=1, finish=4
       Activity 1: start=3, finish=5
       Activity 2: start=5, finish=7
     Expected: count=2, selected = {0, 2}

   Attribution: Pattern inspired by
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

   NO admits. NO assumes.
*)
module CLRS.Ch16.ActivitySelection.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch16.ActivitySelection.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference
module L = CLRS.Ch16.ActivitySelection.Lemmas
module S = CLRS.Ch16.ActivitySelection.Spec
open CLRS.Ch16.ActivitySelection.Complexity

(* ---------- Pure helpers for the concrete instance ---------- *)

(* The concrete start times [1; 3; 5] and finish times [4; 5; 7] *)
noextract
let start3 : Seq.seq int = Seq.seq_of_list [1; 3; 5]
noextract
let finish3 : Seq.seq int = Seq.seq_of_list [4; 5; 7]

(* finish_sorted for [4; 5; 7] *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let finish3_sorted ()
  : Lemma (L.finish_sorted finish3)
  = assert_norm (Seq.length finish3 == 3);
    assert_norm (Seq.index finish3 0 == 4);
    assert_norm (Seq.index finish3 1 == 5);
    assert_norm (Seq.index finish3 2 == 7)
#pop-options

(* All activities valid: start[i] < finish[i] *)
let activities3_valid ()
  : Lemma (forall (i:nat). i < Seq.length start3 ==> L.valid_activity start3 finish3 i)
  = assert_norm (Seq.length start3 == 3);
    assert_norm (Seq.length finish3 == 3);
    assert_norm (Seq.index start3 0 == 1);
    assert_norm (Seq.index finish3 0 == 4);
    assert_norm (Seq.index start3 1 == 3);
    assert_norm (Seq.index finish3 1 == 5);
    assert_norm (Seq.index start3 2 == 5);
    assert_norm (Seq.index finish3 2 == 7)

(* {0, 2} is a mutually compatible set of size 2 *)
let compatible_0_2 ()
  : Lemma (S.mutually_compatible start3 finish3 [0; 2] /\
           S.list_sorted_indices [0; 2] 3 /\
           FStar.List.Tot.length [0; 2] == 2)
  = assert_norm (Seq.index finish3 0 == 4);
    assert_norm (Seq.index start3 2 == 5);
    assert_norm (S.compatible start3 finish3 0 2)

(* No compatible set of size 3 exists: all 3 activities can't be mutually compatible
   since activities 0 and 1 overlap (finish[0]=4 > start[1]=3) *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 15"
let no_compatible_3 (sel: list nat)
  : Lemma
    (requires S.mutually_compatible start3 finish3 sel /\
             S.list_sorted_indices sel 3 /\
             FStar.List.Tot.length sel == 3)
    (ensures False)
  = // sel must be [0; 1; 2] since it's sorted with indices < 3 and has length 3
    match sel with
    | [a; b; c] ->
      assert (a < b /\ b < c /\ c < 3);
      assert (a == 0 /\ b == 1 /\ c == 2);
      // Activities 0 and 1: finish[0]=4, start[1]=3
      // For compatibility we need finish[0] <= start[1] or finish[1] <= start[0]
      assert_norm (Seq.index finish3 0 == 4);
      assert_norm (Seq.index start3 1 == 3);
      assert_norm (Seq.index finish3 1 == 5);
      assert_norm (Seq.index start3 0 == 1);
      // finish[0]=4 > start[1]=3 and finish[1]=5 > start[0]=1
      // So not compatible
      assert (S.compatible start3 finish3 0 1);
      ()
#pop-options

(* max_compatible_count for this instance is 2 *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let max_compatible_is_2 ()
  : Lemma (S.max_compatible_count start3 finish3 3 == 2)
  = reveal_opaque (`%S.max_compatible_count) (S.max_compatible_count start3 finish3 3);
    // Show find_max_compatible start3 finish3 3 3 == 2
    // Step k=3: is there a compatible set of size 3?
    // no_compatible_3 shows any such set leads to False
    // So find_max_compatible 3 recurses to find_max_compatible 2
    // Step k=2: is there a compatible set of size 2?
    // compatible_0_2 shows [0; 2] is such a set
    // So find_max_compatible 2 returns 2
    compatible_0_2 ()
#pop-options

(* The postcondition entails count == 2 *)
let post_implies_count_2 (count: SZ.t) (sout: Seq.seq SZ.t) (cf c0: nat)
  : Lemma
    (requires activity_selection_post count 3sz sout cf c0 start3 finish3)
    (ensures SZ.v count == 2)
  = max_compatible_is_2 ()

(* The postcondition output indices form a 2-element selection.
   For this instance with 3 activities sorted by finish time:
     Activity 0: (1,4), Activity 1: (3,5), Activity 2: (5,7)
   The greedy algorithm selects 0 first, then the earliest compatible,
   which is activity 2 (start[2]=5 >= finish[0]=4).
   
   From the postcondition:
   - sel has length count=2
   - sel[0] = 0 (always selects first)
   - strictly_increasing: sel[0] < sel[1]
   - pairwise_compatible: finish[sel[0]] <= start[sel[1]]
   - earliest_compatible: everything between sel[0] and sel[1] is incompatible
   
   Activity 1 is between sel[0]=0 and sel[1], and it IS incompatible
   (start[1]=3 < finish[0]=4), so sel[1] can be 2.
   
   We prove sel[1] must be 2: it can't be 1 (incompatible with 0) and
   earliest_compatible ensures no gaps are skipped without good reason. *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let post_implies_selection_is_0_2
  (count: SZ.t) (sout: Seq.seq SZ.t) (cf c0: nat)
  : Lemma
    (requires activity_selection_post count 3sz sout cf c0 start3 finish3)
    (ensures SZ.v count == 2 /\
             SZ.v (Seq.index sout 0) == 0 /\
             SZ.v (Seq.index sout 1) == 2)
  = max_compatible_is_2 ();
    // count == 2 from optimality
    assert (SZ.v count == 2);
    // From postcondition with n > 0:
    // There exists sel with:
    //   sel[0] == 0, length sel == 2
    //   strictly_increasing: sel[0] < sel[1]  =>  0 < sel[1]
    //   all_valid_indices: sel[1] < 3
    //   pairwise_compatible: finish[sel[0]] <= start[sel[1]]
    //     i.e. finish[0] <= start[sel[1]]  i.e. 4 <= start[sel[1]]
    //   earliest_compatible: for all z with sel[0] < z < sel[1]:
    //     start[z] < finish[sel[0]] = 4
    // sel[1] in {1, 2}.
    // If sel[1] = 1: need finish[0] <= start[1] i.e. 4 <= 3. False.
    // So sel[1] = 2.
    // out_matches_sel: out[0] == sel[0] == 0, out[1] == sel[1] == 2
    assert_norm (Seq.index start3 1 == 3);
    assert_norm (Seq.index finish3 0 == 4);
    assert_norm (Seq.index start3 2 == 5)
#pop-options

(* Helper to build the sequence for start_times after array writes *)
let seq_after_writes_start ()
  : Lemma (let s0 = Seq.create 3 0 in
           let s1 = Seq.upd s0 0 1 in
           let s2 = Seq.upd s1 1 3 in
           let s3 = Seq.upd s2 2 5 in
           s3 `Seq.equal` start3)
  = assert_norm (start3 `Seq.equal` Seq.seq_of_list [1; 3; 5])

let seq_after_writes_finish ()
  : Lemma (let s0 = Seq.create 3 0 in
           let s1 = Seq.upd s0 0 4 in
           let s2 = Seq.upd s1 1 5 in
           let s3 = Seq.upd s2 2 7 in
           s3 `Seq.equal` finish3)
  = assert_norm (finish3 `Seq.equal` Seq.seq_of_list [4; 5; 7])


(* SZ.t equality check — computational, survives extraction to C *)
inline_for_extraction
let sz_eq (a b: SZ.t) : (r:bool{r <==> SZ.v a = SZ.v b}) =
  let open FStar.SizeT in not (a <^ b || b <^ a)

(* ==================== Main Test ==================== *)

#push-options "--z3rlimit 20 --fuel 4 --ifuel 2"
```pulse
fn test_activity_selection_3 ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // --- Allocate start_times = [1; 3; 5] ---
  let sv = V.alloc 0 3sz;
  V.to_array_pts_to sv;
  let start_arr = V.vec_to_array sv;
  rewrite (A.pts_to (V.vec_to_array sv) (Seq.create 3 0))
       as (A.pts_to start_arr (Seq.create 3 0));
  start_arr.(0sz) <- 1;
  start_arr.(1sz) <- 3;
  start_arr.(2sz) <- 5;
  
  // --- Allocate finish_times = [4; 5; 7] ---
  let fv = V.alloc 0 3sz;
  V.to_array_pts_to fv;
  let finish_arr = V.vec_to_array fv;
  rewrite (A.pts_to (V.vec_to_array fv) (Seq.create 3 0))
       as (A.pts_to finish_arr (Seq.create 3 0));
  finish_arr.(0sz) <- 4;
  finish_arr.(1sz) <- 5;
  finish_arr.(2sz) <- 7;
  
  // --- Allocate output array ---
  let ov = V.alloc 0sz 3sz;
  V.to_array_pts_to ov;
  let out_arr = V.vec_to_array ov;
  rewrite (A.pts_to (V.vec_to_array ov) (Seq.create 3 0sz))
       as (A.pts_to out_arr (Seq.create 3 0sz));

  // --- Ghost counter ---
  let ctr = GR.alloc #nat 0;

  // --- Bind ghost sequences ---
  with ss. assert (A.pts_to start_arr ss);
  with sf. assert (A.pts_to finish_arr sf);
  with sout0. assert (A.pts_to out_arr sout0);

  // --- Prove precondition ---
  seq_after_writes_start ();
  assert (pure (ss `Seq.equal` start3));
  seq_after_writes_finish ();
  assert (pure (sf `Seq.equal` finish3));
  finish3_sorted ();
  activities3_valid ();
  
  // --- Call activity_selection ---
  let count = activity_selection start_arr finish_arr out_arr 3sz ctr;

  // --- Read postcondition ---
  with sout (cf: nat). assert (
    A.pts_to out_arr sout **
    GR.pts_to ctr cf **
    pure (activity_selection_post count 3sz sout cf 0 ss sf)
  );

  // --- Prove the output is precisely [0; 2] ---
  post_implies_selection_is_0_2 count sout cf 0;
  assert (pure (SZ.v count == 2));

  // --- Read and verify output values ---
  let v0 = out_arr.(0sz);
  let v1 = out_arr.(1sz);
  assert (pure (SZ.v v0 == 0));
  assert (pure (SZ.v v1 == 2));
  
  // --- Verify complexity: exactly n-1 = 2 comparisons ---
  assert (pure (cf >= 0 /\ cf - 0 == 3 - 1));
  assert (pure (cf == 2));

  // --- Runtime check (survives extraction to C) ---
  let pass = sz_eq v0 0sz && sz_eq v1 2sz && sz_eq count 2sz;

  // --- Cleanup ---
  with sout'. assert (A.pts_to out_arr sout');
  rewrite (A.pts_to out_arr sout') as (A.pts_to (V.vec_to_array ov) sout');
  V.to_vec_pts_to ov;
  V.free ov;
  
  with sf'. assert (A.pts_to finish_arr sf');
  rewrite (A.pts_to finish_arr sf') as (A.pts_to (V.vec_to_array fv) sf');
  V.to_vec_pts_to fv;
  V.free fv;
  
  with ss'. assert (A.pts_to start_arr ss');
  rewrite (A.pts_to start_arr ss') as (A.pts_to (V.vec_to_array sv) ss');
  V.to_vec_pts_to sv;
  V.free sv;

  GR.free ctr;
  pass
}
```
#pop-options
