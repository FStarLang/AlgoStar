(*
   Spec validation test for Naive String Matching (CLRS §32.1)

   Source: Test methodology from https://arxiv.org/abs/2406.09757
   Reference tests: https://github.com/microsoft/intent-formalization/
     tree/main/eval-autoclrs-specs/intree-tests

   Tests:
   - Precondition satisfiability: constructs a valid call with
     text=[1,2,1,2,1], pattern=[1,2,1]
   - Postcondition precision: proves the result is uniquely determined (count=2)
   - Match position verification: proves matches at positions 0 and 2 only

   NO admits. NO assumes.
*)
module CLRS.Ch32.NaiveStringMatch.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT

open CLRS.Ch32.NaiveStringMatch
open CLRS.Ch32.NaiveStringMatch.Spec
open CLRS.Ch32.NaiveStringMatch.Complexity

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* SZ.fits for our concrete sizes:
   n=5, m=3: need fits(n-m+2)=fits(4) and fits((n-m+1)*m)=fits(9) *)
let naive_fits () : Lemma (SZ.fits 4 /\ SZ.fits 9) =
  assert_norm (pow2 16 == 65536);
  SZ.fits_at_least_16 4;
  SZ.fits_at_least_16 9

(* Postcondition precision lemma:
   For any sequences with content [1,2,1,2,1] and [1,2,1],
   count_matches_up_to evaluates to 2.

   Pattern matches at positions 0 and 2:
   - Position 0: text[0..2] = [1,2,1] = pattern ✓
   - Position 1: text[1..3] = [2,1,2] ≠ pattern ✗ (text[1]=2 ≠ pat[0]=1)
   - Position 2: text[2..4] = [1,2,1] = pattern ✓
   Total: 2 matches *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 100"
let count_matches_is_2 (text pat: Seq.seq int)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 0 == 1 /\ Seq.index text 1 == 2 /\ Seq.index text 2 == 1 /\
              Seq.index text 3 == 2 /\ Seq.index text 4 == 1 /\
              Seq.index pat 0 == 1 /\ Seq.index pat 1 == 2 /\ Seq.index pat 2 == 1)
    (ensures count_matches_up_to text pat 3 == 2)
  = ()
#pop-options

(* Match position verification: each position individually *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 50"
let match_at_0 (text pat: Seq.seq int)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 0 == 1 /\ Seq.index text 1 == 2 /\ Seq.index text 2 == 1 /\
              Seq.index pat 0 == 1 /\ Seq.index pat 1 == 2 /\ Seq.index pat 2 == 1)
    (ensures matches_at text pat 0)
  = ()

let no_match_at_1 (text pat: Seq.seq int)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 1 == 2 /\
              Seq.index pat 0 == 1)
    (ensures ~(matches_at text pat 1))
  = ()

let match_at_2 (text pat: Seq.seq int)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 2 == 1 /\ Seq.index text 3 == 2 /\ Seq.index text 4 == 1 /\
              Seq.index pat 0 == 1 /\ Seq.index pat 1 == 2 /\ Seq.index pat 2 == 1)
    (ensures matches_at text pat 2)
  = ()
#pop-options

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"

```pulse
(* Test: Precondition satisfiability + Postcondition precision *)
fn test_naive_string_match ()
  requires emp
  returns _: unit
  ensures emp
{
  // Text: [1, 2, 1, 2, 1] (length 5)
  let tv = V.alloc #int 0 5sz;
  V.to_array_pts_to tv;
  let text = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 5 0))
       as (A.pts_to text (Seq.create 5 0));
  text.(0sz) <- 1;
  text.(1sz) <- 2;
  text.(2sz) <- 1;
  text.(3sz) <- 2;
  text.(4sz) <- 1;

  // Pattern: [1, 2, 1] (length 3)
  let pv = V.alloc #int 0 3sz;
  V.to_array_pts_to pv;
  let pat = V.vec_to_array pv;
  rewrite (A.pts_to (V.vec_to_array pv) (Seq.create 3 0))
       as (A.pts_to pat (Seq.create 3 0));
  pat.(0sz) <- 1;
  pat.(1sz) <- 2;
  pat.(2sz) <- 1;

  // Ghost counter
  let ctr = GR.alloc #nat 0;

  // Provide SZ.fits facts
  naive_fits ();

  // Call naive_string_match
  // Precondition: m > 0, m <= n, fits constraints — all satisfied
  let count = naive_string_match text pat 5sz 3sz ctr;

  // Bind ghost sequences from postcondition
  with s_text. assert (A.pts_to text s_text);
  with s_pat. assert (A.pts_to pat s_pat);

  // Prove postcondition precision: count must be 2
  count_matches_is_2 s_text s_pat;
  assert (pure (SZ.v count == 2));

  // Verify individual match positions
  match_at_0 s_text s_pat;
  match_at_2 s_text s_pat;
  no_match_at_1 s_text s_pat;

  // Cleanup
  GR.free ctr;
  rewrite (A.pts_to text s_text) as (A.pts_to (V.vec_to_array tv) s_text);
  V.to_vec_pts_to tv;
  V.free tv;
  rewrite (A.pts_to pat s_pat) as (A.pts_to (V.vec_to_array pv) s_pat);
  V.to_vec_pts_to pv;
  V.free pv;

  ()
}
```

#pop-options
