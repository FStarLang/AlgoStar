(*
   Spec validation test for Rabin-Karp String Matching (CLRS §32.2)

   Source: Test methodology from https://arxiv.org/abs/2406.09757
   Reference tests: https://github.com/microsoft/intent-formalization/
     tree/main/eval-autoclrs-specs/intree-tests

   Tests:
   - Precondition satisfiability: constructs a valid call with
     text=[1,2,1,2,1], pattern=[1,2,1], d=10, q=13
   - Postcondition precision: proves the result is uniquely determined (count=2)
   - Match position verification: proves matches at positions 0 and 2 only

   NO admits. NO assumes.
*)
module CLRS.Ch32.RabinKarp.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module RK = CLRS.Ch32.RabinKarp
module RKSpec = CLRS.Ch32.RabinKarp.Spec

open CLRS.Ch32.RabinKarp.Complexity

(* SZ.fits for our concrete sizes:
   n=5, m=3: need fits(n-m+2)=fits(4) and fits(n+1)=fits(6) *)
let rk_fits () : Lemma (SZ.fits 4 /\ SZ.fits 6) =
  assert_norm (pow2 16 == 65536);
  SZ.fits_at_least_16 4;
  SZ.fits_at_least_16 6

(* Postcondition precision lemma:
   For any sequences with content [1,2,1,2,1] and [1,2,1],
   Rabin-Karp's count_matches_up_to evaluates to 2.

   Pattern matches at positions 0 and 2:
   - Position 0: text[0..2] = [1,2,1] = pattern ✓
   - Position 1: text[1..3] = [2,1,2] ≠ pattern ✗
   - Position 2: text[2..4] = [1,2,1] = pattern ✓
   Total: 2 matches *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 100"
let rk_count_matches_is_2 (text pat: Seq.seq nat)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 0 == 1 /\ Seq.index text 1 == 2 /\ Seq.index text 2 == 1 /\
              Seq.index text 3 == 2 /\ Seq.index text 4 == 1 /\
              Seq.index pat 0 == 1 /\ Seq.index pat 1 == 2 /\ Seq.index pat 2 == 1)
    (ensures RK.count_matches_up_to text pat 3 == 2)
  = ()
#pop-options

(* Match position verification: each position individually *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 50"
let rk_match_at_0 (text pat: Seq.seq nat)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 0 == 1 /\ Seq.index text 1 == 2 /\ Seq.index text 2 == 1 /\
              Seq.index pat 0 == 1 /\ Seq.index pat 1 == 2 /\ Seq.index pat 2 == 1)
    (ensures RKSpec.matches_at text pat 0)
  = ()

let rk_no_match_at_1 (text pat: Seq.seq nat)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 1 == 2 /\
              Seq.index pat 0 == 1)
    (ensures ~(RKSpec.matches_at text pat 1))
  = ()

let rk_match_at_2 (text pat: Seq.seq nat)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 2 == 1 /\ Seq.index text 3 == 2 /\ Seq.index text 4 == 1 /\
              Seq.index pat 0 == 1 /\ Seq.index pat 1 == 2 /\ Seq.index pat 2 == 1)
    (ensures RKSpec.matches_at text pat 2)
  = ()
#pop-options

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"

```pulse
(* Test: Precondition satisfiability + Postcondition precision *)
fn test_rabin_karp ()
  requires emp
  returns _: unit
  ensures emp
{
  // Text: [1, 2, 1, 2, 1] (length 5, nat)
  let tv = V.alloc #nat 0 5sz;
  V.to_array_pts_to tv;
  let text = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 5 0))
       as (A.pts_to text (Seq.create 5 0));
  A.op_Array_Assignment text 0sz 1;
  A.op_Array_Assignment text 1sz 2;
  A.op_Array_Assignment text 2sz 1;
  A.op_Array_Assignment text 3sz 2;
  A.op_Array_Assignment text 4sz 1;

  // Pattern: [1, 2, 1] (length 3, nat)
  let pv = V.alloc #nat 0 3sz;
  V.to_array_pts_to pv;
  let pat = V.vec_to_array pv;
  rewrite (A.pts_to (V.vec_to_array pv) (Seq.create 3 0))
       as (A.pts_to pat (Seq.create 3 0));
  A.op_Array_Assignment pat 0sz 1;
  A.op_Array_Assignment pat 1sz 2;
  A.op_Array_Assignment pat 2sz 1;

  // Ghost counter
  let ctr = GR.alloc #nat 0;

  // Provide SZ.fits facts
  rk_fits ();

  // Call rabin_karp: d=10, q=13
  // Precondition: m > 0, m <= n, fits constraints — all satisfied
  let count = RK.rabin_karp text pat 5sz 3sz 10 13 ctr;

  // Bind ghost sequences from postcondition
  with s_text. assert (A.pts_to text s_text);
  with s_pat. assert (A.pts_to pat s_pat);

  // Prove postcondition precision: count must be 2
  rk_count_matches_is_2 s_text s_pat;
  assert (pure (count == 2));

  // Verify individual match positions
  rk_match_at_0 s_text s_pat;
  rk_match_at_2 s_text s_pat;
  rk_no_match_at_1 s_text s_pat;

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
