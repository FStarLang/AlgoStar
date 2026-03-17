(*
   Spec validation test for KMP String Matching (CLRS §32.4)

   Source: Test methodology from https://arxiv.org/abs/2406.09757
   Reference tests: https://github.com/microsoft/intent-formalization/
     tree/main/eval-autoclrs-specs/intree-tests

   Tests:
   - Precondition satisfiability: constructs a valid call with
     text=[0,1,0,1,0], pattern=[0,1,0]
   - Postcondition precision: proves the result is uniquely determined (count=2)
   - Match position verification: proves matches at positions 0 and 2 only

   NO admits. NO assumes.
*)
module CLRS.Ch32.KMP.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul

open CLRS.Ch32.KMP
open CLRS.Ch32.KMP.PureDefs

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = CLRS.Ch32.KMP.Spec

(* SZ.fits for our concrete sizes:
   n=5, m=3: need fits(n+1)=6, fits(m+1)=4, fits(2*n)=10,
   fits(2*(m-1))=4, fits(2*n+2*m)=16 *)
let kmp_fits () : Lemma (
  SZ.fits 4 /\ SZ.fits 6 /\ SZ.fits 10 /\ SZ.fits 16
) =
  assert_norm (pow2 16 == 65536);
  SZ.fits_at_least_16 4;
  SZ.fits_at_least_16 6;
  SZ.fits_at_least_16 10;
  SZ.fits_at_least_16 16

(* Postcondition precision lemma:
   For any sequences with content [0,1,0,1,0] and [0,1,0],
   KMP's count_matches_spec evaluates to 2.

   Pattern matches at positions 0 and 2:
   - Position 0: text[0..2] = [0,1,0] = pattern ✓
   - Position 1: text[1..3] = [1,0,1] ≠ pattern ✗ (text[1]=1 ≠ pat[0]=0)
   - Position 2: text[2..4] = [0,1,0] = pattern ✓
   Total: 2 matches *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 100"
let kmp_count_matches_is_2 (text pat: Seq.seq int)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 0 == 0 /\ Seq.index text 1 == 1 /\ Seq.index text 2 == 0 /\
              Seq.index text 3 == 1 /\ Seq.index text 4 == 0 /\
              Seq.index pat 0 == 0 /\ Seq.index pat 1 == 1 /\ Seq.index pat 2 == 0)
    (ensures Spec.count_matches_spec text pat 5 3 == 2)
  = ()
#pop-options

(* Match position verification: each position individually *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 50"
let kmp_match_at_0 (text pat: Seq.seq int)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 0 == 0 /\ Seq.index text 1 == 1 /\ Seq.index text 2 == 0 /\
              Seq.index pat 0 == 0 /\ Seq.index pat 1 == 1 /\ Seq.index pat 2 == 0)
    (ensures matches_at text pat 0)
  = ()

let kmp_no_match_at_1 (text pat: Seq.seq int)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 1 == 1 /\
              Seq.index pat 0 == 0)
    (ensures ~(matches_at text pat 1))
  = ()

let kmp_match_at_2 (text pat: Seq.seq int)
  : Lemma
    (requires Seq.length text == 5 /\ Seq.length pat == 3 /\
              Seq.index text 2 == 0 /\ Seq.index text 3 == 1 /\ Seq.index text 4 == 0 /\
              Seq.index pat 0 == 0 /\ Seq.index pat 1 == 1 /\ Seq.index pat 2 == 0)
    (ensures matches_at text pat 2)
  = ()
#pop-options

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"

```pulse
(* Test: Precondition satisfiability + Postcondition precision *)
fn test_kmp_string_match ()
  requires emp
  returns _: unit
  ensures emp
{
  // Text: [0, 1, 0, 1, 0] (length 5)
  let tv = V.alloc 0 5sz;
  V.to_array_pts_to tv;
  let text = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 5 0))
       as (A.pts_to text (Seq.create 5 0));
  A.op_Array_Assignment text 0sz 0;
  A.op_Array_Assignment text 1sz 1;
  A.op_Array_Assignment text 2sz 0;
  A.op_Array_Assignment text 3sz 1;
  A.op_Array_Assignment text 4sz 0;

  // Pattern: [0, 1, 0] (length 3)
  let pv = V.alloc 0 3sz;
  V.to_array_pts_to pv;
  let pat = V.vec_to_array pv;
  rewrite (A.pts_to (V.vec_to_array pv) (Seq.create 3 0))
       as (A.pts_to pat (Seq.create 3 0));
  A.op_Array_Assignment pat 0sz 0;
  A.op_Array_Assignment pat 1sz 1;
  A.op_Array_Assignment pat 2sz 0;

  // Ghost counter
  let ctr = GR.alloc #nat 0;

  // Provide SZ.fits facts
  kmp_fits ();

  // Call kmp_string_match
  // Precondition: m > 0, n >= m, fits constraints — all satisfied
  let count = kmp_string_match text pat 5sz 3sz ctr;

  // Bind ghost sequences from postcondition
  with s_text. assert (A.pts_to text s_text);
  with s_pat. assert (A.pts_to pat s_pat);

  // Prove postcondition precision: count must be 2
  kmp_count_matches_is_2 s_text s_pat;
  assert (pure (SZ.v count == 2));

  // Verify individual match positions
  kmp_match_at_0 s_text s_pat;
  kmp_match_at_2 s_text s_pat;
  kmp_no_match_at_1 s_text s_pat;

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
