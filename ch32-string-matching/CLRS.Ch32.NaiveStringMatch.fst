(*
   Naive String Matching Algorithm - Verified implementation in Pulse
   
   Implements the naive string matching algorithm from CLRS Chapter 32:
   Given text of length n and pattern of length m, finds all occurrences
   of pattern in text using the straightforward O((n-m+1)*m) algorithm.
   
   NO admits. NO assumes.
*)

module CLRS.Ch32.NaiveStringMatch
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

#push-options "--z3rlimit 40 --ifuel 2 --fuel 2"

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Pure Specification ==========

// Does pattern match text starting at position s?
let matches_at (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) : prop =
  s + Seq.length pattern <= Seq.length text /\
  (forall (j: nat). j < Seq.length pattern ==> 
    Seq.index text (s + j) == Seq.index pattern j)

// Decidable check for matching
let rec check_match_at (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) (j: nat{j <= Seq.length pattern})
  : Tot bool (decreases (Seq.length pattern - j))
  = if j >= Seq.length pattern then true
    else if s + j >= Seq.length text then false
    else if Seq.index text (s + j) = Seq.index pattern j 
         then check_match_at text pattern s (j + 1)
         else false

// Decidable version
let matches_at_dec (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) : bool =
  s + Seq.length pattern <= Seq.length text && check_match_at text pattern s 0

// Lemma: correctness of decidable version
let rec check_match_at_correct (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) (j: nat{j <= Seq.length pattern})
  : Lemma (requires s + Seq.length pattern <= Seq.length text)
          (ensures check_match_at text pattern s j <==> 
                   (forall (k: nat). j <= k /\ k < Seq.length pattern ==> 
                     Seq.index text (s + k) == Seq.index pattern k))
          (decreases (Seq.length pattern - j))
  = if j >= Seq.length pattern then ()
    else check_match_at_correct text pattern s (j + 1)

let matches_at_dec_correct (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat)
  : Lemma (requires s + Seq.length pattern <= Seq.length text)
          (ensures matches_at_dec text pattern s <==> matches_at text pattern s)
  = check_match_at_correct text pattern s 0

// Simple count: how many positions from 0 to limit have matches
let rec count_matches_up_to (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (limit: nat)
  : Tot nat (decreases limit)
  = if limit = 0 then 0
    else count_matches_up_to text pattern (limit - 1) + 
         (if matches_at_dec text pattern (limit - 1) then 1 else 0)

// ========== Helper Lemmas ==========

// Unfold one step of count_matches_up_to
let count_matches_up_to_unfold (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (limit: nat)
  : Lemma (requires limit > 0)
          (ensures count_matches_up_to text pattern limit ==
                   count_matches_up_to text pattern (limit - 1) + 
                   (if matches_at_dec text pattern (limit - 1) then 1 else 0))
  = ()

// count_matches_up_to is bounded by the limit
let rec count_matches_up_to_bounded (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (limit: nat)
  : Lemma (ensures count_matches_up_to text pattern limit <= limit)
          (decreases limit)
  = if limit = 0 then ()
    else count_matches_up_to_bounded text pattern (limit - 1)

// ========== Pulse Implementation ==========

fn naive_string_match
  (#a: eqtype)
  (#p_text: perm)
  (#p_pat: perm)
  (text: array a)
  (pattern: array a)
  (#s_text: Ghost.erased (Seq.seq a))
  (#s_pat: Ghost.erased (Seq.seq a))
  (n: SZ.t)
  (m: SZ.t)
  requires 
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    pure (
      SZ.v n == Seq.length s_text /\
      SZ.v m == Seq.length s_pat /\
      Seq.length s_text <= A.length text /\
      Seq.length s_pat <= A.length pattern /\
      SZ.v m > 0 /\
      SZ.v m <= SZ.v n /\
      SZ.fits (SZ.v n - SZ.v m + 2)
    )
  returns result: SZ.t
  ensures
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    pure (
      SZ.v result <= SZ.v n - SZ.v m + 1 /\
      SZ.v result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1)
    )
{
  let mut count: SZ.t = 0sz;
  let mut s: SZ.t = 0sz;  // current position in text
  
  // Outer loop: try each starting position
  while (!s <=^ (n -^ m))
  invariant exists* vs vcount.
    R.pts_to s vs **
    R.pts_to count vcount **
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    pure (
      SZ.v vs <= SZ.v n - SZ.v m + 1 /\
      SZ.v vcount == count_matches_up_to s_text s_pat (SZ.v vs) /\
      SZ.v vcount <= SZ.v vs
    )
  {
    let vs = !s;
    let vcount_outer = !count;
    
    // Inner loop: check if pattern matches at position vs
    let mut j: SZ.t = 0sz;
    let mut all_match: bool = true;
    
    while (!j <^ m && !all_match)
    invariant exists* vj vall_match vcount.
      R.pts_to s vs **
      R.pts_to count vcount **
      R.pts_to j vj **
      R.pts_to all_match vall_match **
      A.pts_to text #p_text s_text **
      A.pts_to pattern #p_pat s_pat **
      pure (
        SZ.v vj <= SZ.v m /\
        SZ.v vcount == SZ.v vcount_outer /\
        (vall_match == true ==> (forall (k: nat). k < SZ.v vj ==> 
          Seq.index s_text (SZ.v vs + k) == Seq.index s_pat k)) /\
        (vall_match == false ==> (exists (k: nat). k < SZ.v vj /\ 
          Seq.index s_text (SZ.v vs + k) <> Seq.index s_pat k))
      )
    {
      let vj = !j;
      
      // Compare text[vs + vj] with pattern[vj]
      let text_char = text.(vs +^ vj);
      let pat_char = pattern.(vj);
      
      if (text_char <> pat_char) {
        // Mismatch found
        all_match := false;
      };
      
      j := vj +^ 1sz;
    };
    
    // Check if we found a full match
    let final_j = !j;
    let final_all_match = !all_match;
    let vcount_before = !count;
    
    // After inner loop: final_all_match && final_j == m <==> matches_at_dec
    // When all_match is true and j == m: all m chars matched
    // When all_match is false: some char didn't match
    // When j < m and all_match is true: loop exited because !all_match was false
    //   (but that can only happen if all_match == false, contradiction)
    
    // Establish: (final_j = m && final_all_match) <==> matches_at_dec
    matches_at_dec_correct s_text s_pat (SZ.v vs);
    
    if (final_j = m && final_all_match) {
      // We went through all m characters and they all matched
      count := vcount_before +^ 1sz;
    };
    
    // After count update: count == count_matches_up_to s_text s_pat (vs + 1)
    count_matches_up_to_unfold s_text s_pat (SZ.v vs + 1);
    count_matches_up_to_bounded s_text s_pat (SZ.v vs + 1);
    
    s := vs +^ 1sz;
  };
  
  let final_count = !count;
  final_count
}

#pop-options
