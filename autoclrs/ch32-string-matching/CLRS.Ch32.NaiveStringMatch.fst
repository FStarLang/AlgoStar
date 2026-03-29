(*
   Naive String Matching Algorithm - Verified implementation in Pulse (CLRS §32.1)
   
   Implements the naive string matching algorithm from CLRS Chapter 32:
   Given text of length n and pattern of length m, finds all occurrences
   of pattern in text using the straightforward O((n-m+1)*m) algorithm.
   
   Proves both functional correctness and O((n-m+1)·m) complexity bound.

   Pure specification in CLRS.Ch32.NaiveStringMatch.Spec
   Correctness lemmas in CLRS.Ch32.NaiveStringMatch.Lemmas
   Complexity definition in CLRS.Ch32.NaiveStringMatch.Complexity

   NO admits. NO assumes.
*)

module CLRS.Ch32.NaiveStringMatch
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

open CLRS.Ch32.NaiveStringMatch.Spec
open CLRS.Ch32.NaiveStringMatch.Lemmas
open CLRS.Ch32.NaiveStringMatch.Complexity
open CLRS.Common.Complexity

#push-options "--z3rlimit 20 --ifuel 2 --fuel 2"

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Pulse Implementation ==========

//SNIPPET_START: naive_string_match_sig
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
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires 
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s_text /\
      SZ.v m == Seq.length s_pat /\
      Seq.length s_text <= A.length text /\
      Seq.length s_pat <= A.length pattern /\
      SZ.v m > 0 /\
      SZ.v m <= SZ.v n /\
      SZ.fits (SZ.v n - SZ.v m + 2) /\
      SZ.fits (op_Multiply (SZ.v n - SZ.v m + 1) (SZ.v m))
    )
  returns result: SZ.t
  ensures exists* (cf: nat).
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr cf **
    pure (
      SZ.v result <= SZ.v n - SZ.v m + 1 /\
      SZ.v result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1) /\
      string_match_complexity_bounded cf (reveal c0) (SZ.v n) (SZ.v m)
    )
//SNIPPET_END: naive_string_match_sig
{
  let mut count: SZ.t = 0sz;
  let mut s: SZ.t = 0sz;
  
  // Outer loop: try each starting position
  while (!s <=^ (n -^ m))
  invariant exists* vs vcount (vc : nat).
    R.pts_to s vs **
    R.pts_to count vcount **
    GR.pts_to ctr vc **
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    pure (
      SZ.v vs <= SZ.v n - SZ.v m + 1 /\
      SZ.v vcount == count_matches_up_to s_text s_pat (SZ.v vs) /\
      SZ.v vcount <= SZ.v vs /\
      vc >= reveal c0 /\
      vc - reveal c0 <= op_Multiply (SZ.v vs) (SZ.v m)
    )
  decreases (SZ.v n - SZ.v !s)
  {
    let vs = !s;
    let vcount_outer = !count;
    
    // Inner loop: check if pattern matches at position vs
    let mut j: SZ.t = 0sz;
    let mut all_match: bool = true;
    
    while (!j <^ m && !all_match)
    invariant exists* vj vall_match vcount (vc_inner : nat).
      R.pts_to s vs **
      R.pts_to count vcount **
      R.pts_to j vj **
      R.pts_to all_match vall_match **
      GR.pts_to ctr vc_inner **
      A.pts_to text #p_text s_text **
      A.pts_to pattern #p_pat s_pat **
      pure (
        SZ.v vj <= SZ.v m /\
        SZ.v vcount == SZ.v vcount_outer /\
        (vall_match == true ==> (forall (k: nat). k < SZ.v vj ==> 
          Seq.index s_text (SZ.v vs + k) == Seq.index s_pat k)) /\
        (vall_match == false ==> (exists (k: nat). k < SZ.v vj /\ 
          Seq.index s_text (SZ.v vs + k) <> Seq.index s_pat k)) /\
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 <= op_Multiply (SZ.v vs) (SZ.v m) + SZ.v vj /\
        vc_inner - reveal c0 <= op_Multiply (SZ.v vs) (SZ.v m) + SZ.v m
      )
    decreases (SZ.v m - SZ.v !j)
    {
      let vj = !j;
      
      // Compare text[vs + vj] with pattern[vj]
      let text_char = text.(vs +^ vj);
      let pat_char = pattern.(vj);
      
      // Count the comparison — one ghost tick
      tick ctr;

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
