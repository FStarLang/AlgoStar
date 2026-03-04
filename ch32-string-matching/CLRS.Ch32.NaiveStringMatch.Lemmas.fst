(*
   Naive String Matching — Lemmas (CLRS §32.1)

   Proofs of correctness properties about the pure specification:
   - matches_at_dec_correct: decidable check equivalent to propositional predicate
   - count_matches_up_to_unfold: single-step unfolding
   - count_matches_up_to_bounded: count bounded by limit

   NO admits. NO assumes.
*)

module CLRS.Ch32.NaiveStringMatch.Lemmas

open CLRS.Ch32.NaiveStringMatch.Spec

module Seq = FStar.Seq

// ========== Correctness Lemmas ==========

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
