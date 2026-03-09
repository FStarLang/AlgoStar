(*
   Naive String Matching — Lemmas Interface (CLRS §32.1)
*)

module CLRS.Ch32.NaiveStringMatch.Lemmas

open CLRS.Ch32.NaiveStringMatch.Spec

module Seq = FStar.Seq

/// Decidable check is correct w.r.t. propositional match
val check_match_at_correct (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) (j: nat{j <= Seq.length pattern})
  : Lemma (requires s + Seq.length pattern <= Seq.length text)
          (ensures check_match_at text pattern s j <==> 
                   (forall (k: nat). j <= k /\ k < Seq.length pattern ==> 
                     Seq.index text (s + k) == Seq.index pattern k))

/// matches_at_dec is equivalent to matches_at
val matches_at_dec_correct (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat)
  : Lemma (requires s + Seq.length pattern <= Seq.length text)
          (ensures matches_at_dec text pattern s <==> matches_at text pattern s)

/// One-step unfolding of count_matches_up_to
val count_matches_up_to_unfold (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (limit: nat)
  : Lemma (requires limit > 0)
          (ensures count_matches_up_to text pattern limit ==
                   count_matches_up_to text pattern (limit - 1) + 
                   (if matches_at_dec text pattern (limit - 1) then 1 else 0))

/// count_matches_up_to is bounded by the limit
val count_matches_up_to_bounded (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (limit: nat)
  : Lemma (ensures count_matches_up_to text pattern limit <= limit)
