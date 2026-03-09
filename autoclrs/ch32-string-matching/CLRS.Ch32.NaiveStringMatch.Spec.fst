(*
   Naive String Matching — Pure Specification (CLRS §32.1)

   Pure F* specification of the naive string matching algorithm:
   - matches_at: propositional match predicate
   - matches_at_dec: decidable match check
   - count_matches_up_to: count of matches in a prefix

   NO admits. NO assumes.
*)

module CLRS.Ch32.NaiveStringMatch.Spec

module Seq = FStar.Seq

// ========== Pure Specification ==========

//SNIPPET_START: matches_at_spec
// Does pattern match text starting at position s?
let matches_at (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) : prop =
  s + Seq.length pattern <= Seq.length text /\
  (forall (j: nat). j < Seq.length pattern ==> 
    Seq.index text (s + j) == Seq.index pattern j)
//SNIPPET_END: matches_at_spec

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

// Simple count: how many positions from 0 to limit have matches
let rec count_matches_up_to (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (limit: nat)
  : Tot nat (decreases limit)
  = if limit = 0 then 0
    else count_matches_up_to text pattern (limit - 1) + 
         (if matches_at_dec text pattern (limit - 1) then 1 else 0)
