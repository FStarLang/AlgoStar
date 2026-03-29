(*
   Rabin-Karp String Matching — Correctness Lemmas (CLRS §32.2)

   Proofs of correctness for the pure Rabin-Karp specification:
   - No false positives: every returned position is a valid match
   - No false negatives: every valid match is returned
   - Combined correctness theorem

   Definitions and hash algebra are in CLRS.Ch32.RabinKarp.Spec.

   NO admits. NO assumes.
*)

module CLRS.Ch32.RabinKarp.Lemmas

open FStar.Mul
open FStar.Classical
module Seq = FStar.Seq

open CLRS.Ch32.RabinKarp.Spec

(*** Correctness Proofs ***)

//SNIPPET_START: correctness
/// No false positives: every returned position is a valid match.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec rabin_karp_matches_no_false_positives
    (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
    (s:nat) (current_hash:nat)
  : Lemma (ensures (let results = rabin_karp_matches text pattern d q s current_hash in
                    forall (pos:nat). List.Tot.mem pos results ==>
                      pos >= s /\ matches_at text pattern pos))
          (decreases Seq.length text - s)
  = let m = Seq.length pattern in
    if m = 0 || s + m > Seq.length text then ()
    else (
      if verify_match text pattern s current_hash (hash pattern d q 0 m) then
        matches_at_dec_correct text pattern s;
      if s + m < Seq.length text then
        let h = pow_mod d (m - 1) q in
        let next = rolling_hash_step current_hash
                     (Seq.index text s) (Seq.index text (s + m)) d q h in
        rabin_karp_matches_no_false_positives text pattern d q (s + 1) next
    )
#pop-options

/// No false negatives: every valid match appears in results.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100 --split_queries always"
let rec rabin_karp_matches_no_false_negatives
    (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
    (s:nat) (current_hash:nat)
  : Lemma (requires (let m = Seq.length pattern in
                     m > 0 /\ s + m <= Seq.length text /\
                     current_hash == hash text d q s (s + m)))
          (ensures (let m = Seq.length pattern in
                    let results = rabin_karp_matches text pattern d q s current_hash in
                    forall (pos:nat). s <= pos /\ pos + m <= Seq.length text /\
                      matches_at text pattern pos ==> List.Tot.mem pos results))
          (decreases (Seq.length text - s))
  = let m = Seq.length pattern in
    if m = 0 || s + m > Seq.length text then ()
    else (
      // At position s: matching substrings have equal hashes, so verify_match succeeds
      let helper_at_s () : Lemma
        (requires matches_at text pattern s)
        (ensures List.Tot.mem s (rabin_karp_matches text pattern d q s current_hash))
        = hash_match_lemma text pattern d q s;
          matches_at_dec_correct text pattern s
      in
      Classical.move_requires helper_at_s ();
      // Inductive step: rolling hash gives correct hash for s+1
      if s + m < Seq.length text then (
        let h = pow_mod d (m - 1) q in
        let next = rolling_hash_step current_hash
                     (Seq.index text s) (Seq.index text (s + m)) d q h in
        rolling_hash_step_correct text d q s m current_hash h;
        assert (next == hash text d q (s + 1) (s + m + 1));
        rabin_karp_matches_no_false_negatives text pattern d q (s + 1) next
      )
    )
#pop-options

/// Main theorem: rabin_karp_find_all is correct (no false positives, no false negatives).
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let rabin_karp_find_all_no_false_positives (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
  : Lemma (forall (pos:nat). List.Tot.mem pos (rabin_karp_find_all text pattern d q) ==>
              matches_at text pattern pos)
  = let m = Seq.length pattern in
    if m = 0 || m > Seq.length text then ()
    else rabin_karp_matches_no_false_positives text pattern d q 0 (hash text d q 0 m)

let rabin_karp_find_all_no_false_negatives (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
  : Lemma (requires Seq.length pattern > 0)
          (ensures forall (pos:nat). pos + Seq.length pattern <= Seq.length text /\
                              matches_at text pattern pos ==>
              List.Tot.mem pos (rabin_karp_find_all text pattern d q))
  = let m = Seq.length pattern in
    if m > Seq.length text then ()
    else rabin_karp_matches_no_false_negatives text pattern d q 0 (hash text d q 0 m)

let rabin_karp_find_all_correct (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
  : Lemma (let results = rabin_karp_find_all text pattern d q in
           (forall (pos:nat). List.Tot.mem pos results ==> matches_at text pattern pos) /\
           (Seq.length pattern > 0 ==>
             (forall (pos:nat). pos + Seq.length pattern <= Seq.length text /\
                                matches_at text pattern pos ==> List.Tot.mem pos results)))
  = rabin_karp_find_all_no_false_positives text pattern d q;
    if Seq.length pattern > 0 then
      rabin_karp_find_all_no_false_negatives text pattern d q
#pop-options
//SNIPPET_END: correctness
