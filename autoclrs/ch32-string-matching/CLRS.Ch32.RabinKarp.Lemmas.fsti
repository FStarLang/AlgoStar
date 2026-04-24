(*
   Rabin-Karp String Matching — Correctness Lemmas Interface (CLRS §32.2)
*)

module CLRS.Ch32.RabinKarp.Lemmas

module Seq = FStar.Seq

open CLRS.Ch32.RabinKarp.Spec

/// No false positives: every returned position is a valid match.
val rabin_karp_matches_no_false_positives
    (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
    (s:nat) (current_hash:nat)
  : Lemma (ensures (let results = rabin_karp_matches text pattern d q s current_hash in
                    forall (pos:nat). List.Tot.mem pos results ==>
                      pos >= s /\ matches_at text pattern pos))

/// No false negatives: every valid match appears in results.
val rabin_karp_matches_no_false_negatives
    (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
    (s:nat) (current_hash:nat)
  : Lemma (requires (let m = Seq.length pattern in
                     m > 0 /\ s + m <= Seq.length text /\
                     current_hash == hash text d q s (s + m)))
          (ensures (let m = Seq.length pattern in
                    let results = rabin_karp_matches text pattern d q s current_hash in
                    forall (pos:nat). s <= pos /\ pos + m <= Seq.length text /\
                      matches_at text pattern pos ==> List.Tot.mem pos results))

/// Top-level no false positives
val rabin_karp_find_all_no_false_positives (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
  : Lemma (forall (pos:nat). List.Tot.mem pos (rabin_karp_find_all text pattern d q) ==>
              matches_at text pattern pos)

/// Top-level no false negatives
val rabin_karp_find_all_no_false_negatives (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
  : Lemma (requires Seq.length pattern > 0)
          (ensures forall (pos:nat). pos + Seq.length pattern <= Seq.length text /\
                              matches_at text pattern pos ==>
              List.Tot.mem pos (rabin_karp_find_all text pattern d q))

/// Main correctness theorem: rabin_karp_find_all is correct.
val rabin_karp_find_all_correct (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
  : Lemma (let results = rabin_karp_find_all text pattern d q in
           (forall (pos:nat). List.Tot.mem pos results ==> matches_at text pattern pos) /\
           (Seq.length pattern > 0 ==>
             (forall (pos:nat). pos + Seq.length pattern <= Seq.length text /\
                                matches_at text pattern pos ==> List.Tot.mem pos results)))
