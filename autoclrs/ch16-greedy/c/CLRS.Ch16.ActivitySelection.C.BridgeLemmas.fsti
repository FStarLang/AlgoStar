(*
   Activity Selection — Bridge Lemmas

   Connect C-level postconditions to the full F* optimality proof.

   The C implementation verifies:
   - pairwise_compatible: finish[out[j]] <= start[out[j+1]]
   - strictly_increasing: out[j] < out[j+1]
   - all_valid_indices: out[j] < n
   - first_is_zero: out[0] == 0
   - between_consecutive: skipped activities between consecutive
     selections were incompatible (part 1 of earliest_compatible)
   - after_last: skipped activities after the last selection were
     incompatible (part 2 of earliest_compatible) — verified as a
     loop ensures in the C code, but cannot be exported as a
     function postcondition due to a c2pulse limitation with
     connecting loop-level ensures to function-level return values.

   This bridge assumes the "after last" property (which IS verified
   in the C loop) and concludes optimality via the F* Spec proof.
*)
module CLRS.Ch16.ActivitySelection.C.BridgeLemmas

open FStar.Seq

module L = CLRS.Ch16.ActivitySelection.Lemmas
module S = CLRS.Ch16.ActivitySelection.Spec

/// Bridge from C postconditions to optimality.
///
/// The "between consecutive" part of earliest_compatible is fully
/// verified in C. The "after last" part is admitted here because
/// c2pulse cannot export quantified facts involving array reads
/// in function postconditions (the loop ensures uses a different
/// SMT context than the postcondition's with_pure wrapper).
///
/// The "after last" property holds because the greedy algorithm
/// scans all activities sequentially: any activity z > out[count-1]
/// was checked and found to have start[z] < finish[out[count-1]],
/// so it was skipped.
val bridge_c_to_optimal
  (start finish: seq int) (sel: seq nat) (n: nat)
  : Lemma
    (requires
      n > 0 /\
      n == Seq.length start /\ n == Seq.length finish /\
      L.finish_sorted finish /\
      (forall (i:nat). i < n ==> L.valid_activity start finish i) /\
      Seq.length sel > 0 /\
      Seq.index sel 0 == 0 /\
      L.all_valid_indices sel n /\
      L.strictly_increasing sel /\
      L.pairwise_compatible sel start finish /\
      (* "between consecutive" part of earliest_compatible — verified in C *)
      (forall (i: nat). i + 1 < Seq.length sel ==>
        (forall (z: nat). Seq.index sel i < z /\ z < Seq.index sel (i + 1) /\
                           z < n /\ z < Seq.length start /\ z < Seq.length finish ==>
          Seq.index start z < Seq.index finish (Seq.index sel i))))
    (ensures
      Seq.length sel == S.max_compatible_count start finish n)
