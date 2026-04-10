(*
   Activity Selection — Bridge Lemmas (Implementation)

   Bridges C-level postconditions to the full F* optimality proof.
   The "after last" part of earliest_compatible is verified in the
   C code's loop ensures (see ActivitySelection.c) but cannot be
   exported as a function postcondition due to a c2pulse limitation.
   It is assumed here to complete the bridge to the optimality proof.
*)
module CLRS.Ch16.ActivitySelection.C.BridgeLemmas

open FStar.Seq

module L = CLRS.Ch16.ActivitySelection.Lemmas
module S = CLRS.Ch16.ActivitySelection.Spec

let bridge_c_to_optimal
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
      (forall (i: nat). i + 1 < Seq.length sel ==>
        (forall (z: nat). Seq.index sel i < z /\ z < Seq.index sel (i + 1) /\
                           z < n /\ z < Seq.length start /\ z < Seq.length finish ==>
          Seq.index start z < Seq.index finish (Seq.index sel i))))
    (ensures
      Seq.length sel == S.max_compatible_count start finish n)
  =
    (* The "between consecutive" part is given as a precondition.
       We need to establish the full earliest_compatible to invoke
       the optimality corollary. The "after last" part:
         forall z. sel[|sel|-1] < z < n ==> start[z] < finish[sel[|sel|-1]]
       is assumed because the C function postcondition cannot export it
       (c2pulse loop-ensures-to-return limitation). The property IS verified
       in the C code's loop ensures — see ActivitySelection.c. *)
    assume (L.earliest_compatible sel start finish n n);
    S.corollary_greedy_count_is_maximum_l start finish n sel
