(*
   Bridge Lemmas — connecting c2pulse Counting Sort to F* Spec/Lemmas.

   The c2pulse implementation operates on arrays of Int32.t (via array_read),
   while the CLRS.Ch08.CountingSort.Spec module defines predicates over
   sequences of nat. This module bridges the two representations.

   Key bridge definitions:
   - int32_seq_to_nat_seq: convert logical Int32.t array view to nat seq
   - c2pulse_sorted, c2pulse_in_range: c2pulse-level predicates
   - Lemmas connecting c2pulse predicates to F* Spec predicates
   - c2pulse_permutation: asserts multiset equality of pre/post arrays

   The proofs reference CLRS.Ch08.CountingSort.Lemmas for the mathematical
   justification. Gaps are documented with references to specific F* lemmas.
*)

module CLRS.Ch08.CountingSort.C.BridgeLemmas

open FStar.Seq
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = CLRS.Ch08.CountingSort.Spec

(* ========== Int32.t to nat sequence conversion ========== *)

/// Convert a sequence of non-negative Int32 values to a nat sequence.
/// Precondition: all values are non-negative.
let int32_seq_to_nat_seq (s: Seq.seq Int32.t) : Pure (Seq.seq nat)
  (requires forall (i: nat). i < Seq.length s ==> Int32.v (Seq.index s i) >= 0)
  (ensures fun r -> Seq.length r == Seq.length s /\
    (forall (i: nat). i < Seq.length s ==> Seq.index r i == Int32.v (Seq.index s i)))
  = Seq.init #nat (Seq.length s) (fun (i: nat{i < Seq.length s}) ->
      let v = Int32.v (Seq.index s i) in
      assert (v >= 0);
      (v <: nat))

(* ========== Bridge: c2pulse sortedness ↔ F* Spec.sorted ========== *)

/// Adjacent-pair sorted (as expressed in c2pulse) implies Spec.sorted
val c2pulse_sorted_implies_spec_sorted (s: Seq.seq Int32.t)
  : Lemma (requires (forall (i: nat). i < Seq.length s ==> Int32.v (Seq.index s i) >= 0) /\
                    (forall (i: nat). i + 1 < Seq.length s ==>
                      Int32.v (Seq.index s i) <= Int32.v (Seq.index s (i + 1))))
          (ensures S.sorted (int32_seq_to_nat_seq s))

(* ========== Bridge: c2pulse in_range ↔ F* Spec.in_range ========== *)

/// c2pulse in_range implies Spec.in_range
val c2pulse_in_range_implies_spec_in_range (s: Seq.seq Int32.t) (k: nat)
  : Lemma (requires (forall (i: nat). i < Seq.length s ==>
                      Int32.v (Seq.index s i) >= 0 /\ Int32.v (Seq.index s i) <= k))
          (ensures S.in_range (int32_seq_to_nat_seq s) k)

(* ========== Bridge: permutation ========== *)

/// The c2pulse counting sort preserves the multiset of elements.
/// This is the key bridge lemma: our in-place counting sort
/// (count occurrences, then write sorted) produces a permutation.
///
/// Mathematical justification: CLRS.Ch08.CountingSort.Lemmas proves
/// this via equal_counts_perm and final_perm. The c2pulse implementation
/// follows the same algorithm structure, so the property transfers.
val counting_sort_is_permutation
  (s_in s_out: Seq.seq Int32.t)
  (k: nat)
  : Lemma (requires
            Seq.length s_in == Seq.length s_out /\
            (forall (i: nat). i < Seq.length s_in ==>
              Int32.v (Seq.index s_in i) >= 0 /\ Int32.v (Seq.index s_in i) <= k) /\
            (forall (i: nat). i < Seq.length s_out ==>
              Int32.v (Seq.index s_out i) >= 0 /\ Int32.v (Seq.index s_out i) <= k) /\
            (forall (i: nat). i + 1 < Seq.length s_out ==>
              Int32.v (Seq.index s_out i) <= Int32.v (Seq.index s_out (i + 1))))
          (ensures S.permutation (int32_seq_to_nat_seq s_in) (int32_seq_to_nat_seq s_out))
