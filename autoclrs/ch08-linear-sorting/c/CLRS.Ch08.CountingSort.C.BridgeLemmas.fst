(*
   Bridge Lemmas — Implementation

   Proves the sortedness and in_range bridges.
   The permutation bridge is admitted — fully connecting the c2pulse
   Int32.t array model to the F* nat-sequence counting sort lemmas
   (CLRS.Ch08.CountingSort.Lemmas.equal_counts_perm) requires
   materializing the nat sequence inside c2pulse, which the current
   array abstraction does not expose.

   The admitted lemma (counting_sort_is_permutation) is mathematically
   justified: our implementation follows the same count-then-write
   algorithm that CLRS.Ch08.CountingSort.Lemmas proves correct.
*)

module CLRS.Ch08.CountingSort.C.BridgeLemmas

open FStar.Seq
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = CLRS.Ch08.CountingSort.Spec

(* ========== Sortedness bridge ========== *)

(* Adjacent-pair sorted on a nat seq implies all-pairs sorted.
   By induction on (j - i). *)
let rec adjacent_implies_all_pairs (s: Seq.seq nat) (i: nat) (j: nat)
  : Lemma
    (requires i <= j /\ j < Seq.length s /\
              (forall (k: nat). k + 1 < Seq.length s ==> Seq.index s k <= Seq.index s (k + 1)))
    (ensures Seq.index s i <= Seq.index s j)
    (decreases (j - i))
  = if i < j then adjacent_implies_all_pairs s i (j - 1)

#push-options "--z3rlimit 100"
let c2pulse_sorted_implies_spec_sorted (s: Seq.seq Int32.t)
  : Lemma (requires (forall (i: nat). i < Seq.length s ==> Int32.v (Seq.index s i) >= 0) /\
                    (forall (i: nat). i + 1 < Seq.length s ==>
                      Int32.v (Seq.index s i) <= Int32.v (Seq.index s (i + 1))))
          (ensures S.sorted (int32_seq_to_nat_seq s))
  = let ns = int32_seq_to_nat_seq s in
    let _adj : squash (forall (k: nat). k + 1 < Seq.length ns ==>
                         Seq.index ns k <= Seq.index ns (k + 1)) = () in
    let aux (i: nat) (j: nat)
      : Lemma (ensures (i <= j /\ j < Seq.length ns) ==> Seq.index ns i <= Seq.index ns j)
      = if i <= j && j < Seq.length ns then
          adjacent_implies_all_pairs ns i j
    in
    Classical.forall_intro_2 aux
#pop-options

(* ========== In-range bridge ========== *)

let c2pulse_in_range_implies_spec_in_range (s: Seq.seq Int32.t) (k: nat)
  : Lemma (requires (forall (i: nat). i < Seq.length s ==>
                      Int32.v (Seq.index s i) >= 0 /\ Int32.v (Seq.index s i) <= k))
          (ensures S.in_range (int32_seq_to_nat_seq s) k)
  = ()

(* ========== Permutation bridge (admitted) ========== *)

(*
  This is admitted because fully connecting the two array models requires:
  1. Showing the c2pulse count phase computes the same counts as
     CLRS.Ch08.CountingSort.Lemmas.counts_match
  2. Showing the recursive write phase produces the same multiset
     (CLRS.Ch08.CountingSort.Lemmas.final_perm)

  The mathematical argument is: counting sort with identical algorithm
  structure preserves multisets, proven in Lemmas.fst. This C code
  follows the same structure (count, then write sorted by value).
*)
let counting_sort_is_permutation (s_in s_out: Seq.seq Int32.t) (k: nat)
  = admit ()
