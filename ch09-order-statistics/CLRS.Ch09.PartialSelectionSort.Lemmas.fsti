(*
   CLRS Chapter 9: Partial Selection Sort — Lemma Signatures

   Key lemmas for proving correctness:
   - sorted_permutation_equal: sorted permutations of the same multiset are equal
   - pulse_correctness_hint: bridge from partition property to select_spec

   NO admits. NO assumes.
*)
module CLRS.Ch09.PartialSelectionSort.Lemmas

open FStar.Seq
open CLRS.Ch09.PartialSelectionSort.Spec

module Seq = FStar.Seq

/// If s1 and s2 are both sorted and are permutations of each other, then s1 = s2.
val sorted_permutation_equal (s1 s2: seq int)
  : Lemma (requires is_sorted s1 /\ is_sorted s2 /\ is_permutation s1 s2)
          (ensures Seq.equal s1 s2)

/// Partition left part: if k < p, select_spec is preserved.
val partition_left_part_correct (s s': seq int) (k lo p hi: nat)
  : Lemma (requires lo <= k /\ k < p /\ p < hi /\ hi <= Seq.length s /\
                    is_permutation s s' /\
                    (forall (i: nat). lo <= i /\ i < p ==> Seq.index s' i <= Seq.index s' p) /\
                    (forall (i: nat). p < i /\ i < hi ==> Seq.index s' p <= Seq.index s' i))
          (ensures select_spec s k == select_spec s' k)

/// Partition right part: if k > p, select_spec is preserved.
val partition_right_part_correct (s s': seq int) (k lo p hi: nat)
  : Lemma (requires lo <= p /\ p < k /\ k < hi /\ hi <= Seq.length s /\
                    is_permutation s s' /\
                    (forall (i: nat). lo <= i /\ i < p ==> Seq.index s' i <= Seq.index s' p) /\
                    (forall (i: nat). p < i /\ i < hi ==> Seq.index s' p <= Seq.index s' i))
          (ensures select_spec s k == select_spec s' k)

/// Partition pivot is kth: if k == p in a fully-partitioned array, s'[p] is kth.
val partition_pivot_is_kth (s s': seq int) (k lo p hi: nat)
  : Lemma (requires lo <= k /\ k == p /\ p < hi /\ hi <= Seq.length s /\
                    is_permutation s s' /\
                    (forall (i: nat). lo <= i /\ i < p ==> Seq.index s' i <= Seq.index s' p) /\
                    (forall (i: nat). p < i /\ i < hi ==> Seq.index s' p <= Seq.index s' i) /\
                    lo == 0 /\ hi == Seq.length s)
          (ensures Seq.index s' p == select_spec s k)

/// If s_final is a permutation of s0 and s_final is partitioned at k
/// (all elements before k are ≤ s_final[k], all after are ≥), then
/// s_final[k] = select_spec s0 k.
val pulse_correctness_hint (s0 s_final: seq int) (k: nat)
  : Lemma (requires k < Seq.length s0 /\
                    Seq.length s_final == Seq.length s0 /\
                    is_permutation s0 s_final /\
                    (forall (i: nat). i < k ==> Seq.index s_final i <= Seq.index s_final k) /\
                    (forall (i: nat). k < i /\ i < Seq.length s_final ==>
                      Seq.index s_final k <= Seq.index s_final i))
          (ensures Seq.index s_final k == select_spec s0 k)
