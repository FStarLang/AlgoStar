(*
   CLRS Chapter 9.2: Quickselect — Lemma Signatures

   Key lemmas for strengthening quickselect's postcondition:
   - Bound preservation through partitions
   - Bridge between Seq.Properties.permutation and count_occ-based is_permutation
   - Correctness bridge to select_spec
*)
module CLRS.Ch09.Quickselect.Lemmas

open FStar.Seq
module Seq = FStar.Seq
module Spec = CLRS.Ch09.PartialSelectionSort.Spec

/// If all values in s_pre[lo..hi) are >= v, and s1 is a permutation of s_pre
/// with elements outside [lo,hi) unchanged, then all values in s1[lo..hi) are >= v.
val perm_unchanged_lower_bound_forall
  (s_pre s1: Seq.seq int) (lo hi: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s_pre /\
              Seq.length s_pre == Seq.length s1 /\
              Seq.Properties.permutation int s_pre s1 /\
              (forall (idx: nat). idx < Seq.length s1 ==>
                (idx < lo \/ hi <= idx) ==> Seq.index s1 idx == Seq.index s_pre idx))
    (ensures forall (j: nat) (v: int). lo <= j /\ j < hi /\
              (forall (m: nat). lo <= m /\ m < hi ==> v <= Seq.index s_pre m) ==>
              v <= Seq.index s1 j)

/// Symmetric: upper bound preservation
val perm_unchanged_upper_bound_forall
  (s_pre s1: Seq.seq int) (lo hi: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s_pre /\
              Seq.length s_pre == Seq.length s1 /\
              Seq.Properties.permutation int s_pre s1 /\
              (forall (idx: nat). idx < Seq.length s1 ==>
                (idx < lo \/ hi <= idx) ==> Seq.index s1 idx == Seq.index s_pre idx))
    (ensures forall (j: nat) (v: int). lo <= j /\ j < hi /\
              (forall (m: nat). lo <= m /\ m < hi ==> Seq.index s_pre m <= v) ==>
              Seq.index s1 j <= v)

/// Bridge: Seq.Properties.permutation ==> Spec.is_permutation (given equal lengths)
val seq_perm_implies_is_perm (s1 s2: Seq.seq int)
  : Lemma (requires Seq.Properties.permutation int s1 s2 /\
                    Seq.length s1 == Seq.length s2)
          (ensures Spec.is_permutation s1 s2)
