(*
   Merge Sort - Lemma signatures

   Interface for lemmas about the pure seq_merge specification.
*)
module CLRS.Ch02.MergeSort.Lemmas

open CLRS.Common.SortSpec
open CLRS.Ch02.MergeSort.Spec
open CLRS.Ch02.MergeSort.Complexity
open Pulse.Lib.BoundedIntegers
module Seq = FStar.Seq

/// seq_merge preserves total length
val seq_merge_length (s1 s2: Seq.seq int)
  : Lemma (ensures Seq.length (seq_merge s1 s2) == Seq.length s1 + Seq.length s2)
          [SMTPat (Seq.length (seq_merge s1 s2))]

/// seq_merge result is a permutation of append
val seq_merge_permutation (s1 s2: Seq.seq int)
  : Lemma (ensures permutation (Seq.append s1 s2) (seq_merge s1 s2))

/// seq_merge preserves sortedness
val seq_merge_sorted (s1 s2: Seq.seq int)
  : Lemma (requires sorted s1 /\ sorted s2)
          (ensures sorted (seq_merge s1 s2))

/// Suffix step: take from left
val suffix_step_left (s1 s2: Seq.seq int) (i l1 j l2: nat)
  : Lemma (requires i < l1 /\ l1 <= Seq.length s1 /\
                     j <= l2 /\ l2 <= Seq.length s2 /\
                     (Seq.length (Seq.slice s2 j l2) = 0 \/
                      Seq.index s1 i <= Seq.head (Seq.slice s2 j l2)))
          (ensures
            Seq.length (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) > 0 /\
            Seq.head (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) == Seq.index s1 i /\
            seq_merge (Seq.slice s1 (i+1) l1) (Seq.slice s2 j l2) ==
            Seq.tail (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)))

/// Suffix step: take from right
val suffix_step_right (s1 s2: Seq.seq int) (i l1 j l2: nat)
  : Lemma (requires i <= l1 /\ l1 <= Seq.length s1 /\
                     j < l2 /\ l2 <= Seq.length s2 /\
                     (Seq.length (Seq.slice s1 i l1) = 0 \/
                      ~(Seq.index s1 i <= Seq.index s2 j)))
          (ensures
            Seq.length (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) > 0 /\
            Seq.head (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)) == Seq.index s2 j /\
            seq_merge (Seq.slice s1 i l1) (Seq.slice s2 (j+1) l2) ==
            Seq.tail (seq_merge (Seq.slice s1 i l1) (Seq.slice s2 j l2)))

/// Full slice identity
val slice_full (s: Seq.seq int)
  : Lemma (Seq.equal (Seq.slice s 0 (Seq.length s)) s)
          [SMTPat (Seq.slice s 0 (Seq.length s))]

/// Suffix head gives index into merged sequence
val suffix_gives_index (merged: Seq.seq int) (k: nat) (suffix: Seq.seq int)
  : Lemma (requires k < Seq.length merged /\
                     Seq.equal suffix (Seq.slice merged k (Seq.length merged)) /\
                     Seq.length suffix > 0)
          (ensures Seq.head suffix == Seq.index merged k)

/// ms_cost split lemma: cost of left + right + merge <= total cost
val ms_cost_split (n: int{n >= 2})
  : Lemma (ensures ms_cost (n / 2) + ms_cost (n - n / 2) + n <= ms_cost n)
