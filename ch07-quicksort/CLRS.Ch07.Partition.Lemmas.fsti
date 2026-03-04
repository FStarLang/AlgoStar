(*
   CLRS Chapter 7: Partition — Lemma Signatures

   Interface for correctness lemmas about the partition operation:
   swap commutativity, swap-permutation, and bounds transfer.
*)
module CLRS.Ch07.Partition.Lemmas

open CLRS.Ch07.Partition.Spec
open CLRS.Common.SortSpec
module Seq = FStar.Seq

val seq_swap_commute (s: Seq.seq int) (i j: nat_smaller (Seq.length s))
  : Lemma (seq_swap s i j == seq_swap s j i)

val permutation_swap (s: Seq.seq int) (i j: nat_smaller (Seq.length s))
  : Lemma (permutation s (seq_swap s i j))
    [SMTPat (permutation s (seq_swap s i j))]

val transfer_larger_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (lb: int)
  : Lemma
    (requires forall (k: int). l <= k /\ k < r ==> (lb <= Seq.index s (k - shift)))
    (ensures larger_than (Seq.slice s (l - shift) (r - shift)) lb)

val transfer_smaller_slice
  (s : Seq.seq int)
  (shift : nat)
  (l : nat{shift <= l})
  (r : nat{l <= r /\ r <= shift + Seq.length s})
  (rb: int)
  : Lemma
    (requires forall (k: int). l <= k /\ k < r ==> (Seq.index s (k - shift) <= rb))
    (ensures smaller_than (Seq.slice s (l - shift) (r - shift)) rb)
