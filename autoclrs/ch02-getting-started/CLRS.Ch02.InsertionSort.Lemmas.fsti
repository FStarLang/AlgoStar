(*
   Insertion Sort - Lemma signatures
*)
module CLRS.Ch02.InsertionSort.Lemmas

open CLRS.Common.SortSpec
open Pulse.Lib.BoundedIntegers
module Seq = FStar.Seq

val lemma_prefix_le_key
  (s s_outer: Seq.seq int) (vi vj: nat) (key: int)
  : Lemma
    (requires
      vi <= vj /\ vj < Seq.length s /\ Seq.length s == Seq.length s_outer /\
      prefix_sorted s_outer vj /\
      prefix_sorted s vi /\
      (forall (k: nat). k < vi ==> Seq.index s k == Seq.index s_outer k) /\
      (forall (k: nat). k + 1 == vi ==> Seq.index s_outer k <= key))
    (ensures forall (k: nat). k < vi ==> Seq.index s k <= key)

val lemma_combine_sorted_regions
  (s: Seq.seq int) (vi vj: nat) (key: int)
  : Lemma
    (requires vi <= vj /\ vj < Seq.length s /\
      prefix_sorted s vi /\
      Seq.index s vi == key /\
      (forall (k: nat). k < vi ==> Seq.index s k <= key) /\
      (forall (k: nat). vi < k /\ k <= vj ==> Seq.index s k > key) /\
      (forall (k1 k2: nat). vi < k1 /\ k1 <= k2 /\ k2 <= vj ==>
        Seq.index s k1 <= Seq.index s k2))
    (ensures prefix_sorted s (vj + 1))

val lemma_triangle_step (vj: nat)
  : Lemma (requires vj >= 1)
          (ensures op_Multiply vj (vj - 1) / 2 + vj == op_Multiply (vj + 1) vj / 2)
