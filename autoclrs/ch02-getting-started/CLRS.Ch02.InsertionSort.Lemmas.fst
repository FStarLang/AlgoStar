(*
   Insertion Sort - Lemma proofs

   Proves:
   - lemma_prefix_le_key: prefix elements are <= key
   - lemma_combine_sorted_regions: combine sorted prefix with key and shifted suffix
   - lemma_triangle_step: vj*(vj-1)/2 + vj = (vj+1)*vj/2
*)
module CLRS.Ch02.InsertionSort.Lemmas

open CLRS.Common.SortSpec
open Pulse.Lib.BoundedIntegers
module Seq = FStar.Seq

let lemma_prefix_le_key
  (s s_outer: Seq.seq int) (vi vj: nat) (key: int)
  = if vi = 0 then ()
    else
      let pred = vi - 1 in
      assert (pred + 1 == vi);
      assert (Seq.index s_outer pred <= key);
      assert (forall (k: nat). k < vi ==> k <= pred);
      assert (forall (k: nat). k <= pred /\ pred < vj ==> Seq.index s_outer k <= Seq.index s_outer pred);
      ()

let lemma_combine_sorted_regions
  (s: Seq.seq int) (vi vj: nat) (key: int)
  = ()

let lemma_triangle_step (vj: nat)
  = assert (op_Multiply vj (vj - 1) + op_Multiply 2 vj == op_Multiply vj (vj + 1))
