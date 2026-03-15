(*
   Maximum Subarray — Lemmas interface
*)

module CLRS.Ch04.MaxSubarray.Lemmas
open FStar.Seq
open CLRS.Ch04.MaxSubarray.Spec
module Seq = FStar.Seq

val lemma_max_suffix_ge (s: Seq.seq int) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j <= i)
          (ensures max_suffix_sum s i >= sum_range s j (i + 1))

val max_suffix_witness (s: Seq.seq int) (i: nat) : Pure nat
  (requires i < Seq.length s)
  (ensures fun j -> j <= i /\ max_suffix_sum s i == sum_range s j (i + 1))

val lemma_max_sub_ge (s: Seq.seq int) (i j k: nat)
  : Lemma (requires i < Seq.length s /\ j < k /\ k <= i + 1)
          (ensures max_sub_sum s i >= sum_range s j k)

val max_sub_witness (s: Seq.seq int) (i: nat) : Pure (nat & nat)
  (requires i < Seq.length s)
  (ensures fun (j, k) -> j < k /\ k <= i + 1 /\ max_sub_sum s i == sum_range s j k)

val lemma_kadane_correct (s: Seq.seq int) (i: nat) (cur best: int)
  : Lemma
    (requires i <= Seq.length s /\ Seq.length s > 0 /\
              (i = 0 ==> cur == 0 /\ best == Seq.index s 0) /\
              (i > 0 ==> cur == max_suffix_sum s (Prims.op_Subtraction i 1) /\
                         best == max_sub_sum s (Prims.op_Subtraction i 1)))
    (ensures kadane_spec s i cur best == max_sub_sum s (Prims.op_Subtraction (Seq.length s) 1))

val theorem_kadane_optimal (s: Seq.seq int) (i j: nat)
  : Lemma
    (requires Seq.length s > 0 /\ i < j /\ j <= Seq.length s)
    (ensures max_subarray_spec s >= sum_range s i j)

val theorem_kadane_witness (s: Seq.seq int)
  : Lemma
    (requires Seq.length s > 0)
    (ensures (let n = Seq.length s in
              exists (i j: nat). i < j /\ j <= n /\ max_subarray_spec s == sum_range s i j))
