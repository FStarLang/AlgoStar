(*
   Maximum Subarray D&C — Lemmas interface
*)

module CLRS.Ch04.MaxSubarray.DivideConquer.Lemmas
open FStar.Seq
open CLRS.Ch04.MaxSubarray.Spec
open CLRS.Ch04.MaxSubarray.DivideConquer.Spec
module Seq = FStar.Seq

val lemma_dc_sum_correct (s: Seq.seq int) (low high: nat)
  : Lemma
    (requires low <= high /\ high <= Seq.length s)
    (ensures (let (sum, left, right) = find_maximum_subarray_dc s low high in
              low <= left /\ left <= right /\ right <= high /\
              (if left = right then sum == 0 else sum == sum_range s left right)))

val lemma_dc_nonempty (s: Seq.seq int) (low high: nat)
  : Lemma (requires low < high /\ high <= Seq.length s)
          (ensures (let (_, l, r) = find_maximum_subarray_dc s low high in l < r))

val lemma_dc_optimal (s: Seq.seq int) (low high qi qj: nat)
  : Lemma
    (requires low < high /\ high <= Seq.length s /\ low <= qi /\ qi < qj /\ qj <= high)
    (ensures (let (sum, _, _) = find_maximum_subarray_dc s low high in sum >= sum_range s qi qj))

val dc_kadane_equivalence (s: Seq.seq int)
  : Lemma (requires Seq.length s > 0)
          (ensures find_maximum_subarray_sum s == max_subarray_spec s)
