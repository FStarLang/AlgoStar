(*
   Maximum Subarray D&C — Complexity interface
*)

module CLRS.Ch04.MaxSubarray.DivideConquer.Complexity

val dc_ops_count (n: nat) : Tot nat

val log2_ceil (n: pos) : Tot nat

val lemma_dc_complexity_bound (n: pos)
  : Lemma (ensures dc_ops_count n <= op_Star 4 (op_Star n (log2_ceil n + 1)))
