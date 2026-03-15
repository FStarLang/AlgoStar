(*
   Maximum Subarray — Lemmas about the pure specification

   Proves correctness and optimality of the Kadane specification:
   - lemma_kadane_correct: kadane_spec tracks max_suffix_sum / max_sub_sum
   - theorem_kadane_optimal: result >= every contiguous subarray sum
   - theorem_kadane_witness: result equals some contiguous subarray sum

   NO admits. NO assumes.
*)

module CLRS.Ch04.MaxSubarray.Lemmas
open FStar.Seq
open CLRS.Ch04.MaxSubarray.Spec
module Seq = FStar.Seq

// max_suffix_sum i >= sum_range s j (i+1) for any j <= i
let rec lemma_max_suffix_ge (s: Seq.seq int) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j <= i)
          (ensures max_suffix_sum s i >= sum_range s j (i + 1))
          (decreases i) =
  if j = i then ()
  else (
    lemma_sum_range_append s j i (i + 1);
    lemma_max_suffix_ge s (Prims.op_Subtraction i 1) j
  )

// Witness: max_suffix_sum equals some sum_range
let rec max_suffix_witness (s: Seq.seq int) (i: nat) : Pure nat
  (requires i < Seq.length s)
  (ensures fun j -> j <= i /\ max_suffix_sum s i == sum_range s j (i + 1))
  (decreases i) =
  if i = 0 then 0
  else
    let pj = max_suffix_witness s (Prims.op_Subtraction i 1) in
    if Seq.index s i >= max_suffix_sum s (Prims.op_Subtraction i 1) + Seq.index s i then i
    else (lemma_sum_range_append s pj i (i + 1); pj)

// max_sub_sum i >= any subarray sum in [0, i+1)
let rec lemma_max_sub_ge (s: Seq.seq int) (i j k: nat)
  : Lemma (requires i < Seq.length s /\ j < k /\ k <= i + 1)
          (ensures max_sub_sum s i >= sum_range s j k)
          (decreases i) =
  if Prims.op_Subtraction k 1 = i then lemma_max_suffix_ge s i j
  else lemma_max_sub_ge s (Prims.op_Subtraction i 1) j k

// Witness: max_sub_sum equals some sum_range
let rec max_sub_witness (s: Seq.seq int) (i: nat) : Pure (nat & nat)
  (requires i < Seq.length s)
  (ensures fun (j, k) -> j < k /\ k <= i + 1 /\ max_sub_sum s i == sum_range s j k)
  (decreases i) =
  if i = 0 then (0, 1)
  else
    let (pj, pk) = max_sub_witness s (Prims.op_Subtraction i 1) in
    if max_sub_sum s (Prims.op_Subtraction i 1) >= max_suffix_sum s i then (pj, pk)
    else let sj = max_suffix_witness s i in (sj, i + 1)

// Core: kadane_spec tracks max_suffix_sum and max_sub_sum
let rec lemma_kadane_correct (s: Seq.seq int) (i: nat) (cur best: int)
  : Lemma
    (requires i <= Seq.length s /\ Seq.length s > 0 /\
              (i = 0 ==> cur == 0 /\ best == Seq.index s 0) /\
              (i > 0 ==> cur == max_suffix_sum s (Prims.op_Subtraction i 1) /\
                         best == max_sub_sum s (Prims.op_Subtraction i 1)))
    (ensures kadane_spec s i cur best == max_sub_sum s (Prims.op_Subtraction (Seq.length s) 1))
    (decreases Prims.op_Subtraction (Seq.length s) i) =
  if i >= Seq.length s then ()
  else lemma_kadane_correct s (i + 1) (max_suffix_sum s i) (max_sub_sum s i)

// Theorem 1: Kadane's result is >= every contiguous subarray sum
let theorem_kadane_optimal (s: Seq.seq int) (i j: nat)
  : Lemma
    (requires Seq.length s > 0 /\ i < j /\ j <= Seq.length s)
    (ensures max_subarray_spec s >= sum_range s i j) =
  lemma_kadane_correct s 0 0 (Seq.index s 0);
  lemma_max_sub_ge s (Prims.op_Subtraction (Seq.length s) 1) i j

// Theorem 2: Kadane's result is achieved by some contiguous subarray
let theorem_kadane_witness (s: Seq.seq int)
  : Lemma
    (requires Seq.length s > 0)
    (ensures (let n = Seq.length s in
              exists (i j: nat). i < j /\ j <= n /\ max_subarray_spec s == sum_range s i j)) =
  lemma_kadane_correct s 0 0 (Seq.index s 0);
  let (wi, wj) = max_sub_witness s (Prims.op_Subtraction (Seq.length s) 1) in
  assert (wi < wj /\ wj <= Seq.length s /\ max_subarray_spec s == sum_range s wi wj)
