(*
   Maximum Subarray — Shared Specification

   Contains the canonical definitions of kadane_spec, max_subarray_spec,
   sum_range, max_suffix_sum, max_sub_sum, and their correctness proofs.

   Used by both Kadane (Pulse) and DivideConquer (pure) implementations.

   NO admits. NO assumes.
*)

module CLRS.Ch04.MaxSubarray.Spec
open FStar.Seq
module Seq = FStar.Seq

// ========== Common Definitions ==========

let max_int (a b: int) : Tot int = if a >= b then a else b

// A very small integer to use as initial best_sum
let initial_min : int = -1000000000

// ========== Kadane Specification ==========

// Kadane's algorithm specification: iterative maximum subarray
let rec kadane_spec (s: Seq.seq int) (i: nat) 
  (current_sum: int) (best_sum: int) : Pure int
  (requires i <= Seq.length s)
  (ensures fun _ -> True)
  (decreases (if i <= Seq.length s then Seq.length s - i else 0))
  =
  if i >= Seq.length s then best_sum
  else (
    let elem = Seq.index s i in
    let new_current = max_int elem (current_sum + elem) in
    let new_best = max_int best_sum new_current in
    kadane_spec s (i + 1) new_current new_best
  )

// The main spec: maximum subarray sum
let max_subarray_spec (s: Seq.seq int) : Tot int =
  if Seq.length s = 0 then 0
  else kadane_spec s 0 0 initial_min

// ========== Sum Range ==========

// Sum of elements in range [i, j)
let rec sum_range (s: Seq.seq int) (i j: nat) : Pure int
  (requires i <= j /\ j <= Seq.length s)
  (ensures fun _ -> True)
  (decreases Prims.op_Subtraction j i)
  =
  if i >= j then 0
  else Seq.index s i + sum_range s (i + 1) j

// Lemma: sum_range is compositional
let rec lemma_sum_range_append (s: Seq.seq int) (i j k: nat)
  : Lemma
    (requires i <= j /\ j <= k /\ k <= Seq.length s)
    (ensures sum_range s i k == sum_range s i j + sum_range s j k)
    (decreases Prims.op_Subtraction j i)
  =
  if i >= j then ()
  else lemma_sum_range_append s (i + 1) j k

// ========== True Optimality Definitions ==========

// Max non-empty subarray sum ending at position i
let rec max_suffix_sum (s: Seq.seq int) (i: nat) : Pure int
  (requires i < Seq.length s) (ensures fun _ -> True) (decreases i) =
  if i = 0 then Seq.index s 0
  else max_int (Seq.index s i) (max_suffix_sum s (Prims.op_Subtraction i 1) + Seq.index s i)

// Global max non-empty subarray sum in s[0..i+1)
let rec max_sub_sum (s: Seq.seq int) (i: nat) : Pure int
  (requires i < Seq.length s) (ensures fun _ -> True) (decreases i) =
  if i = 0 then Seq.index s 0
  else max_int (max_sub_sum s (Prims.op_Subtraction i 1)) (max_suffix_sum s i)

// Kadane uses initial_min as a sentinel; correctness requires elements >= it
let elements_bounded (s: Seq.seq int) : prop =
  forall (k:nat). k < Seq.length s ==> Seq.index s k >= initial_min

// ========== Optimality Proofs ==========

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
    (requires i <= Seq.length s /\ Seq.length s > 0 /\ elements_bounded s /\
              (i = 0 ==> cur == 0 /\ best == initial_min) /\
              (i > 0 ==> cur == max_suffix_sum s (Prims.op_Subtraction i 1) /\
                         best == max_sub_sum s (Prims.op_Subtraction i 1)))
    (ensures kadane_spec s i cur best == max_sub_sum s (Prims.op_Subtraction (Seq.length s) 1))
    (decreases Prims.op_Subtraction (Seq.length s) i) =
  if i >= Seq.length s then ()
  else lemma_kadane_correct s (i + 1) (max_suffix_sum s i) (max_sub_sum s i)

// Theorem 1: Kadane's result is >= every contiguous subarray sum
let theorem_kadane_optimal (s: Seq.seq int) (i j: nat)
  : Lemma
    (requires Seq.length s > 0 /\ elements_bounded s /\ i < j /\ j <= Seq.length s)
    (ensures max_subarray_spec s >= sum_range s i j) =
  lemma_kadane_correct s 0 0 initial_min;
  lemma_max_sub_ge s (Prims.op_Subtraction (Seq.length s) 1) i j

// Theorem 2: Kadane's result is achieved by some contiguous subarray
let theorem_kadane_witness (s: Seq.seq int)
  : Lemma
    (requires Seq.length s > 0 /\ elements_bounded s)
    (ensures (let n = Seq.length s in
              exists (i j: nat). i < j /\ j <= n /\ max_subarray_spec s == sum_range s i j)) =
  lemma_kadane_correct s 0 0 initial_min;
  let (wi, wj) = max_sub_witness s (Prims.op_Subtraction (Seq.length s) 1) in
  assert (wi < wj /\ wj <= Seq.length s /\ max_subarray_spec s == sum_range s wi wj)
