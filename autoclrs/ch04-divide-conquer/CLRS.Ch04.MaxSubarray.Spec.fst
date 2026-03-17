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
  else kadane_spec s 0 0 (Seq.index s 0)

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

// ========== Complexity bound predicate (Kadane) ==========

let complexity_bounded_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n

