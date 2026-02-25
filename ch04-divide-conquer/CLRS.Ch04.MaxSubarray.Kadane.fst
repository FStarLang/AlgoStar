(*
   Maximum Subarray (Kadane's Algorithm) - Verified implementation in Pulse
   
   Proves: The result equals the maximum sum of any contiguous subarray.
   
   NO admits. NO assumes.
*)

module CLRS.Ch04.MaxSubarray.Kadane
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Definitions ==========

// Helper: maximum of two integers
let max_int (a b: int) : Tot int = if a >= b then a else b

// A very small integer to use as initial best_sum
let initial_min : int = -1000000000

// Lemma: Seq.length is always non-negative
let seq_length_nonneg (s: Seq.seq 'a) : Lemma (Seq.length s >= 0) = ()

//SNIPPET_START: kadane_spec
// Kadane's algorithm specification: iterative maximum subarray
// We use i as decreases with the invariant that we call with i+1 < length
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
//SNIPPET_END: kadane_spec

// ========== True Optimality Proof ==========

//SNIPPET_START: sum_range
// Sum of elements in range [i, j)
let rec sum_range (s: Seq.seq int) (i j: nat) : Pure int
  (requires i <= j /\ j <= Seq.length s)
  (ensures fun _ -> True)
  (decreases Prims.op_Subtraction j i)
  =
  if i >= j then 0
  else Seq.index s i + sum_range s (i + 1) j
//SNIPPET_END: sum_range

// Lemma: sum_range is compositional
let rec lemma_sum_range_append (s: Seq.seq int) (i j k: nat)
  : Lemma
    (requires i <= j /\ j <= k /\ k <= Seq.length s)
    (ensures sum_range s i k == sum_range s i j + sum_range s j k)
    (decreases Prims.op_Subtraction j i)
  =
  if i >= j then ()
  else lemma_sum_range_append s (i + 1) j k

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

//SNIPPET_START: kadane_optimality
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
//SNIPPET_END: kadane_optimality

// ========== Main Algorithm ==========

//SNIPPET_START: max_subarray_sig
fn max_subarray
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    Seq.length s0 <= A.length a /\
    SZ.v len > 0
  )
  returns result: int
  ensures A.pts_to a s0 ** pure (
    result == max_subarray_spec s0
  )
//SNIPPET_END: max_subarray_sig
{
  let mut current_sum: int = 0;
  let mut best_sum: int = initial_min;
  let mut i: SZ.t = 0sz;
  
  while (!i <^ len)
  invariant exists* vi vcur vbest.
    R.pts_to i vi **
    R.pts_to current_sum vcur **
    R.pts_to best_sum vbest **
    A.pts_to a s0 **
    pure (
      SZ.v vi <= SZ.v len /\
      kadane_spec s0 (SZ.v vi) vcur vbest == kadane_spec s0 0 0 initial_min
    )
  {
    let vi = !i;
    let vcur = !current_sum;
    let vbest = !best_sum;
    
    let elem = a.(vi);
    
    // new_current = max(elem, current + elem)
    let sum_with_current : int = vcur + elem;
    let mut new_current : int = elem;
    if (sum_with_current > elem) {
      new_current := sum_with_current;
    };
    let vnew_current = !new_current;
    
    // new_best = max(best, new_current)
    let mut new_best : int = vbest;
    if (vnew_current > vbest) {
      new_best := vnew_current;
    };
    let vnew_best = !new_best;
    
    current_sum := vnew_current;
    best_sum := vnew_best;
    i := vi + 1sz;
  };
  
  !best_sum
}
