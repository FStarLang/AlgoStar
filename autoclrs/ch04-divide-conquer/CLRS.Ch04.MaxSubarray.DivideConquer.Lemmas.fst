(*
   Maximum Subarray D&C — Correctness Lemmas

   Proves:
   - D&C returns a valid subarray sum (lemma_dc_sum_correct)
   - D&C is optimal: result >= every subarray sum (lemma_dc_optimal)
   - D&C result is non-empty for non-empty input (lemma_dc_nonempty)
   - Equivalence with Kadane's algorithm (dc_kadane_equivalence)

   NO admits. NO assumes.
*)

module CLRS.Ch04.MaxSubarray.DivideConquer.Lemmas
open FStar.Seq
open FStar.Math.Lemmas
open CLRS.Ch04.MaxSubarray.Spec
open CLRS.Ch04.MaxSubarray.Lemmas
open CLRS.Ch04.MaxSubarray.DivideConquer.Spec
module Seq = FStar.Seq

// ========== Correctness Properties ==========

// Base case correctness: single element
let lemma_dc_base_case (s: Seq.seq int) (i: nat)
  : Lemma
    (requires i < Seq.length s)
    (ensures (let (sum, low, high) = find_maximum_subarray_dc s i (i + 1) in
              sum == Seq.index s i /\ low == i /\ high == i + 1))
  = ()

// Empty case correctness
let lemma_dc_empty_case (s: Seq.seq int) (i: nat)
  : Lemma
    (requires i <= Seq.length s)
    (ensures (let (sum, low, high) = find_maximum_subarray_dc s i i in
              sum == 0 /\ low == i /\ high == i))
  = ()

// Helper lemma: find_max_crossing_left computes sum correctly
let rec lemma_crossing_left_sum (s: Seq.seq int) (low mid: nat)
  (i: nat) (current_sum: int) (best_sum: int) (best_idx: nat)
  : Lemma
    (requires low <= i /\ i < mid /\ mid <= Seq.length s /\ low <= best_idx /\ best_idx < mid /\
              current_sum == sum_range s (i + 1) mid /\
              best_sum == sum_range s best_idx mid)
    (ensures (let (sum, idx) = find_max_crossing_left s low mid i current_sum best_sum best_idx in
              low <= idx /\ idx < mid /\ sum == sum_range s idx mid))
    (decreases i)
  =
  let new_sum = current_sum + Seq.index s i in
  lemma_sum_range_append s i (i + 1) mid;
  assert (new_sum == sum_range s i mid);
  let (new_best_sum, new_best_idx) = 
    if new_sum > best_sum then (new_sum, i) else (best_sum, best_idx) in
  if i = low then ()
  else (
    let i_prev : nat = i - 1 in
    lemma_crossing_left_sum s low mid i_prev new_sum new_best_sum new_best_idx
  )

// Helper lemma: find_max_crossing_right computes sum correctly
let rec lemma_crossing_right_sum (s: Seq.seq int) (mid high: nat)
  (i: nat) (current_sum: int) (best_sum: int) (best_idx: nat)
  : Lemma
    (requires mid <= i /\ i < high /\ high <= Seq.length s /\ mid < best_idx /\ best_idx <= high /\
              current_sum == sum_range s mid i /\
              best_sum == sum_range s mid best_idx)
    (ensures (let (sum, idx) = find_max_crossing_right s mid high i current_sum best_sum best_idx in
              mid < idx /\ idx <= high /\ sum == sum_range s mid idx))
    (decreases high - i)
  =
  let new_sum = current_sum + Seq.index s i in
  lemma_sum_range_append s mid i (i + 1);
  assert (new_sum == sum_range s mid (i + 1));
  let (new_best_sum, new_best_idx) =
    if new_sum > best_sum then (new_sum, i + 1) else (best_sum, best_idx) in
  if i + 1 >= high then ()
  else lemma_crossing_right_sum s mid high (i + 1) new_sum new_best_sum new_best_idx

// Helper lemma: find_max_crossing_subarray returns correct sum
let lemma_crossing_sum_correct (s: Seq.seq int) (low mid high: nat)
  : Lemma
    (requires low < mid /\ mid < high /\ high <= Seq.length s)
    (ensures (let (sum, left_idx, right_idx) = find_max_crossing_subarray s low mid high in
              low <= left_idx /\ left_idx < mid /\
              mid < right_idx /\ right_idx <= high /\
              sum == sum_range s left_idx right_idx))
  =
  assert (sum_range s mid mid == 0);
  assert (Seq.index s (mid - 1) == sum_range s (mid - 1) mid);
  lemma_crossing_left_sum s low mid (mid - 1) 0 (Seq.index s (mid - 1)) (mid - 1);
  
  assert (sum_range s mid mid == 0);
  assert (Seq.index s mid == sum_range s mid (mid + 1));
  lemma_crossing_right_sum s mid high mid 0 (Seq.index s mid) (mid + 1);
  
  let (left_sum, left_idx) = 
    find_max_crossing_left s low mid (mid - 1) 0 (Seq.index s (mid - 1)) (mid - 1) in
  let (right_sum, right_idx) =
    find_max_crossing_right s mid high mid 0 (Seq.index s mid) (mid + 1) in
  lemma_sum_range_append s left_idx mid right_idx

//SNIPPET_START: dc_sum_correct
// The returned range has the claimed sum
let rec lemma_dc_sum_correct (s: Seq.seq int) (low high: nat)
  : Lemma
    (requires low <= high /\ high <= Seq.length s)
    (ensures (let (sum, left, right) = find_maximum_subarray_dc s low high in
              low <= left /\ left <= right /\ right <= high /\
              (if left = right then sum == 0 else sum == sum_range s left right)))
    (decreases high - low)
//SNIPPET_END: dc_sum_correct
  = 
  if low >= high then ()
  else if low + 1 = high then (
    lemma_sum_range_append s low (low + 1) (low + 1)
  )
  else (
    let mid = low + (high - low) / 2 in
    lemma_dc_sum_correct s low mid;
    lemma_dc_sum_correct s mid high;
    lemma_crossing_sum_correct s low mid high;
    let (left_sum, left_low, left_high) = find_maximum_subarray_dc s low mid in
    let (right_sum, right_low, right_high) = find_maximum_subarray_dc s mid high in
    let (cross_sum, cross_low, cross_high) = find_max_crossing_subarray s low mid high in
    ()
  )

// ========== D&C crossing optimality ==========

let rec lemma_crossing_left_opt (s: Seq.seq int) (low mid i: nat) (cs bs: int) (bi q: nat)
  : Lemma
    (requires low <= i /\ i < mid /\ mid <= Seq.length s /\ low <= bi /\ bi < mid /\
              cs == sum_range s (i + 1) mid /\ bs == sum_range s bi mid /\
              (i < q /\ q < mid ==> bs >= sum_range s q mid) /\ low <= q /\ q < mid)
    (ensures (fst (find_max_crossing_left s low mid i cs bs bi) >= sum_range s q mid))
    (decreases i) =
  lemma_sum_range_append s i (i + 1) mid;
  let ns = cs + Seq.index s i in
  let (nbs, nbi) = if ns > bs then (ns, i) else (bs, bi) in
  if q > i then ()
  else if q = i then ()
  else if i = low then ()
  else lemma_crossing_left_opt s low mid (i - 1) ns nbs nbi q

let rec lemma_crossing_right_opt (s: Seq.seq int) (mid high i: nat) (cs bs: int) (bi q: nat)
  : Lemma
    (requires mid <= i /\ i < high /\ high <= Seq.length s /\ mid < bi /\ bi <= high /\
              cs == sum_range s mid i /\ bs == sum_range s mid bi /\
              (mid < q /\ q <= i ==> bs >= sum_range s mid q) /\ mid < q /\ q <= high)
    (ensures (fst (find_max_crossing_right s mid high i cs bs bi) >= sum_range s mid q))
    (decreases high - i) =
  lemma_sum_range_append s mid i (i + 1);
  let ns = cs + Seq.index s i in
  let (nbs, nbi) = if ns > bs then (ns, i + 1) else (bs, bi) in
  if q <= i then ()
  else if q = i + 1 then ()
  else if i + 1 >= high then ()
  else lemma_crossing_right_opt s mid high (i + 1) ns nbs nbi q

// ========== D&C optimality ==========

let rec lemma_dc_nonempty (s: Seq.seq int) (low high: nat)
  : Lemma (requires low < high /\ high <= Seq.length s)
          (ensures (let (_, l, r) = find_maximum_subarray_dc s low high in l < r))
          (decreases high - low) =
  if low + 1 = high then ()
  else
    let mid = low + (high - low) / 2 in
    lemma_dc_nonempty s low mid;
    lemma_dc_nonempty s mid high

let rec lemma_dc_optimal (s: Seq.seq int) (low high qi qj: nat)
  : Lemma
    (requires low < high /\ high <= Seq.length s /\ low <= qi /\ qi < qj /\ qj <= high)
    (ensures (let (sum, _, _) = find_maximum_subarray_dc s low high in sum >= sum_range s qi qj))
    (decreases high - low) =
  if low + 1 = high then ()
  else
    let mid = low + (high - low) / 2 in
    if qj <= mid then lemma_dc_optimal s low mid qi qj
    else if qi >= mid then lemma_dc_optimal s mid high qi qj
    else (
      lemma_sum_range_append s qi mid qj;
      lemma_crossing_left_opt s low mid (mid - 1) 0 (Seq.index s (mid - 1)) (mid - 1) qi;
      lemma_crossing_right_opt s mid high mid 0 (Seq.index s mid) (mid + 1) qj
    )

// ========== Equivalence with Kadane ==========

//SNIPPET_START: dc_kadane_equivalence
// Proved equivalence: D&C and Kadane compute the same result.
// Both algorithms compute the unique maximum non-empty subarray sum.
let dc_kadane_equivalence (s: Seq.seq int)
  : Lemma (requires Seq.length s > 0 /\ elements_bounded s)
          (ensures find_maximum_subarray_sum s == max_subarray_spec s) =
  let n = Seq.length s in
  lemma_kadane_correct s 0 0 initial_min;
  lemma_dc_sum_correct s 0 n;
  lemma_dc_nonempty s 0 n;
  let (_, l, r) = find_maximum_subarray_dc s 0 n in
  lemma_max_sub_ge s (n - 1) l r;
  let (mj, mk) = max_sub_witness s (n - 1) in
  lemma_dc_optimal s 0 n mj mk
//SNIPPET_END: dc_kadane_equivalence
