(*
   Maximum Subarray - Divide and Conquer — Algorithm Specification (CLRS Section 4.1)

   Pure specification of the D&C algorithm:
   - find_max_crossing_subarray: Find max subarray crossing the midpoint
   - find_maximum_subarray_dc: Recursively solve left, right, and crossing cases
   - find_maximum_subarray_sum: Simple wrapper returning just the sum

   NO admits. NO assumes.
*)

module CLRS.Ch04.MaxSubarray.DivideConquer.Spec
open FStar.Seq
open CLRS.Ch04.MaxSubarray.Spec
module Seq = FStar.Seq

// ========== Find Maximum Crossing Subarray ==========

// Find best sum extending left from position i (inclusive) down to low
// Returns (best_sum, best_left_index)
let rec find_max_crossing_left (s: Seq.seq int) (low mid: nat) 
  (i: nat) (current_sum: int) (best_sum: int) (best_idx: nat)
  : Pure (int & nat)
  (requires low <= i /\ i < mid /\ mid <= Seq.length s /\ low <= best_idx /\ best_idx < mid)
  (ensures fun (sum, idx) -> low <= idx /\ idx < mid /\ sum >= best_sum)
  (decreases i)
  =
  let new_sum = current_sum + Seq.index s i in
  let (new_best_sum, new_best_idx) = 
    if new_sum > best_sum then (new_sum, i) else (best_sum, best_idx) in
  if i = low then (new_best_sum, new_best_idx)
  else (
    let i_prev : nat = i - 1 in
    find_max_crossing_left s low mid i_prev new_sum new_best_sum new_best_idx
  )

// Find best sum extending right from position i (inclusive) to high-1
// Returns (best_sum, best_right_index)  
let rec find_max_crossing_right (s: Seq.seq int) (mid high: nat)
  (i: nat) (current_sum: int) (best_sum: int) (best_idx: nat)
  : Pure (int & nat)
  (requires mid <= i /\ i < high /\ high <= Seq.length s /\ mid < best_idx /\ best_idx <= high)
  (ensures fun (sum, idx) -> mid < idx /\ idx <= high /\ sum >= best_sum)
  (decreases high - i)
  =
  let new_sum = current_sum + Seq.index s i in
  let (new_best_sum, new_best_idx) =
    if new_sum > best_sum then (new_sum, i + 1) else (best_sum, best_idx) in
  if i + 1 >= high then (new_best_sum, new_best_idx)
  else find_max_crossing_right s mid high (i + 1) new_sum new_best_sum new_best_idx

// Find maximum subarray crossing mid (combining left and right extensions)
let find_max_crossing_subarray (s: Seq.seq int) (low mid high: nat) 
  : Pure (int & nat & nat)
  (requires low < mid /\ mid < high /\ high <= Seq.length s)
  (ensures fun (sum, left_idx, right_idx) -> 
    low <= left_idx /\ left_idx < mid /\ 
    mid < right_idx /\ right_idx <= high)
  =
  let (left_sum, left_idx) = 
    find_max_crossing_left s low mid (mid - 1) 0 (Seq.index s (mid - 1)) (mid - 1) in
  let (right_sum, right_idx) =
    find_max_crossing_right s mid high mid 0 (Seq.index s mid) (mid + 1) in
  (left_sum + right_sum, left_idx, right_idx)

// ========== Main Divide-and-Conquer Algorithm ==========

// Returns (max_sum, left_index, right_index) where the max subarray is [left, right)
let rec find_maximum_subarray_dc (s: Seq.seq int) (low high: nat) 
  : Pure (int & nat & nat)
  (requires low <= high /\ high <= Seq.length s)
  (ensures fun (sum, left, right) -> low <= left /\ left <= right /\ right <= high)
  (decreases high - low)
  =
  if low >= high then (0, low, low)  // Empty range
  else if low + 1 = high then (Seq.index s low, low, high)  // Single element
  else (
    let mid = low + (high - low) / 2 in
    let (left_sum, left_low, left_high) = find_maximum_subarray_dc s low mid in
    let (right_sum, right_low, right_high) = find_maximum_subarray_dc s mid high in
    let (cross_sum, cross_low, cross_high) = find_max_crossing_subarray s low mid high in
    
    // Return the maximum of the three cases
    if left_sum >= right_sum && left_sum >= cross_sum then
      (left_sum, left_low, left_high)
    else if right_sum >= cross_sum then
      (right_sum, right_low, right_high)
    else
      (cross_sum, cross_low, cross_high)
  )

// Simple interface: just return the sum
let find_maximum_subarray_sum (s: Seq.seq int) : Tot int =
  if Seq.length s = 0 then 0
  else (
    let (sum, _, _) = find_maximum_subarray_dc s 0 (Seq.length s) in
    sum
  )
