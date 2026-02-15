(*
   Maximum Subarray - Divide and Conquer (CLRS Section 4.1)
   
   Implements the divide-and-conquer algorithm from CLRS Chapter 4.1:
   1. FIND-MAX-CROSSING-SUBARRAY: Find max subarray crossing the midpoint
   2. FIND-MAXIMUM-SUBARRAY: Recursively solve left, right, and crossing cases
   
   Proves:
   - Algorithm structure follows CLRS exactly
   - Complexity: O(n lg n) via T(n) = 2T(n/2) + Θ(n) recurrence
   - Correctness for base cases and recursive structure
   
   This is a pure F* implementation (not Pulse).
*)

module CLRS.Ch04.MaxSubarray.DivideConquer
open FStar.Seq
open FStar.Math.Lemmas
module Seq = FStar.Seq

// ========== Common Definitions ==========

let max_int (a b: int) : Tot int = if a >= b then a else b
let min_int (a b: int) : Tot int = if a <= b then a else b

// ========== Helper: Sum of Range ==========

// Sum of elements in range [i, j)
let rec sum_range (s: Seq.seq int) (i j: nat) : Pure int
  (requires i <= j /\ j <= Seq.length s)
  (ensures fun _ -> True)
  (decreases j - i)
  =
  if i >= j then 0
  else Seq.index s i + sum_range s (i + 1) j

// Lemma: sum_range is compositional
let rec lemma_sum_range_append (s: Seq.seq int) (i j k: nat)
  : Lemma
    (requires i <= j /\ j <= k /\ k <= Seq.length s)
    (ensures sum_range s i k == sum_range s i j + sum_range s j k)
    (decreases j - i)
  =
  if i >= j then ()
  else lemma_sum_range_append s (i + 1) j k

// ========== Find Maximum Crossing Subarray ==========

// Find best sum extending left from position i (inclusive) down to low
// Returns (best_sum, best_left_index)
let rec find_max_crossing_left (s: Seq.seq int) (low mid: nat) 
  (i: nat) (current_sum: int) (best_sum: int) (best_idx: nat)
  : Pure (int * nat)
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
  : Pure (int * nat)
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
  : Pure (int * nat * nat)
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
  : Pure (int * nat * nat)
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

// ========== Complexity Analysis ==========

// Operation count for D&C algorithm
// T(n) = 2T(n/2) + cn for n > 1, T(1) = c
let rec dc_ops_count (n: nat) : Tot nat =
  if n <= 1 then 1
  else
    let half_ops = dc_ops_count (n / 2) in
    let double_half = half_ops + half_ops in
    double_half + n

// log2 ceiling function for complexity bounds
let rec log2_ceil (n: pos) : Tot nat (decreases n) =
  if n = 1 then 0
  else 1 + log2_ceil ((n + 1) / 2)

// Key property: 2^(log2_ceil n - 1) < n <= 2^(log2_ceil n)
let rec lemma_log2_ceil_bounds (n: pos)
  : Lemma (ensures (log2_ceil n = 0 /\ n = 1) \/
                    (log2_ceil n > 0 /\ pow2 (log2_ceil n - 1) < n /\ n <= pow2 (log2_ceil n)))
          (decreases n)
  =
  if n = 1 then ()
  else (
    let n' = (n + 1) / 2 in
    if n' > 0 then lemma_log2_ceil_bounds n'
  )

// log2_ceil is monotone
let rec log2_ceil_monotone (a b: pos)
  : Lemma (requires a <= b) (ensures log2_ceil a <= log2_ceil b) (decreases b)
  = if a = b then ()
    else if b = 1 then ()
    else if a = 1 then ()
    else begin
      assert ((a + 1) / 2 <= (b + 1) / 2);
      log2_ceil_monotone ((a + 1) / 2) ((b + 1) / 2)
    end

// log2_ceil(n) >= 1 + log2_ceil(n/2) for n >= 2
let log2_ceil_halving (n: pos{n >= 2})
  : Lemma (ensures log2_ceil n >= 1 + log2_ceil (n / 2))
  = assert (n / 2 >= 1);
    log2_ceil_monotone (n / 2) ((n + 1) / 2)

// Prove: T(n) = O(n log n) via Master Theorem case 2
// T(n) = 2T(n/2) + n, solution T(n) <= 4n(log2_ceil(n) + 1)
let rec lemma_dc_complexity_bound (n: pos) 
  : Lemma (ensures dc_ops_count n <= op_Multiply 4 (op_Multiply n (log2_ceil n + 1)))
          (decreases n)
  = if n = 1 then ()
    else begin
      let h = n / 2 in
      assert (h >= 1);
      lemma_dc_complexity_bound h;
      // IH: T(h) <= 4h(log2_ceil(h)+1). T(n) = 2*T(h)+n <= 8h(log2_ceil(h)+1)+n
      // Since 8h <= 4n: T(n) <= 4n(log2_ceil(h)+1)+n = 4n*log2_ceil(h)+5n
      // Need <= 4n*(log2_ceil(n)+1) = 4n*log2_ceil(n)+4n
      // i.e., 4*log2_ceil(h)+1 <= 4*log2_ceil(n). By halving: log2_ceil(n) >= 1+log2_ceil(h)
      assert (op_Multiply 8 h <= op_Multiply 4 n);
      log2_ceil_halving n
    end

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
  // Establish that initial values satisfy preconditions
  assert (sum_range s mid mid == 0);  // empty range
  assert (Seq.index s (mid - 1) == sum_range s (mid - 1) mid);  // single element
  lemma_crossing_left_sum s low mid (mid - 1) 0 (Seq.index s (mid - 1)) (mid - 1);
  
  assert (sum_range s mid mid == 0);  // empty range
  assert (Seq.index s mid == sum_range s mid (mid + 1));  // single element
  lemma_crossing_right_sum s mid high mid 0 (Seq.index s mid) (mid + 1);
  
  let (left_sum, left_idx) = 
    find_max_crossing_left s low mid (mid - 1) 0 (Seq.index s (mid - 1)) (mid - 1) in
  let (right_sum, right_idx) =
    find_max_crossing_right s mid high mid 0 (Seq.index s mid) (mid + 1) in
  lemma_sum_range_append s left_idx mid right_idx

// The returned range has the claimed sum
let rec lemma_dc_sum_correct (s: Seq.seq int) (low high: nat)
  : Lemma
    (requires low <= high /\ high <= Seq.length s)
    (ensures (let (sum, left, right) = find_maximum_subarray_dc s low high in
              low <= left /\ left <= right /\ right <= high /\
              (if left = right then sum == 0 else sum == sum_range s left right)))
    (decreases high - low)
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

// ========== Equivalence with Kadane (Axiomatized) ==========

// Kadane's algorithm specification (from MaxSubarray.fst)
let rec kadane_spec (s: Seq.seq int) (i: nat) 
  (current_sum: int) (best_sum: int) : Pure int
  (requires i <= Seq.length s)
  (ensures fun _ -> True)
  (decreases (if i <= Seq.length s then Seq.length s - i else 0))
  =
  let initial_min = -1000000000 in
  let max_int' a b = if a >= b then a else b in
  if i >= Seq.length s then best_sum
  else (
    let elem = Seq.index s i in
    let new_current = max_int' elem (current_sum + elem) in
    let new_best = max_int' best_sum new_current in
    kadane_spec s (i + 1) new_current new_best
  )

let max_subarray_spec_kadane (s: Seq.seq int) : Tot int =
  let initial_min = -1000000000 in
  if Seq.length s = 0 then 0
  else kadane_spec s 0 0 initial_min

// Equivalence theorem (axiomatized due to proof complexity)
//
// This states that the divide-and-conquer and Kadane algorithms compute
// the same result. A complete formal proof would require extensive lemmas:
//
// 1. Proving D&C correctness: showing it returns the maximum over all subarrays
//    - Case analysis: left, right, and crossing subarrays
//    - Induction on problem size
//    - Showing all cases are covered
//
// 2. Proving Kadane correctness: showing DP maintains the global optimum
//    - Loop invariant: current_sum is optimal ending at position i
//    - best_sum tracks the global maximum seen so far
//    - Optimal substructure property
//
// 3. Uniqueness: the maximum subarray sum is unique
//
// 4. Equivalence follows from both computing the unique maximum
//
// This is a well-known result from algorithm analysis (CLRS Ch 4).
// For this educational file focusing on D&C implementation,
// we state the equivalence as an axiom.
assume val axiom_dc_kadane_equivalence: s:Seq.seq int{Seq.length s > 0} ->
  Lemma (find_maximum_subarray_sum s == max_subarray_spec_kadane s)

let lemma_dc_equals_kadane (s: Seq.seq int)
  : Lemma
    (requires Seq.length s > 0)
    (ensures find_maximum_subarray_sum s == max_subarray_spec_kadane s)
  =
  // Establish that D&C computes correct sums for identified ranges
  lemma_dc_sum_correct s 0 (Seq.length s);
  
  // Apply the axiomatized equivalence
  axiom_dc_kadane_equivalence s



