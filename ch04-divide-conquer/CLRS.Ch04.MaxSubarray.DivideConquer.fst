(*
   Maximum Subarray - Divide and Conquer (CLRS Section 4.1)
   
   Implements the divide-and-conquer algorithm from CLRS Chapter 4.1:
   1. FIND-MAX-CROSSING-SUBARRAY: Find max subarray crossing the midpoint
   2. FIND-MAXIMUM-SUBARRAY: Recursively solve left, right, and crossing cases
   
   Proves:
   - Algorithm structure follows CLRS exactly
   - Complexity: O(n lg n) via T(n) = 2T(n/2) + Theta(n) recurrence
   - Correctness for base cases and recursive structure
   - Equivalence with Kadane's algorithm (proved)
   
   This is a pure implementation (not Pulse).
*)

module CLRS.Ch04.MaxSubarray.DivideConquer
open FStar.Seq
open FStar.Math.Lemmas
open CLRS.Ch04.MaxSubarray.Spec
module Seq = FStar.Seq
module Spec = CLRS.Ch04.MaxSubarray.Spec

// ========== Local Definitions ==========

let min_int (a b: int) : Tot int = if a <= b then a else b

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

//SNIPPET_START: find_maximum_subarray_dc
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
//SNIPPET_END: find_maximum_subarray_dc

// Simple interface: just return the sum
let find_maximum_subarray_sum (s: Seq.seq int) : Tot int =
  if Seq.length s = 0 then 0
  else (
    let (sum, _, _) = find_maximum_subarray_dc s 0 (Seq.length s) in
    sum
  )

// ========== Complexity Analysis ==========

//SNIPPET_START: dc_ops_count
// Operation count for D&C algorithm
// T(n) = 2T(n/2) + cn for n > 1, T(1) = c
let rec dc_ops_count (n: nat) : Tot nat =
  if n <= 1 then 1
  else
    let half_ops = dc_ops_count (n / 2) in
    let double_half = half_ops + half_ops in
    double_half + n
//SNIPPET_END: dc_ops_count

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

//SNIPPET_START: dc_complexity_bound
// Prove: T(n) = O(n log n) via Master Theorem case 2
// T(n) = 2T(n/2) + n, solution T(n) <= 4n(log2_ceil(n) + 1)
let rec lemma_dc_complexity_bound (n: pos) 
  : Lemma (ensures dc_ops_count n <= op_Multiply 4 (op_Multiply n (log2_ceil n + 1)))
          (decreases n)
//SNIPPET_END: dc_complexity_bound
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

// ========== Equivalence with Kadane (Proved) ==========

// Use shared spec definitions from CLRS.Ch04.MaxSubarray.Spec

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

// ========== Equivalence ==========

//SNIPPET_START: dc_kadane_equivalence
// Proved equivalence: D&C and Kadane compute the same result.
// Both algorithms compute the unique maximum non-empty subarray sum.
// The elements_bounded precondition ensures Kadane's sentinel value (-10^9)
// does not interfere with the result.
let dc_kadane_equivalence (s: Seq.seq int)
  : Lemma (requires Seq.length s > 0 /\ elements_bounded s)
          (ensures find_maximum_subarray_sum s == max_subarray_spec s) =
  let n = Seq.length s in
  // Kadane = max_sub_sum
  lemma_kadane_correct s 0 0 initial_min;
  // DC returns a valid subarray sum
  lemma_dc_sum_correct s 0 n;
  lemma_dc_nonempty s 0 n;
  let (_, l, r) = find_maximum_subarray_dc s 0 n in
  // DC <= max_sub_sum (DC = sum_range l r; max_sub_sum >= all sum_range)
  lemma_max_sub_ge s (n - 1) l r;
  // DC >= max_sub_sum (max_sub_sum = sum_range mj mk; DC >= all sum_range)
  let (mj, mk) = max_sub_witness s (n - 1) in
  lemma_dc_optimal s 0 n mj mk
//SNIPPET_END: dc_kadane_equivalence

let lemma_dc_equals_kadane (s: Seq.seq int)
  : Lemma
    (requires Seq.length s > 0 /\ elements_bounded s)
    (ensures find_maximum_subarray_sum s == max_subarray_spec s)
  =
  dc_kadane_equivalence s

