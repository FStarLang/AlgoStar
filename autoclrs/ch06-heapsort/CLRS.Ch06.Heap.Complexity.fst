module CLRS.Ch06.Heap.Complexity

/// Complexity analysis for HEAPSORT algorithm from CLRS Chapter 6
/// This module provides complexity proofs following CLRS Theorems 6.3–6.4:
///
/// - BUILD-MAX-HEAP: O(n) [Theorem 6.3], proved as ≤ 4n operations
/// - HEAPSORT: O(n log n) with constant 6, i.e., ≤ 6n(1 + ⌊log₂ n⌋)
/// - Tighter practical bound: ≤ 2n·log₂n + 4n
/// - Heapsort beats quadratic sorting for n ≥ 11

open FStar.Mul
open FStar.Math.Lemmas

/// Floor of logarithm base 2 (used throughout CLRS Chapter 6 complexity analysis)
let rec log2_floor (n: pos) : nat =
  if n = 1 then 0 else 1 + log2_floor (n / 2)

/// Height of a node at index i in a heap of size n (CLRS §6.1)
/// Height is the number of edges on the longest path from node to a leaf
let height_at_index (i: pos) (n: pos{i <= n}) : nat =
  log2_floor (n / i)

/// MAX-HEAPIFY operations count: at most 2 * height (CLRS §6.2, Theorem 6.2)
/// (2 comparisons per level: find max of {parent, left, right})
let max_heapify_ops (height: nat) : nat =
  2 * height

/// BUILD-MAX-HEAP operations count (CLRS §6.3, Theorem 6.3)
/// Sum over all nodes of max_heapify_ops for their height
/// We model this by summing over heights: nodes_at_height h * max_heapify_ops h
let rec sum_from_to (f: nat -> nat) (i: nat) (j: nat) 
  : Tot nat (decreases (if i > j then 0 else j - i + 1))
  = if i > j then 0
    else f i + sum_from_to f (i + 1) j

/// Count of nodes at height h in a heap of size n (CLRS §6.3, Exercise 6.3-3)
/// A heap of size n has at most ceil(n / 2^(h+1)) nodes at height h
let nodes_at_height (n: pos) (h: nat) : nat =
  (n + (pow2 (h + 1)) - 1) / (pow2 (h + 1))

/// BUILD-MAX-HEAP operations: sum over heights
let build_heap_ops (n: pos) : nat =
  let max_height = log2_floor n in
  sum_from_to (fun h -> nodes_at_height n h * max_heapify_ops h) 0 max_height

/// Extract-max loop operations (CLRS §6.4): (n-1) calls to MAX-HEAPIFY on decreasing sizes
let rec extract_max_ops (n: nat) : nat =
  if n <= 1 then 0
  else max_heapify_ops (log2_floor n) + extract_max_ops (n - 1)

/// HEAPSORT total operations (CLRS §6.4)
let heapsort_ops (n: pos) : nat =
  build_heap_ops n + extract_max_ops n

/// ========================================================================
/// Lemmas about log2_floor
/// ========================================================================

let rec log2_floor_bound (n: pos)
  : Lemma (ensures log2_floor n < n)
          (decreases n)
  = if n = 1 then () else log2_floor_bound (n / 2)

let rec log2_floor_monotonic (m n: pos)
  : Lemma (requires m <= n)
          (ensures log2_floor m <= log2_floor n)
          (decreases n)
  = if m = n then ()
    else if n = 1 then ()
    else if m = 1 then ()
    else begin
      log2_floor_monotonic (m / 2) (n / 2);
      ()
    end

/// log2_floor of n/2 is one less than log2_floor n for n > 1
let rec log2_floor_half (n: pos)
  : Lemma (requires n > 1)
          (ensures log2_floor (n / 2) = log2_floor n - 1)
          (decreases n)
  = if n = 2 then ()
    else if n = 3 then ()
    else log2_floor_half (n / 2)

/// Tight bound: log2_floor n <= n - 1
let rec log2_floor_tight (n: pos)
  : Lemma (ensures log2_floor n <= n - 1)
          (decreases n)
  = if n = 1 then ()
    else log2_floor_tight (n / 2)

let log2_floor_positive (n: pos{n > 1})
  : Lemma (ensures log2_floor n > 0)
  = ()

/// log2_floor of 2^k is exactly k
let rec log2_floor_pow2 (k: nat)
  : Lemma (ensures log2_floor (pow2 k) = k)
          (decreases k)
  = if k = 0 then ()
    else begin
      pow2_double_sum k;
      log2_floor_pow2 (k - 1)
    end

/// log2_floor(n) <= k iff n < 2^(k+1)
let rec log2_floor_upper_bound (n: pos) (k: nat)
  : Lemma (requires log2_floor n <= k)
          (ensures n < pow2 (k + 1))
          (decreases n)
  = if n = 1 then ()
    else if k = 0 then ()
    else begin
      log2_floor_upper_bound (n / 2) (k - 1);
      pow2_double_sum k;
      ()
    end

/// pow2 (log2_floor n) <= n (follows from definition)
let rec log2_floor_lower_bound (n: pos)
  : Lemma (ensures pow2 (log2_floor n) <= n)
          (decreases n)
  = if n = 1 then ()
    else begin
      log2_floor_lower_bound (n / 2);
      pow2_double_sum (log2_floor (n / 2));
      // log2_floor n = 1 + log2_floor (n / 2)
      // pow2 (log2_floor n) = pow2 (1 + log2_floor (n/2))
      //                     = 2 * pow2 (log2_floor (n/2))
      // By IH: pow2 (log2_floor (n/2)) <= n/2
      // So: 2 * pow2 (log2_floor (n/2)) <= 2 * (n/2) <= n
      ()
    end

/// ========================================================================
/// Lemmas about BUILD-MAX-HEAP complexity (CLRS Theorem 6.3)
/// ========================================================================

/// Weighted power-of-2 sum: sum_{h=start}^{max_h} h * 2^{max_h - h}
let rec weighted_pow2_sum (h max_h: nat)
  : Tot nat (decreases (if h > max_h then 0 else max_h - h + 1))
  = if h > max_h then 0
    else h * pow2 (max_h - h) + weighted_pow2_sum (h + 1) max_h

/// Recurrence: S(H) = 2 * S(H-1) + H
let rec factor_two_lemma (h max_h: nat)
  : Lemma (requires h <= max_h /\ max_h > 0)
          (ensures weighted_pow2_sum h max_h = 2 * weighted_pow2_sum h (max_h - 1) + max_h)
          (decreases (max_h - h))
  = if h = max_h then ()
    else begin factor_two_lemma (h + 1) max_h; assert (pow2 (max_h - h) = 2 * pow2 (max_h - 1 - h)) end

/// Exact formula: sum_{h=0}^{H} h * 2^{H-h} = 2^{H+1} - H - 2
let rec weighted_pow2_sum_exact (max_h: nat)
  : Lemma (ensures weighted_pow2_sum 0 max_h = pow2 (max_h + 1) - (max_h + 2))
          (decreases max_h)
  = if max_h = 0 then () else begin weighted_pow2_sum_exact (max_h - 1); factor_two_lemma 0 max_h; assert (pow2 (max_h + 1) = 2 * pow2 max_h) end

private let cancel_mul_div (a: nat) (b: pos) : Lemma ((a * b) / b = a) = lemma_div_plus 0 a b

private let floor_mul_le (a: nat) (b: pos) (c: nat) : Lemma ((a / b) * c <= a * c / b) =
  lemma_div_mod a b; lemma_div_plus ((a % b) * c) ((a / b) * c) b

#push-options "--z3rlimit 10 --split_queries always"

/// Scaling: pow2(H) * sum floor(n*h/2^h) <= n * weighted_pow2_sum(0,H)
private let rec scaled_floor_sum_bound (n: pos) (h max_h: nat)
  : Lemma (requires h <= max_h + 1)
          (ensures pow2 max_h * sum_from_to (fun i -> n * i / pow2 i) h max_h <= n * weighted_pow2_sum h max_h)
          (decreases (if h > max_h then 0 else max_h - h + 1))
  = if h > max_h then ()
    else begin
      scaled_floor_sum_bound n (h + 1) max_h;
      floor_mul_le (n * h) (pow2 h) (pow2 max_h);
      pow2_plus h (max_h - h);
      cancel_mul_div (n * h * pow2 (max_h - h)) (pow2 h)
    end

/// Core bound: sum floor(n*h/2^h) < 2n (geometric series convergence)
private let floor_sum_lt_2n (n: pos) (max_h: nat)
  : Lemma (ensures sum_from_to (fun i -> n * i / pow2 i) 0 max_h < 2 * n)
  = scaled_floor_sum_bound n 0 max_h;
    weighted_pow2_sum_exact max_h;
    assert (pow2 max_h * sum_from_to (fun i -> n * i / pow2 i) 0 max_h < 2 * n * pow2 max_h)

private let cancel_2_div (a: nat) (b: pos) : Lemma ((2 * a) / (2 * b) = a / b) =
  lemma_div_mod a b;
  let q = a / b in let r = a % b in
  assert (2 * a = (2 * b) * q + 2 * r /\ 0 <= 2 * r /\ 2 * r < 2 * b);
  lemma_div_plus (2 * r) q (2 * b)

private let ceil_bound_1 (a: nat) (b: pos) : Lemma ((a + b - 1) / b <= a / b + 1) =
  lemma_div_le (a + b - 1) (a + b) b

/// Each term: ceil(n/2^{h+1}) * 2h <= n*h/2^h + 2h
private let ceil_term_bound (n: pos) (h: nat)
  : Lemma (ensures nodes_at_height n h * max_heapify_ops h <= n * h / pow2 h + max_heapify_ops h)
  = ceil_bound_1 n (pow2 (h + 1));
    floor_mul_le n (pow2 (h + 1)) (max_heapify_ops h);
    assert (pow2 (h + 1) = 2 * pow2 h);
    assert (n * (2 * h) = 2 * (n * h));
    cancel_2_div (n * h) (pow2 h)

/// Decompose: sum ceil(...)*2h <= sum floor_part + sum correction
private let rec sum_bound_decomp (n: pos) (h max_h: nat)
  : Lemma (requires h <= max_h + 1)
          (ensures sum_from_to (fun i -> nodes_at_height n i * max_heapify_ops i) h max_h
                   <= sum_from_to (fun i -> n * i / pow2 i) h max_h
                    + sum_from_to (fun i -> max_heapify_ops i) h max_h)
          (decreases (if h > max_h then 0 else max_h - h + 1))
  = if h > max_h then () else begin sum_bound_decomp n (h + 1) max_h; ceil_term_bound n h end

/// Split sum: sum f 0 max_h = sum f 0 (max_h-1) + f(max_h)
private let rec sum_split_last_from (f: nat -> nat) (start: nat) (max_h: nat{max_h >= start /\ max_h > 0})
  : Lemma (ensures sum_from_to f start max_h = sum_from_to f start (max_h - 1) + f max_h)
          (decreases (max_h - start))
  = if start = max_h then ()
    else if start = max_h - 1 then ()
    else sum_split_last_from f (start + 1) max_h

private let sum_split_last (f: nat -> nat) (max_h: nat{max_h > 0})
  : Lemma (ensures sum_from_to f 0 max_h = sum_from_to f 0 (max_h - 1) + f max_h)
  = if max_h = 1 then ()
    else sum_split_last_from f 1 max_h

/// Bound on correction: sum_{i=0}^{max_h} 2i = max_h*(max_h+1)
private let rec sum_heapify_ops (max_h: nat)
  : Lemma (ensures sum_from_to (fun i -> max_heapify_ops i) 0 max_h <= max_h * (max_h + 1))
          (decreases max_h)
  = if max_h = 0 then ()
    else begin
      sum_heapify_ops (max_h - 1);
      sum_split_last (fun i -> max_heapify_ops i) max_h
      // sum(0..max_h) = sum(0..max_h-1) + 2*max_h
      // By IH: sum(0..max_h-1) <= (max_h-1)*max_h
      // Total: (max_h-1)*max_h + 2*max_h = max_h^2 + max_h = max_h*(max_h+1)
    end

/// h+1 <= 2^h for all h
private let rec h_le_pow2 (h: nat) : Lemma (ensures h + 1 <= pow2 h) (decreases h) =
  if h = 0 then () else h_le_pow2 (h - 1)

/// h*(h+1) <= 2*2^h
private let rec h_sq_bound (h: nat) : Lemma (ensures h * (h + 1) <= 2 * pow2 h) (decreases h) =
  if h <= 1 then () else begin h_sq_bound (h - 1); h_le_pow2 (h - 1) end

/// log2_floor(n)*(log2_floor(n)+1) <= 2n
private let log2_sq_bound (n: pos) : Lemma (ensures log2_floor n * (log2_floor n + 1) <= 2 * n) =
  h_sq_bound (log2_floor n); log2_floor_lower_bound n

/// CLRS Theorem 6.3: BUILD-MAX-HEAP sum is O(n)
/// Proof: decompose ceil into floor + correction, bound each part
///   floor part: sum n*h/2^h < 2n  (geometric series via weighted_pow2_sum identity)
///   correction: sum 2h = H(H+1) <= 2*2^H <= 2n  (since 2^H <= n)
///   total < 2n + 2n = 4n
let simple_sum_bound (n: pos) (h: nat)
  : Lemma (requires h <= log2_floor n)
          (ensures sum_from_to (fun i -> nodes_at_height n i * max_heapify_ops i) 0 h <= 4 * n)
          (decreases h)
  = sum_bound_decomp n 0 h;
    floor_sum_lt_2n n h;
    sum_heapify_ops h;
    h_sq_bound h;
    log2_floor_lower_bound n;
    // sum ceil*2h <= sum(n*h/2^h) + sum(2h) < 2n + h*(h+1) <= 2n + 2*pow2(h) <= 2n + 2n = 4n
    assert (h * (h + 1) <= 2 * pow2 h);
    pow2_le_compat (log2_floor n) h;
    assert (pow2 h <= pow2 (log2_floor n));
    assert (pow2 (log2_floor n) <= n)

#pop-options

/// First, prove that sum_from_to of operations is bounded by a simpler expression
let sum_height_ops_bound (n: pos) (max_h: nat)
  : Lemma (requires max_h = log2_floor n)
          (ensures sum_from_to (fun h -> nodes_at_height n h * max_heapify_ops h) 0 max_h 
                   <= op_Multiply 4 n)
  = // This is BUILD-MAX-HEAP O(n) theorem from CLRS Theorem 6.3
    simple_sum_bound n max_h

//SNIPPET_START: build_heap_ops_linear
/// BUILD-MAX-HEAP is O(n)
let build_heap_ops_linear (n: pos)
  : Lemma (ensures build_heap_ops n <= 4 * n)
  = sum_height_ops_bound n (log2_floor n)
//SNIPPET_END: build_heap_ops_linear

/// ========================================================================
/// Lemmas about extract-max complexity
/// ========================================================================

/// Extract-max operations are bounded by 2 * n * log2_floor n
let rec extract_max_ops_bound (n: nat)
  : Lemma (ensures extract_max_ops n <= op_Multiply (op_Multiply 2 n) (log2_floor (if n = 0 then 1 else n)))
          (decreases n)
  = if n <= 1 then ()
    else begin
      extract_max_ops_bound (n - 1);
      log2_floor_monotonic (n - 1) n;
      // max_heapify_ops (log2_floor n) = 2 * log2_floor n
      // extract_max_ops (n-1) <= 2 * (n-1) * log2_floor (n-1) <= 2 * (n-1) * log2_floor n
      // So total: 2 * log2_floor n + 2 * (n-1) * log2_floor n = 2 * n * log2_floor n
      ()
    end

/// ========================================================================
/// Main theorem: HEAPSORT is O(n log n)
/// ========================================================================

/// Heapsort operations are bounded by c * n * log2(n) for suitable constant c
let heapsort_ops_bound (n: pos)
  : Lemma (ensures heapsort_ops n <= op_Multiply (op_Multiply 2 n) (1 + log2_floor n) + op_Multiply 4 n)
  = build_heap_ops_linear n;
    extract_max_ops_bound n

//SNIPPET_START: heapsort_ops_simplified
/// Simplified: heapsort does at most c * n * (1 + log n) operations for c = 6
let heapsort_ops_simplified (n: pos)
  : Lemma (ensures heapsort_ops n <= op_Multiply (op_Multiply 6 n) (1 + log2_floor n))
//SNIPPET_END: heapsort_ops_simplified
  = heapsort_ops_bound n;
    // build_heap_ops n <= 4n
    // extract_max_ops n <= 2n * log2_floor n
    // Total: heapsort_ops n <= 2n * (1 + log2_floor n) + 4n
    //                       = 2n + 2n*log2_floor n + 4n
    //                       = 6n + 2n*log2_floor n
    //                       = 2n(3 + log2_floor n)
    // Want to show: 2n(3 + log2_floor n) <= 6n(1 + log2_floor n)
    // Divide by 2n: 3 + log2_floor n <= 3(1 + log2_floor n)
    //               3 + log2_floor n <= 3 + 3*log2_floor n
    //               0 <= 2*log2_floor n
    // This is always true for n >= 1
    ()

/// ========================================================================
/// Additional useful lemmas for practical bounds
/// ========================================================================

/// For practical purposes: heapsort uses at most 2n log n + 4n operations
let heapsort_practical_bound (n: pos)
  : Lemma (ensures heapsort_ops n <= op_Multiply (op_Multiply 2 n) (log2_floor n) + op_Multiply 4 n)
  = build_heap_ops_linear n;
    extract_max_ops_bound n;
    // From build_heap_ops_linear:
    //   build_heap_ops n <= 4n
    // From extract_max_ops_bound:
    //   extract_max_ops n <= 2n * log2_floor n
    // Since heapsort_ops n = build_heap_ops n + extract_max_ops n
    // We have: heapsort_ops n <= 4n + 2n * log2_floor n
    //                        = 2n * log2_floor n + 4n
    // Which is exactly the postcondition
    assert (heapsort_ops n = build_heap_ops n + extract_max_ops n);
    assert (build_heap_ops n <= 4 * n);
    assert (extract_max_ops n <= 2 * n * log2_floor n);
    // The SMT solver should now see: 
    // heapsort_ops n <= (4 * n) + (2 * n * log2_floor n)
    ()

/// Verify the asymptotic behavior: for large n, the n log n term dominates
let heapsort_asymptotic (n: pos{n >= 16})
  : Lemma (ensures heapsort_ops n <= op_Multiply (op_Multiply 3 n) (log2_floor n))
  = heapsort_practical_bound n;
    // From heapsort_practical_bound: heapsort_ops n <= 2n*log2_floor n + 4n
    // Want: 2n*log2_floor n + 4n <= 3n*log2_floor n
    // Equivalently: 4n <= n*log2_floor n
    //               4 <= log2_floor n
    // For n >= 16: log2_floor 16 = 4, so log2_floor n >= 4 by monotonicity
    log2_floor_pow2 4;
    assert (log2_floor 16 = 4);
    log2_floor_monotonic 16 n;
    assert (log2_floor n >= 4);
    // Now 4n <= n * log2_floor n follows since log2_floor n >= 4
    ()

/// ========================================================================
/// Comparison with naive O(n^2) sorting
/// ========================================================================

/// Exponential dominates linear: for k >= 5, 2k + 4 < 2^k
let rec exp_dominates_linear (k: nat{k >= 5})
  : Lemma (ensures 2 * k + 4 < pow2 k)
          (decreases k)
  = if k = 5 then begin
      // Base case: 2*5 + 4 = 14 < 32 = 2^5
      pow2_plus 1 4;
      // 2^5 = 2 * 2^4 = 2 * 16 = 32
      ()
    end
    else begin
      // Inductive case: assume 2*(k-1) + 4 < 2^(k-1)
      exp_dominates_linear (k - 1);
      // We have: 2*(k-1) + 4 < pow2 (k-1)
      //          2*k - 2 + 4 < pow2 (k-1)
      //          2*k + 2 < pow2 (k-1)
      // We want: 2*k + 4 < pow2 k = 2 * pow2 (k-1)
      // From above: 2*k + 2 < pow2 (k-1)
      // So: 2*(2*k + 2) < 2*pow2 (k-1)
      //     4*k + 4 < pow2 k
      // But we need only: 2*k + 4 < pow2 k
      // Since 2*k + 4 < 4*k + 4 (for k >= 1), we're done
      pow2_plus 1 (k - 1);
      // pow2 k = 2 * pow2 (k-1)
      // From IH: 2*(k-1) + 4 < pow2 (k-1)
      // So: 2 * (2*(k-1) + 4) < 2 * pow2 (k-1) = pow2 k
      //     4*k - 4 + 8 < pow2 k
      //     4*k + 4 < pow2 k
      // And clearly: 2*k + 4 < 4*k + 4 for k >= 1
      ()
    end

/// Helper: for n >= 16, 2*log2_floor n + 4 < n
let log_linear_bound (n: pos{n >= 16})
  : Lemma (ensures 2 * log2_floor n + 4 < n)
  = // Strategy: bound log2_floor n and use that pow2 grows exponentially
    
    if n >= 32 then begin
      // For n >= 32: log2_floor n >= 5
      log2_floor_pow2 5;
      log2_floor_monotonic 32 n;
      assert (log2_floor n >= 5);
      // We need: 2*log2_floor n + 4 < n
      // Step 1: By exp_dominates_linear: 2*log2_floor n + 4 < pow2 (log2_floor n)
      exp_dominates_linear (log2_floor n);
      // Step 2: By log2_floor_lower_bound: pow2 (log2_floor n) <= n
      log2_floor_lower_bound n;
      // Therefore: 2*log2_floor n + 4 < pow2 (log2_floor n) <= n
      ()
    end
    else begin
      // For 16 <= n < 32: log2_floor n = 4
      log2_floor_pow2 4;
      log2_floor_monotonic 16 n;
      // log2_floor n >= log2_floor 16 = 4
      log2_floor_pow2 5;
      log2_floor_upper_bound n 4;
      // n < 32 = pow2 5, so log2_floor n <= 4
      // Therefore log2_floor n = 4
      // So: 2*4 + 4 = 12 < 16 <= n ✓
      ()
    end

//SNIPPET_START: heapsort_better_than_quadratic
/// For n >= 11, heapsort beats naive O(n^2) sorting
/// We use the bound: 2n log n + 4n < n^2 (valid when 2*log2_floor n + 4 < n)
let heapsort_better_than_quadratic (n: pos{n >= 11})
  : Lemma (ensures heapsort_ops n < op_Multiply n n)
//SNIPPET_END: heapsort_better_than_quadratic
  = heapsort_practical_bound n;
    // From heapsort_practical_bound: heapsort_ops n <= 2n*log2_floor n + 4n
    // Need to show: 2n*log2_floor n + 4n < n^2
    // Equivalently: 2*log2_floor n + 4 < n (dividing by n)
    if n >= 16 then begin
      log_linear_bound n;
      // We have: 2*log2_floor n + 4 < n
      // Multiply by n: n*(2*log2_floor n + 4) < n*n
      //                2n*log2_floor n + 4n < n^2 ✓
      ()
    end
    else begin
      // For 11 <= n < 16: log2_floor n = 3 for all these values
      log2_floor_monotonic n 15;
      assert_norm (log2_floor 15 = 3);
      log2_floor_upper_bound n 3;
      ()
    end



// ========== Root-bound lemmas for bridging to CostBound module ==========

// For small n, verify computationally
#push-options "--fuel 20 --ifuel 5 --z3rlimit 50 --split_queries always"
private
let build_heap_ops_le_root_bound_small (n: pos)
  : Lemma (requires n < 32)
          (ensures build_heap_ops n <= (n / 2) * 2 * log2_floor n)
  = if n < 16 then () else ()
#pop-options

#push-options "--z3rlimit 10"
let build_heap_ops_le_root_bound (n: pos)
  : Lemma (ensures build_heap_ops n <= (n / 2) * 2 * log2_floor n)
  = if n < 32 then
      build_heap_ops_le_root_bound_small n
    else begin
      build_heap_ops_linear n;
      log2_floor_pow2 5;
      log2_floor_monotonic 32 n;
      assert (log2_floor n >= 5)
    end
#pop-options

let rec extract_max_ops_le_root_bound (n: pos)
  : Lemma (ensures extract_max_ops n <= (n - 1) * 2 * log2_floor n)
          (decreases n)
  = if n = 1 then ()
    else begin
      extract_max_ops_le_root_bound (n - 1);
      log2_floor_monotonic (n - 1) n
    end

// ========== Definition-unfolding lemmas ==========

let max_heapify_ops_def (h: nat) : Lemma (ensures max_heapify_ops h == 2 * h) = ()
let extract_max_ops_base (n: nat{n <= 1}) : Lemma (ensures extract_max_ops n == 0) = ()
let extract_max_ops_step (n: nat{n > 1})
  : Lemma (ensures extract_max_ops n == max_heapify_ops (log2_floor n) + extract_max_ops (n - 1)) = ()
let heapsort_ops_def (n: pos) : Lemma (ensures heapsort_ops n == build_heap_ops n + extract_max_ops n) = ()
