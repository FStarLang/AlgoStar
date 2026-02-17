module CLRS.Ch06.Heap.Complexity

/// Complexity analysis for HEAPSORT algorithm from CLRS Chapter 6
/// This module proves the O(n log n) upper bound for heapsort

open FStar.Mul

/// Floor of logarithm base 2
let rec log2_floor (n: pos) : nat =
  if n = 1 then 0 else 1 + log2_floor (n / 2)

/// MAX-HEAPIFY comparisons: at most 2 * log2_floor(heap_size)
/// (2 comparisons per level: find max of {parent, left, right})
let max_heapify_comparisons (heap_size: pos) : nat =
  2 * log2_floor heap_size

/// Extract-max loop: (n-1) calls to MAX-HEAPIFY on decreasing heap sizes
let rec extract_max_comparisons (n: nat) : nat =
  if n <= 1 then 0
  else max_heapify_comparisons n + extract_max_comparisons (n - 1)

//SNIPPET_START: heapsort_comparisons
/// HEAPSORT total comparisons:
/// BUILD-MAX-HEAP: at most 2n comparisons (CLRS Theorem 6.3)
/// Extract-max loop: (n-1) calls to MAX-HEAPIFY
let heapsort_comparisons (n: pos) : nat =
  2 * n + extract_max_comparisons n
//SNIPPET_END: heapsort_comparisons

/// Lemma 1: log2_floor is bounded by n
let rec log2_floor_bound (n: pos)
  : Lemma (ensures log2_floor n < n)
          (decreases n)
  = if n = 1 then () else log2_floor_bound (n / 2)

/// Helper: log2_floor is monotonic
let rec log2_floor_monotonic (m n: pos)
  : Lemma (requires m <= n)
          (ensures log2_floor m <= log2_floor n)
          (decreases n)
  = if m = n then ()
    else if n = 1 then ()
    else if m = 1 then ()
    else begin
      // m <= n and both > 1, so m/2 and n/2 are valid
      assert (m / 2 >= 1);
      assert (n / 2 >= 1);
      assert (m / 2 <= n / 2); // Division preserves order
      log2_floor_monotonic (m / 2) (n / 2);
      // log2_floor (m/2) <= log2_floor (n/2)
      // So 1 + log2_floor (m/2) <= 1 + log2_floor (n/2)
      // i.e., log2_floor m <= log2_floor n
      ()
    end

/// Helper: log2_floor of n/2 is one less than log2_floor n for n > 1
let rec log2_floor_half (n: pos)
  : Lemma (requires n > 1)
          (ensures log2_floor (n / 2) = log2_floor n - 1)
          (decreases n)
  = if n = 2 then ()
    else if n = 3 then ()
    else log2_floor_half (n / 2)

/// Helper: establish a tighter bound for log2_floor
let rec log2_floor_tight (n: pos)
  : Lemma (ensures log2_floor n <= n - 1)
          (decreases n)
  = if n = 1 then ()
    else log2_floor_tight (n / 2)

/// Lemma 2: Extract-max comparisons are bounded by 2 * n * log2_floor n
let rec extract_max_comparisons_bound (n: nat)
  : Lemma (ensures extract_max_comparisons n <= op_Multiply (op_Multiply 2 n) (log2_floor (if n = 0 then 1 else n)))
          (decreases n)
  = if n <= 1 then ()
    else begin
      extract_max_comparisons_bound (n - 1);
      log2_floor_monotonic (n - 1) n;
      log2_floor_tight n;
      // We need to show:
      // max_heapify_comparisons n + extract_max_comparisons (n-1) <= 2 * n * log2_floor n
      // i.e., 2 * log2_floor n + extract_max_comparisons (n-1) <= 2 * n * log2_floor n
      // By IH: extract_max_comparisons (n-1) <= 2 * (n-1) * log2_floor (n-1)
      // Since log2_floor (n-1) <= log2_floor n, we have:
      // extract_max_comparisons (n-1) <= 2 * (n-1) * log2_floor n
      // So: 2 * log2_floor n + 2 * (n-1) * log2_floor n = 2 * log2_floor n * (1 + n - 1) = 2 * n * log2_floor n
      ()
    end

/// Lemma 3: Main theorem - heapsort comparisons are O(n log n)
let heapsort_comparisons_bound (n: pos)
  : Lemma (ensures heapsort_comparisons n <= op_Multiply 2 n + op_Multiply (op_Multiply 2 n) (log2_floor n))
  = extract_max_comparisons_bound n

//SNIPPET_START: heapsort_simplified_bound
/// Simplified bound: heapsort does at most 2n(1 + log2_floor n) comparisons
let heapsort_simplified_bound (n: pos)
  : Lemma (ensures heapsort_comparisons n <= op_Multiply (op_Multiply 2 n) (1 + log2_floor n))
  = heapsort_comparisons_bound n
//SNIPPET_END: heapsort_simplified_bound
