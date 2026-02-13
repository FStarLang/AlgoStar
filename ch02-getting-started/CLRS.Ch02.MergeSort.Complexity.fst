module CLRS.Ch02.MergeSort.Complexity

open FStar.Mul

(** 
  Complexity analysis for merge sort from CLRS Chapter 2.
  
  Key insights:
  - MERGE takes Θ(n) time (n comparisons)
  - MERGE-SORT recurrence: T(n) = 2·T(⌈n/2⌉) + n, T(1) = 0
  - Upper bound: T(n) ≤ 2·n·⌈log₂ n⌉ (loose but easy to prove)
**)

/// Ceiling of log base 2
/// log2_ceil(1) = 0, log2_ceil(2) = 1, log2_ceil(3) = 2, log2_ceil(4) = 2, etc.
let rec log2_ceil (n: pos) : nat =
  if n = 1 then 0
  else 1 + log2_ceil ((n + 1) / 2)

/// Ceiling division: ⌈n/2⌉
let ceil_div2 (n: pos) : pos = (n + 1) / 2

/// The actual recurrence for merge sort comparisons
let rec merge_sort_comparisons (n: pos) : Tot nat (decreases n)
  = if n = 1 then 0
    else 2 * merge_sort_comparisons (ceil_div2 n) + n

/// The closed-form upper bound
let merge_sort_bound (n: pos) : nat = n * log2_ceil n

/// Lemma: log2_ceil is bounded by n
let rec log2_ceil_bounded (n: pos)
  : Lemma (ensures log2_ceil n <= n)
          (decreases n)
  = if n = 1 then ()
    else log2_ceil_bounded (ceil_div2 n)

/// Key observation: log2_ceil n = 1 + log2_ceil (ceil_div2 n) for n > 1
let log2_ceil_recurrence (n: pos{n > 1})
  : Lemma (ensures log2_ceil n = 1 + log2_ceil (ceil_div2 n))
  = ()

/// Helper: ceil_div2 n < n for n > 1
let ceil_div2_decreases (n: pos{n > 1})
  : Lemma (ensures ceil_div2 n < n)
  = ()

/// Lemma: 2 * ceil_div2(n) >= n
let ceil_div2_lower (n: pos)
  : Lemma (ensures 2 * ceil_div2 n >= n)
  = ()

/// Lemma: 2 * ceil_div2(n) <= n + 1
let ceil_div2_upper (n: pos)
  : Lemma (ensures 2 * ceil_div2 n <= n + 1)
  = ()

/// A simple provable bound: T(n) <= 4n·log(n) + 4n  
/// This is still O(n log n)
let rec merge_sort_4n_logn_bound (n: pos)
  : Lemma (ensures merge_sort_comparisons n <= 4 * n * log2_ceil n + 4 * n)
          (decreases n)
  = if n = 1 then ()
    else begin
      let half = ceil_div2 n in
      merge_sort_4n_logn_bound half;
      log2_ceil_recurrence n;
      ceil_div2_upper n;
      log2_ceil_bounded half;
      ()
    end

/// Final theorem: merge sort is O(n log n)
let merge_sort_is_n_log_n (n: pos)
  : Lemma (ensures merge_sort_comparisons n <= op_Multiply (op_Multiply 4 n) (log2_ceil n + 1))
  = merge_sort_4n_logn_bound n
