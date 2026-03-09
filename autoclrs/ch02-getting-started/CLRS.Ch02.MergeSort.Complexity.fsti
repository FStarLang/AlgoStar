(*
   Merge Sort - Complexity interface

   Exposes the O(n log n) bound and supporting definitions.
*)
module CLRS.Ch02.MergeSort.Complexity

open FStar.Mul

/// Ceiling of log base 2
val log2_ceil (n: pos) : nat

/// Ceiling division: ⌈n/2⌉
val ceil_div2 (n: pos) : pos

/// The merge sort recurrence: T(n) = 2·T(⌈n/2⌉) + n for n > 1, T(1) = 0
val merge_sort_ops (n: pos) : nat

/// The closed-form upper bound: 4n⌈log₂ n⌉ + 4n
val merge_sort_bound (n: pos) : nat

/// Final theorem: merge sort is O(n log n)
val merge_sort_is_n_log_n (n: pos)
  : Lemma (ensures merge_sort_ops n <= merge_sort_bound n)

/// merge_sort_ops is monotone: larger inputs have larger costs
val merge_sort_ops_monotone (m n: pos)
  : Lemma (requires m <= n)
          (ensures merge_sort_ops m <= merge_sort_ops n)

/// The split used in the implementation: T(⌊n/2⌋) + T(⌈n/2⌉) + n ≤ T(n)
val merge_sort_ops_split (n: pos{n > 1})
  : Lemma (ensures merge_sort_ops (n / 2) + merge_sort_ops (n - n / 2) + n <= merge_sort_ops n)
