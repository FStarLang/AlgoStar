(*
   Radix Sort Complexity Analysis

   CLRS Theorem 8.4: Given n d-digit numbers where each digit can take on
   up to k possible values, RADIX-SORT correctly sorts these numbers in
   Θ(d(n+k)) time if the stable sort it uses takes Θ(n+k) time.

   Proof structure:
   1. Each pass of RadixSort uses counting sort on one digit: Θ(n+k) operations
   2. There are d passes (one per digit position)
   3. Total: d × Θ(n+k) = Θ(d(n+k))

   This module proves:
   - Upper bound: radix_sort_ops(n,d,k) ≤ 2d(n+k) + d
   - Lower bound: radix_sort_ops(n,d,k) ≥ d(n+k)
   - Together these show Θ(d(n+k)) complexity

   NO admits. NO assumes.
*)

module CLRS.Ch08.RadixSort.Complexity

open FStar.Mul
module CS = CLRS.Ch08.CountingSort.Complexity

/// The total number of operations performed by radix sort
/// on an array of n elements with d digits, where each digit has k+1 possible values
///
/// Structure:
/// - d passes through the array (one per digit)
/// - Each pass uses counting sort: 2n + k + 1 operations (from CountingSort.Complexity)
/// Total: d * (2n + k + 1)
let radix_sort_ops (n d k: nat) : nat =
  d * CS.counting_sort_iterations n k

/// Expand the definition for clarity
let radix_sort_ops_explicit (n d k: nat)
  : Lemma (ensures radix_sort_ops n d k == d * (2 * n + k + 1))
  = ()

/// Upper bound: radix sort is O(d(n+k))
/// More precisely: ops ≤ 2d(n+k) + d
///
/// Proof: d * (2n + k + 1) = 2dn + dk + d = 2d(n+k) + d
let radix_sort_upper_bound (n d k: nat)
  : Lemma (ensures radix_sort_ops n d k <= 2 * d * (n + k) + d)
  = // The proof is straightforward algebraic expansion
    // d * (2n + k + 1) = d*2n + d*k + d*1 = 2dn + dk + d
    // = 2d(n+k) + d
    FStar.Math.Lemmas.distributivity_add_left d (2 * n) (k + 1);
    FStar.Math.Lemmas.distributivity_add_left d k 1;
    FStar.Math.Lemmas.distributivity_add_left (2 * d) n k

/// Lower bound: radix sort is Ω(d(n+k))
/// More precisely: ops ≥ d(n+k)
///
/// Proof:
/// - Each pass must examine all n elements: ≥ n operations
/// - Each pass must handle all k+1 buckets: ≥ k+1 operations  
/// - Each pass does at least n + k operations
/// - d passes give d(n+k) operations
let radix_sort_lower_bound (n d k: nat)
  : Lemma (ensures radix_sort_ops n d k >= d * (n + k))
  = // From CountingSort.Complexity, we know:
    CS.counting_sort_lower_bound n k;
    assert (CS.counting_sort_iterations n k >= n + k);
    // Therefore:
    assert (radix_sort_ops n d k == d * CS.counting_sort_iterations n k);
    // Since multiplication preserves ≥ for non-negative numbers:
    assert (radix_sort_ops n d k >= d * (n + k))

/// Combined: radix sort is Θ(d(n+k))
/// Establish both bounds simultaneously
let radix_sort_theta_bound (n d k: nat)
  : Lemma (ensures d * (n + k) <= radix_sort_ops n d k /\
                   radix_sort_ops n d k <= 2 * d * (n + k) + d)
  = radix_sort_lower_bound n d k;
    radix_sort_upper_bound n d k

/// For fixed d and k, radix sort is O(n)
/// This shows that when the number of digits is constant,
/// radix sort achieves linear time complexity
let radix_sort_linear_in_n (n d k: nat)
  : Lemma (ensures radix_sort_ops n d k <= 2 * d * n + d * (k + 1))
  = radix_sort_ops_explicit n d k;
    assert (d * (2 * n + k + 1) == 2 * d * n + d * k + d);
    assert (d * k + d == d * (k + 1))

/// For fixed n and k, radix sort is O(d)
/// This shows that when array size is constant,
/// complexity is linear in the number of digits
let radix_sort_linear_in_d (n d k: nat)
  : Lemma (ensures radix_sort_ops n d k <= d * (2 * n + k + 1))
  = radix_sort_ops_explicit n d k

/// Comparison with comparison-based sorts
/// For d-digit numbers with base k+1, comparison-based sorting requires
/// Ω(n log n) comparisons. Radix sort uses Θ(d(n+k)) operations.
///
/// When is radix sort faster?
/// - If d = O(log n) and k = O(n), then d(n+k) = O(n log n)
/// - If d is constant and k is constant, then d(n+k) = O(n)
///   which beats comparison-based Θ(n log n) for large n
///
/// Example: sorting 32-bit integers
/// - n = 1,000,000 elements
/// - d = 4 digits in base 256 (k = 255)
/// - radix_sort_ops ≈ 4 * (2n + 256) ≈ 8n + 1024 operations
/// - comparison sort ≈ n log n ≈ 20n comparisons for n = 1M
///
/// Radix sort uses about 8n operations vs 20n for comparison sorts!
let radix_sort_beats_comparison (n: nat)
  : Lemma (requires n > 0)
          (ensures (let d = 4 in
                   let k = 255 in
                   // Radix sort for 32-bit integers
                   radix_sort_ops n d k == 8 * n + 1024))
  = let d = 4 in
    let k = 255 in
    radix_sort_ops_explicit n d k

/// Key insight: why d passes suffice
/// Each digit position can be sorted independently using a stable sort.
/// After d passes (from least to most significant digit), the entire
/// number is correctly sorted by the lexicographic ordering of digits,
/// which corresponds to the numeric value ordering.
///
/// This is CLRS Lemma 8.3, proven in RadixSort.Spec module.
///
/// The complexity analysis here shows that this d-pass algorithm
/// achieves O(d(n+k)) time, which is linear in n when d and k are
/// treated as constants.

/// Special case: single digit (d=1) reduces to counting sort
let radix_sort_single_digit (n k: nat)
  : Lemma (ensures radix_sort_ops n 1 k == CS.counting_sort_iterations n k)
  = ()

/// Special case: no digits (d=0) is trivial (no operations needed)
let radix_sort_zero_digits (n k: nat)
  : Lemma (ensures radix_sort_ops n 0 k == 0)
  = ()

/// Linearity in d: doubling digits doubles operations
let radix_sort_double_digits (n d k: nat)
  : Lemma (ensures radix_sort_ops n (2 * d) k == 2 * radix_sort_ops n d k)
  = ()

/// Linearity in n: doubling array size doubles operations (for fixed d, k)
let radix_sort_double_n (n d k: nat)
  : Lemma (ensures radix_sort_ops (2 * n) d k <= 2 * radix_sort_ops n d k + d)
  = radix_sort_ops_explicit n d k;
    radix_sort_ops_explicit (2 * n) d k;
    // radix_sort_ops n d k = d * (2n + k + 1)
    // radix_sort_ops (2n) d k = d * (4n + k + 1)
    //                         = d * (4n + k + 1)
    //                         = 2d * (2n) + d * (k + 1)
    //                         = 2 * (d * (2n + k + 1)) + d * (k + 1) - 2d * (k + 1)
    //                         = 2 * radix_sort_ops n d k - d * (k + 1)
    // Actually, let's just show the bound:
    assert (d * (4 * n + k + 1) == 4 * d * n + d * k + d);
    assert (2 * (d * (2 * n + k + 1)) == 4 * d * n + 2 * d * k + 2 * d);
    // We need: 4dn + dk + d <= 4dn + 2dk + 2d
    // This requires: dk + d <= 2dk + 2d, i.e., 0 <= dk + d, which is true
    ()
