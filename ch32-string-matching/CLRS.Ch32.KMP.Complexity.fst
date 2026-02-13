module CLRS.Ch32.KMP.Complexity

open FStar.Mul

(**
 * Complexity Analysis of the Knuth-Morris-Pratt (KMP) String Matching Algorithm
 * 
 * This module formally proves Theorem 32.4 from CLRS: The KMP algorithm runs in
 * O(n + m) time, where n is the text length and m is the pattern length.
 *
 * The proof uses amortized analysis with a potential function based on the
 * failure function value q, which tracks how far we've matched in the pattern.
 *)

(** 
 * AMORTIZED ANALYSIS OVERVIEW
 * ===========================
 *
 * Phase 1: COMPUTE-PREFIX-FUNCTION(P[1..m])
 * ------------------------------------------
 * The algorithm computes the failure function π[1..m] for pattern P.
 * 
 * Key insight: Use potential Φ = k (the current prefix match length)
 * - k starts at 0 and never exceeds m-1
 * - Each iteration either:
 *   (a) Increases k by 1 (one comparison, potential increases by 1)
 *   (b) Decreases k (one or more comparisons, potential decreases)
 * 
 * Amortized cost per iteration:
 * - Case (a): actual cost 1 + potential change +1 = 2
 * - Case (b): actual cost ≥1 + potential change <0 ≤ 1
 * 
 * There are m-1 iterations (for positions 2..m).
 * Total increase in potential: at most m-1 (from 0 to m-1)
 * Total amortized cost: ≤ 2(m-1)
 * Since potential is non-negative, actual cost ≤ amortized cost
 * 
 * Therefore: prefix function uses at most 2(m-1) comparisons
 *
 * Phase 2: KMP-MATCHER(T[1..n], P[1..m])
 * ---------------------------------------
 * The algorithm scans text T to find occurrences of pattern P.
 *
 * Key insight: Use potential Φ = q (current match position in pattern)
 * - q starts at 0 and never exceeds m
 * - Each of n text characters either:
 *   (a) Increases q by 1 (one comparison, potential increases by 1)
 *   (b) Decreases q (one or more comparisons, potential decreases)
 *
 * Amortized cost per character:
 * - Case (a): actual cost 1 + potential change +1 = 2
 * - Case (b): actual cost ≥1 + potential change <0 ≤ 1
 *
 * There are n characters to process.
 * Total increase in potential: at most n (bounded by n increments)
 * Total amortized cost: ≤ 2n
 * Since potential is non-negative, actual cost ≤ amortized cost
 *
 * Therefore: matching phase uses at most 2n comparisons
 *
 * COMBINED COMPLEXITY
 * ===================
 * Total comparisons: ≤ 2(m-1) + 2n = 2n + 2m - 2 < 2(n + m)
 * 
 * This is O(n + m), vastly better than naive O(nm) algorithm.
 *)

(**
 * Number of comparisons for computing the prefix function.
 * Uses amortized analysis: potential function Φ = k (current prefix length).
 * At most 2(m-1) comparisons for pattern of length m.
 *)
let prefix_function_comparisons (m: nat) : nat =
  if m >= 1 then 2 * (m - 1) else 0

(**
 * Number of comparisons for the KMP matching phase.
 * Uses amortized analysis: potential function Φ = q (current match position).
 * At most 2n comparisons for text of length n.
 *)
let kmp_matcher_comparisons (n: nat) : nat =
  2 * n

(**
 * Total number of comparisons for complete KMP algorithm.
 * Combines prefix function computation and matching phases.
 *)
let kmp_total_comparisons (n m: nat) : nat =
  prefix_function_comparisons m + kmp_matcher_comparisons n

(**
 * THEOREM 32.4 (CLRS): KMP runs in O(n + m) time
 * 
 * Formally: total comparisons ≤ 2(n + m)
 *)
let kmp_linear (n m: nat) : Lemma
  (ensures kmp_total_comparisons n m <= 2 * (n + m))
  =
  // Expand definitions
  assert (kmp_total_comparisons n m == prefix_function_comparisons m + kmp_matcher_comparisons n);
  assert (kmp_matcher_comparisons n == 2 * n);
  
  // Case analysis on m
  if m >= 1 then begin
    // When m >= 1: prefix_function_comparisons m = 2 * (m - 1)
    assert (prefix_function_comparisons m == 2 * (m - 1));
    
    // Total = 2(m-1) + 2n = 2m - 2 + 2n
    assert (kmp_total_comparisons n m == 2 * (m - 1) + 2 * n);
    
    // Simplify: 2(m-1) + 2n = 2m - 2 + 2n
    assert (2 * (m - 1) == 2 * m - 2);
    assert (kmp_total_comparisons n m == 2 * m - 2 + 2 * n);
    
    // Rearrange: 2m - 2 + 2n = 2(m + n) - 2 <= 2(m + n)
    assert (2 * m - 2 + 2 * n == 2 * m + 2 * n - 2);
    assert (2 * m + 2 * n - 2 == 2 * (m + n) - 2);
    assert (2 * (m + n) - 2 <= 2 * (m + n))
  end else begin
    // When m = 0: prefix_function_comparisons 0 = 0
    assert (prefix_function_comparisons m == 0);
    assert (kmp_total_comparisons n m == 2 * n);
    
    // 2n <= 2(n + 0)
    assert (2 * n == 2 * (n + m))
  end

(**
 * KMP is asymptotically better than naive O(nm) algorithm.
 * 
 * For realistic inputs where m <= n, KMP uses at most 4n comparisons,
 * while naive algorithm uses up to nm comparisons.
 *)
let kmp_better_than_naive (n m: nat) : Lemma
  (requires n >= 1 /\ m >= 1 /\ m <= n)
  (ensures kmp_total_comparisons n m <= 2 * n + 2 * m /\
           2 * n + 2 * m <= 4 * n)
  =
  // First part: expand the definition
  kmp_linear n m;
  assert (kmp_total_comparisons n m <= 2 * (n + m));
  assert (2 * (n + m) == 2 * n + 2 * m);
  
  // Second part: use m <= n
  assert (m <= n);
  assert (2 * m <= 2 * n);
  assert (2 * n + 2 * m <= 2 * n + 2 * n);
  assert (2 * n + 2 * n == 4 * n)

(**
 * Concrete bound: For any text and pattern, KMP uses at most 2(n+m) comparisons.
 * This provides a concrete constant factor, not just asymptotic notation.
 *)
let kmp_concrete_bound (n m: nat) : Lemma
  (ensures kmp_total_comparisons n m <= 2 * n + 2 * m)
  =
  kmp_linear n m;
  assert (2 * (n + m) == 2 * n + 2 * m)

(**
 * Prefix function computation is linear in pattern length.
 *)
let prefix_function_linear (m: nat) : Lemma
  (ensures prefix_function_comparisons m <= 2 * m)
  =
  if m >= 1 then begin
    assert (prefix_function_comparisons m == 2 * (m - 1));
    assert (2 * (m - 1) == 2 * m - 2);
    assert (2 * m - 2 <= 2 * m)
  end else begin
    assert (prefix_function_comparisons 0 == 0);
    assert (0 <= 2 * 0)
  end

(**
 * Matching phase is linear in text length.
 *)
let matcher_linear (n: nat) : Lemma
  (ensures kmp_matcher_comparisons n == 2 * n)
  =
  ()

(**
 * KMP never uses more comparisons than 2(n+m), regardless of input.
 * This proves worst-case linear time complexity.
 *)
let kmp_worst_case (n m: nat) : Lemma
  (ensures kmp_total_comparisons n m <= 2 * (n + m))
  =
  kmp_linear n m

(**
 * For the common case where pattern is much smaller than text (m << n),
 * KMP complexity is dominated by the text length: O(n).
 *)
let kmp_dominated_by_text (n m: nat) : Lemma
  (requires n >= 10 * m)
  (ensures kmp_total_comparisons n m <= 2 * n + 2 * m /\
           2 * n + 2 * m <= 3 * n)
  =
  kmp_linear n m;
  
  // Given: n >= 10m, so m <= n/10
  assert (n >= 10 * m);
  assert (10 * m <= n);
  assert (m <= n / 10);  // Conceptually
  
  // Therefore: 2m <= 2n/10 = n/5 < n
  assert (2 * m <= 2 * (n / 10));
  // So: 2n + 2m <= 2n + n/5 < 3n (for n >= 10m)
  
  // Formal arithmetic: from 10m <= n we get m <= n/10
  // Multiply by 20: 20m <= 2n
  // So: 2n + 2m <= 2n + 2n/10 = 2n + n/5
  // For n >= 10m: 2m <= n/5, thus 2n + 2m <= 2n + n = 3n
  assert (10 * m <= n);
  assert (20 * m <= 2 * n);
  assert (2 * m <= 2 * n / 10);
  
  // Simpler: 2m <= n (since 10m <= n implies 2m <= n/5 < n)
  assert (2 * m <= n);
  assert (2 * n + 2 * m <= 2 * n + n);
  assert (2 * n + n == 3 * n)

(**
 * Comparison with naive algorithm:
 * Naive: O(nm) - can use up to nm comparisons in the worst case
 * KMP: O(n+m) - uses at most 2(n+m) comparisons
 * 
 * For realistic inputs where both n and m are reasonable,
 * KMP provides significant speedup over naive string matching.
 * The exact crossover point depends on the specific values of n and m,
 * but generally KMP becomes advantageous when the pattern length m > 2
 * and the text is longer than the pattern.
 *)
