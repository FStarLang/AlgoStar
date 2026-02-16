module CLRS.Ch02.MergeSort.Complexity

open FStar.Mul

(** 
  Complexity analysis for merge sort from CLRS Chapter 2.
  
  CLRS Theorem 2.3: The MERGE-SORT procedure correctly sorts an array of n elements
  in Θ(n log n) time.
  
  Key insights:
  - MERGE takes Θ(n) time (n comparisons to merge two sorted arrays)
  - MERGE-SORT recurrence: T(n) = 2·T(⌈n/2⌉) + n, T(1) = 0
  - We prove: T(n) ≤ 4n⌈log₂ n⌉ + 4n, which is O(n log n)
  
  The constant 4 is loose but makes the proof straightforward. The asymptotic
  complexity is still Θ(n log n) as stated in CLRS.
**)

/// Ceiling of log base 2
/// log2_ceil(1) = 0, log2_ceil(2) = 1, log2_ceil(3) = 2, log2_ceil(4) = 2, etc.
let rec log2_ceil (n: pos) : nat =
  if n = 1 then 0
  else 1 + log2_ceil ((n + 1) / 2)

/// Ceiling division: ⌈n/2⌉
let ceil_div2 (n: pos) : pos = (n + 1) / 2

//SNIPPET_START: merge_sort_ops
/// The actual recurrence for merge sort operations
/// T(n) = 2·T(⌈n/2⌉) + n for n > 1, T(1) = 0
let rec merge_sort_ops (n: pos) : Tot nat (decreases n)
  = if n = 1 then 0
    else 2 * merge_sort_ops (ceil_div2 n) + n
//SNIPPET_END: merge_sort_ops

/// ========== Properties of ceil_div2 and log2_ceil ==========

/// Helper: ceil_div2 n < n for n > 1
let ceil_div2_decreases (n: pos{n > 1})
  : Lemma (ensures ceil_div2 n < n)
  = ()

/// Lemma: 2 * ceil_div2(n) >= n (ceiling property)
let ceil_div2_lower (n: pos)
  : Lemma (ensures 2 * ceil_div2 n >= n)
  = ()

/// Lemma: 2 * ceil_div2(n) <= n + 1
let ceil_div2_upper (n: pos)
  : Lemma (ensures 2 * ceil_div2 n <= n + 1)
  = ()

/// Key observation: log2_ceil n = 1 + log2_ceil (ceil_div2 n) for n > 1
let log2_ceil_recurrence (n: pos{n > 1})
  : Lemma (ensures log2_ceil n = 1 + log2_ceil (ceil_div2 n))
  = ()

/// Lemma: log2_ceil is bounded by n
let rec log2_ceil_bounded (n: pos)
  : Lemma (ensures log2_ceil n <= n)
          (decreases n)
  = if n = 1 then ()
    else log2_ceil_bounded (ceil_div2 n)

/// ========== Main Theorem: T(n) ≤ 4n⌈log₂ n⌉ + 4n ==========

/// Helper: Establish that log grows much slower than linear
/// For m = ⌈n/2⌉, we have log_m << n, specifically: 4·log_m + 4 ≤ 3n for n ≥ 2
let rec log_linear_bound (n: pos{n > 1})
  : Lemma (ensures (let m = ceil_div2 n in
                    let log_m = log2_ceil m in
                    4 * log_m + 4 <= 3 * n))
          (decreases n)
  = let m = ceil_div2 n in
    let log_m = log2_ceil m in
    if n = 2 then begin
      // n=2: m=1, log_m=0, 4·0+4 = 4 ≤ 6 = 3·2 ✓
      assert (m == 1);
      assert (log_m == 0);
      assert (4 * log_m + 4 == 4);
      assert (3 * n == 6)
    end else if n = 3 then begin
      // n=3: m=2, log_m=1, 4·1+4 = 8 ≤ 9 = 3·3 ✓
      assert (m == 2);
      assert (log_m == 1);
      assert (4 * log_m + 4 == 8);
      assert (3 * n == 9)
    end else begin
      // n ≥ 4: Use induction
      // From recurrence: log_m = log2_ceil(⌈m/2⌉) + 1 when m > 1
      // By IH on m: 4·log2_ceil(⌈m/2⌉) + 4 ≤ 3m
      // So: log2_ceil(⌈m/2⌉) ≤ (3m - 4) / 4 < m (for m ≥ 2)
      // And: log_m = log2_ceil(⌈m/2⌉) + 1 < m + 1
      
      // We need: 4·log_m + 4 ≤ 3n
      // We know: m ≤ (n+1)/2, so 2m ≤ n+1, so m ≤ n/2 + 1/2
      // For n ≥ 4: m ≤ n/2 + 1/2 < n
      
      // By recursive structure: log_m grows as O(log n), specifically ≤ log_2(n)
      // For n ≥ 4, log_2(n) ≤ n/2, so log_m ≤ n/2
      // Thus: 4·log_m + 4 ≤ 4·(n/2) + 4 = 2n + 4 ≤ 3n (for n ≥ 4)
      
      if m > 1 then begin
        log_linear_bound m;
        let m' = ceil_div2 m in
        let log_m' = log2_ceil m' in
        assert (4 * log_m' + 4 <= 3 * m);
        assert (log_m == 1 + log_m')
      end;
      
      // For n ≥ 4, we have m ≥ 2, and by IH: 4·log_m' + 4 ≤ 3m
      // So: 4·(log_m' + 1) + 4 = 4·log_m' + 8 ≤ 3m + 4
      // We need: 3m + 4 ≤ 3n
      // I.e., 3m ≤ 3n - 4
      // Since 2m ≤ n+1, we have 3m ≤ (3/2)·(n+1) = 1.5n + 1.5
      // For n ≥ 4: 1.5n + 1.5 ≤ 3n - 4 ⟺ 5.5 ≤ 1.5n ⟺ n ≥ 3.67 ✓
      
      assert (2 * m <= n + 1);
      ()
    end

/// Helper lemma: The key arithmetic inequality
/// Given: 2m ≤ n+1, log_m ≤ m, and specific bound on log_m
/// Show: 8m·log_m + 8m + n ≤ 4n·log_m + 8n
let arithmetic_step (n: pos{n > 1}) (m: pos) (log_m: nat)
  : Lemma (requires 2 * m <= n + 1 /\ log_m <= m /\ 4 * log_m + 4 <= 3 * n)
          (ensures 8 * m * log_m + 8 * m + n <= 4 * n * log_m + 8 * n)
  = // Factor as: LHS = 8m·(log_m + 1) + n, RHS = 4n·(log_m + 1) + 4n
    
    // From 2m ≤ n+1, we get 8m ≤ 4n + 4
    assert (8 * m <= 4 * n + 4);
    
    // Multiply by (log_m + 1)
    FStar.Math.Lemmas.lemma_mult_le_right (log_m + 1) (8 * m) (4 * n + 4);
    assert (8 * m * (log_m + 1) <= (4 * n + 4) * (log_m + 1));
    
    // Expand RHS
    FStar.Math.Lemmas.distributivity_add_left 4 n 4;
    assert ((4 * n + 4) * (log_m + 1) == 4 * n * (log_m + 1) + 4 * (log_m + 1));
    
    // So: 8m·(log_m+1) ≤ 4n·(log_m+1) + 4·(log_m+1)
    assert (8 * m * (log_m + 1) <= 4 * n * (log_m + 1) + 4 * (log_m + 1));
    
    // Add n to both sides: 8m·(log_m+1) + n ≤ 4n·(log_m+1) + 4·(log_m+1) + n
    assert (8 * m * (log_m + 1) + n <= 4 * n * (log_m + 1) + 4 * (log_m + 1) + n);
    
    // Simplify: 4·(log_m+1) = 4·log_m + 4
    assert (4 * (log_m + 1) == 4 * log_m + 4);
    
    // So: 8m·(log_m+1) + n ≤ 4n·(log_m+1) + 4·log_m + 4 + n
    assert (8 * m * (log_m + 1) + n <= 4 * n * (log_m + 1) + 4 * log_m + 4 + n);
    
    // By hypothesis: 4·log_m + 4 + n ≤ 3n + n = 4n
    assert (4 * log_m + 4 + n <= 3 * n + n);
    assert (4 * log_m + 4 + n <= 4 * n);
    
    // Therefore: 8m·(log_m+1) + n ≤ 4n·(log_m+1) + 4n
    assert (8 * m * (log_m + 1) + n <= 4 * n * (log_m + 1) + 4 * n);
    
    // Expand back to original form
    FStar.Math.Lemmas.distributivity_add_left (8 * m) log_m 1;
    FStar.Math.Lemmas.distributivity_add_left (4 * n) log_m 1;
    
    ()

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"

let rec merge_sort_n_log_n_bound (n: pos)
  : Lemma (ensures merge_sort_ops n <= 4 * n * log2_ceil n + 4 * n)
          (decreases n)
  = if n = 1 then ()
    else begin
      let m = ceil_div2 n in
      let log_m = log2_ceil m in
      let log_n = log2_ceil n in
      
      // Inductive hypothesis
      merge_sort_n_log_n_bound m;
      
      // Establish key properties  
      log2_ceil_recurrence n;
      ceil_div2_upper n;
      log2_ceil_bounded m;
      log_linear_bound n; // Proves 4·log_m + 4 ≤ 3n
      
      // By IH: T(m) ≤ 4m·log_m + 4m
      assert (merge_sort_ops m <= 4 * m * log_m + 4 * m);
      
      // Recurrence: T(n) = 2·T(m) + n
      assert (merge_sort_ops n == 2 * merge_sort_ops m + n);
      
      // So: T(n) ≤ 2·(4m·log_m + 4m) + n = 8m·log_m + 8m + n
      assert (merge_sort_ops n <= 8 * m * log_m + 8 * m + n);
      
      // Log recurrence: log_n = log_m + 1
      assert (log_n == log_m + 1);
      
      // Ceil property: 2m ≤ n+1
      assert (2 * m <= n + 1);
      
      // Bound: log_m ≤ m and 4·log_m + 4 ≤ 3n
      assert (log_m <= m);
      assert (4 * log_m + 4 <= 3 * n);
      
      // Apply arithmetic lemma: 8m·log_m + 8m + n ≤ 4n·log_m + 8n
      arithmetic_step n m log_m;
      assert (8 * m * log_m + 8 * m + n <= 4 * n * log_m + 8 * n);
      
      // RHS = 4n·log_m + 8n = 4n·log_m + 4n + 4n = 4n·(log_m + 1) + 4n = 4n·log_n + 4n
      assert (4 * n * log_m + 8 * n == 4 * n * (log_m + 1) + 4 * n);
      assert (4 * n * (log_m + 1) == 4 * n * log_n);
      assert (4 * n * log_m + 8 * n == 4 * n * log_n + 4 * n);
      
      // Therefore: T(n) ≤ 4n·log_n + 4n
      ()
    end

#pop-options

/// ========== Final Theorem ==========

//SNIPPET_START: merge_sort_bound
/// The closed-form upper bound
let merge_sort_bound (n: pos) : nat = 4 * n * log2_ceil n + 4 * n

/// Final theorem: merge sort is O(n log n)
let merge_sort_is_n_log_n (n: pos)
  : Lemma (ensures merge_sort_ops n <= merge_sort_bound n)
  = merge_sort_n_log_n_bound n
//SNIPPET_END: merge_sort_bound

/// ========== Asymptotic Interpretation ==========

/// The bound 4n⌈log₂ n⌉ + 4n is Θ(n log n):
/// - Dominant term: n⌈log₂ n⌉
/// - Constant factors don't affect asymptotic class
/// - This matches CLRS Theorem 2.3: merge sort is Θ(n log n)

/// For practical interpretation: 
/// - n=100: T(100) ≤ 4·100·7 + 400 = 3,200 comparisons (loose bound)
/// - n=1000: T(1000) ≤ 4·1000·10 + 4000 = 44,000 comparisons
/// - n=1,000,000: T(10^6) ≤ 4·10^6·20 + 4·10^6 = 84,000,000 comparisons
///
/// Note: Actual merge sort typically uses ≈ n⌈log₂ n⌉ comparisons;
/// our bound is deliberately loose for ease of formal proof.
