module CLRS.Ch07.Quicksort.Complexity

(* 
   Worst-case complexity analysis for quicksort
   Based on CLRS Chapter 7, §7.2
   
   Key insight: Worst case occurs when partition is most unbalanced,
   i.e., when one side has 0 elements and the other has n-1 elements.
   This gives the recurrence: T(n) = T(n-1) + (n-1)
   Which solves to: T(n) = n(n-1)/2 = O(n²)
*)

//SNIPPET_START: worst_case_comparisons
let rec worst_case_comparisons (n: nat) : nat =
  if n <= 1 then 0
  else n - 1 + worst_case_comparisons (n - 1)
//SNIPPET_END: worst_case_comparisons

//SNIPPET_START: worst_case_bound
let rec worst_case_bound (n: nat)
  : Lemma (ensures (op_Multiply 2 (worst_case_comparisons n) == op_Multiply n (n - 1)))
  = if n <= 1 then () 
    else worst_case_bound (n - 1)
//SNIPPET_END: worst_case_bound

(* Simpler bound: worst_case_comparisons n <= n * n
   Useful as a simpler O(n²) bound
*)
let rec worst_case_quadratic_bound (n: nat)
  : Lemma (ensures worst_case_comparisons n <= op_Multiply n n)
  = if n <= 1 then ()
    else (
      worst_case_quadratic_bound (n - 1);
      worst_case_bound n
      // From exact formula: worst_case_comparisons n == n * (n-1) / 2
      // Since n * (n-1) / 2 <= n * n for all n >= 0
    )

(* Maximality: worst-case partition is the most unbalanced.
   For any split k ∈ [0, n-1), total comparisons are bounded by worst_case.
   Key theorem: T(k) + T(n-k-1) ≤ T(n-1), proved by convexity.
*)
let rec sum_of_parts_bound (a b: nat)
  : Lemma (ensures worst_case_comparisons a + worst_case_comparisons b 
                  <= worst_case_comparisons (a + b))
          (decreases a + b)
  = if a = 0 then ()
    else if b = 0 then ()
    else begin
      // worst_case a = (a-1) + worst_case (a-1)
      // worst_case (a+b) = (a+b-1) + worst_case (a+b-1)
      // IH on (a-1, b): worst_case (a-1) + worst_case b <= worst_case (a-1+b)
      sum_of_parts_bound (a - 1) b;
      // worst_case (a-1+b) <= worst_case (a+b-1) by monotonicity (a-1+b = a+b-1)
      // So: worst_case a + worst_case b 
      //   = (a-1) + worst_case (a-1) + worst_case b
      //   <= (a-1) + worst_case (a-1+b)
      //   = (a-1) + worst_case (a+b-1)
      //   <= (a+b-1) + worst_case (a+b-1)   [since a-1 <= a+b-1]
      //   = worst_case (a+b)
      ()
    end

//SNIPPET_START: partition_split_bounded
let partition_split_bounded (n: nat{n > 1}) (k: nat{k < n})
  : Lemma (ensures n - 1 + worst_case_comparisons k + worst_case_comparisons (n - 1 - k) 
                  <= worst_case_comparisons n)
  = sum_of_parts_bound k (n - 1 - k)
//SNIPPET_END: partition_split_bounded

(* Helper lemma: worst_case_comparisons is monotonic *)
let rec worst_case_monotonic (m: nat) (n: nat{m <= n})
  : Lemma 
    (ensures worst_case_comparisons m <= worst_case_comparisons n)
    (decreases n)
  = if m = n then ()
    else if n <= 1 then ()
    else (
      worst_case_monotonic m (n - 1);
      // worst_case_comparisons n = (n-1) + worst_case_comparisons (n-1)
      // worst_case_comparisons m <= worst_case_comparisons (n-1) by IH
      // Therefore worst_case_comparisons m <= worst_case_comparisons n
      ()
    )

(* Main theorem: Quicksort has O(n²) worst-case time complexity
   Specifically: T(n) = n(n-1)/2 comparisons in the worst case
*)
let quicksort_worst_case_theorem (n: nat)
  : Lemma (ensures op_Multiply 2 (worst_case_comparisons n) == op_Multiply n (n - 1))
  = worst_case_bound n

(* Corollary: The worst case is bounded by n² *)
let quicksort_worst_case_quadratic (n: nat)
  : Lemma (ensures worst_case_comparisons n <= op_Multiply n n)
  = worst_case_quadratic_bound n
