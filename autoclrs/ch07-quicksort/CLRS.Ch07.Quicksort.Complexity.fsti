(*
   CLRS Chapter 7: Quicksort — Complexity Signatures

   Interface for the worst-case complexity analysis of quicksort.
   Based on CLRS Chapter 7, §7.2:
   - Worst-case recurrence: T(n) = T(n-1) + (n-1)
   - Closed form: T(n) = n(n-1)/2 = O(n²)
   - Convexity: any partition split is bounded by worst case
   - Monotonicity of worst_case_comparisons
*)
module CLRS.Ch07.Quicksort.Complexity

val worst_case_comparisons (n: nat) : nat

val worst_case_bound (n: nat)
  : Lemma (ensures (op_Multiply 2 (worst_case_comparisons n) == op_Multiply n (n - 1)))

val worst_case_quadratic_bound (n: nat)
  : Lemma (ensures worst_case_comparisons n <= op_Multiply n n)

val sum_of_parts_bound (a b: nat)
  : Lemma (ensures worst_case_comparisons a + worst_case_comparisons b 
                  <= worst_case_comparisons (a + b))

val partition_split_bounded (n: nat{n > 1}) (k: nat{k < n})
  : Lemma (ensures n - 1 + worst_case_comparisons k + worst_case_comparisons (n - 1 - k) 
                  <= worst_case_comparisons n)

val worst_case_monotonic (m: nat) (n: nat{m <= n})
  : Lemma (ensures worst_case_comparisons m <= worst_case_comparisons n)

val quicksort_worst_case_theorem (n: nat)
  : Lemma (ensures op_Multiply 2 (worst_case_comparisons n) == op_Multiply n (n - 1))

val quicksort_worst_case_quadratic (n: nat)
  : Lemma (ensures worst_case_comparisons n <= op_Multiply n n)
