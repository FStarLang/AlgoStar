(*
   CLRS Chapter 9.2: Quickselect — Complexity Interface

   Worst-case complexity analysis: T(n) = n + T(n-1) solves to O(n²).
*)
module CLRS.Ch09.Quickselect.Complexity


val qs_cost (n: nat) : nat

val qs_bound (n: nat)
  : Lemma (ensures qs_cost n <= n * (n + 1) / 2)

val qs_quadratic (n: nat)
  : Lemma (ensures qs_cost n <= n * n)

val quickselect_worst_case_theorem (n: nat)
  : Lemma (ensures qs_cost n <= n * (n + 1) / 2)

val quickselect_worst_case_quadratic (n: nat)
  : Lemma (ensures qs_cost n <= n * n)

val qs_cost_monotone (a b: nat)
  : Lemma (requires a <= b)
          (ensures qs_cost a <= qs_cost b)

val qs_cost_unfold (m: nat)
  : Lemma (requires m >= 2)
          (ensures qs_cost m == m + qs_cost (m - 1))
