module CLRS.Ch09.Quickselect.Complexity

(*
   Worst-case complexity analysis for quickselect
   Based on CLRS Chapter 9
   
   Key insight: Worst case occurs when partition is most unbalanced,
   i.e., the pivot is always the extreme element (smallest or largest).
   This gives the recurrence: T(n) = n + T(n-1)
   Which solves to: T(n) = n + (n-1) + ... + 2 = n(n+1)/2 - 1 = O(n²)
*)

open FStar.Mul
open CLRS.Common.Complexity

(* Worst-case cost for quickselect
   T(0) = 0, T(1) = 0
   T(n) = n + T(n-1) for worst case (always partition to extreme)
*)
let rec qs_cost (n: nat) : nat =
  if n <= 1 then 0
  else n + qs_cost (n - 1)

(* Prove the tight bound: qs_cost n ≤ n(n+1)/2 *)
let rec qs_bound (n: nat)
  : Lemma (ensures qs_cost n <= n * (n + 1) / 2)
          (decreases n)
  = if n <= 1 then ()
    else qs_bound (n - 1)

(* Prove the O(n²) characterization: qs_cost n ≤ n² *)
let rec qs_quadratic (n: nat)
  : Lemma (ensures qs_cost n <= n * n)
          (decreases n)
  = if n <= 1 then ()
    else qs_quadratic (n - 1)

(* Main theorem: Quickselect has O(n²) worst-case time complexity
   Specifically: T(n) ≤ n(n+1)/2 comparisons in the worst case
*)
let quickselect_worst_case_theorem (n: nat)
  : Lemma (ensures qs_cost n <= n * (n + 1) / 2)
  = qs_bound n

(* Corollary: The worst case is bounded by n² *)
let quickselect_worst_case_quadratic (n: nat)
  : Lemma (ensures qs_cost n <= n * n)
  = qs_quadratic n
