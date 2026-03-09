(*
   Naive String Matching — Complexity (CLRS §32.1)

   Complexity bound definition for the naive string matching algorithm:
   O((n-m+1) * m) comparisons.

   NO admits. NO assumes.
*)

module CLRS.Ch32.NaiveStringMatch.Complexity

open FStar.Mul

(** Lemma: complexity is quadratic in the worst case *)
let naive_worst_case_quadratic (n m: nat) : Lemma
  (requires m <= n /\ m >= 1)
  (ensures (n - m + 1) * m <= n * m)
  = ()

(** Lemma: complexity bound is non-negative *)
let complexity_nonneg (cf c0 n m: nat) : Lemma
  (requires string_match_complexity_bounded cf c0 n m)
  (ensures cf >= c0)
  = ()
