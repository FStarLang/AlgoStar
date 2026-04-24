(*
   Naive String Matching — Complexity Interface (CLRS §32.1)
*)

module CLRS.Ch32.NaiveStringMatch.Complexity


//SNIPPET_START: complexity_bound_naive
/// Complexity bound: cf - c0 <= (n - m + 1) * m
let string_match_complexity_bounded (cf c0 n m: nat) : prop =
  cf >= c0 /\ cf - c0 <= (n - m + 1) * m
//SNIPPET_END: complexity_bound_naive

/// Complexity is quadratic in the worst case
val naive_worst_case_quadratic (n m: nat)
  : Lemma (requires m <= n /\ m >= 1)
          (ensures (n - m + 1) * m <= n * m)

/// Complexity bound implies cf >= c0
val complexity_nonneg (cf c0 n m: nat)
  : Lemma (requires string_match_complexity_bounded cf c0 n m)
          (ensures cf >= c0)
