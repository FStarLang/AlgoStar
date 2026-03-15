(*
   CLRS Chapter 9.1: MINIMUM / MAXIMUM — Pure Specification

   Complexity bound predicates for min/max finding.
   Both find_minimum and find_maximum use exactly n-1 comparisons.

   NO admits. NO assumes.
*)
module CLRS.Ch09.MinMax.Spec

//SNIPPET_START: minmax_complexity_bound
/// Unified complexity predicate: exactly n−1 comparisons.
/// Used by both find_minimum and find_maximum (their complexity is identical).
let complexity_bounded_n_minus_1 (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1

/// Backward-compatible aliases
let complexity_bounded_min (cf c0 n: nat) : prop = complexity_bounded_n_minus_1 cf c0 n
let complexity_bounded_max (cf c0 n: nat) : prop = complexity_bounded_n_minus_1 cf c0 n
//SNIPPET_END: minmax_complexity_bound
