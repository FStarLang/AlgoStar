(*
   CLRS Chapter 9.1: MINIMUM / MAXIMUM — Pure Specification

   Complexity bound predicates for min/max finding.
   Both find_minimum and find_maximum use exactly n-1 comparisons.

   NO admits. NO assumes.
*)
module CLRS.Ch09.MinMax.Spec

//SNIPPET_START: minmax_complexity_bound
/// Complexity predicates: exactly n−1 comparisons.
/// Both find_minimum and find_maximum have identical complexity.
let complexity_bounded_min (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1

let complexity_bounded_max (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1

/// Unified name (same predicate, for clients that want a single name).
let complexity_bounded_n_minus_1 (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1
//SNIPPET_END: minmax_complexity_bound
