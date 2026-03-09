(*
   Activity Selection — Complexity Interface

   Complexity bound for the greedy activity selection algorithm.
   CLRS §16.1: O(n) for presorted input — exactly n-1 comparisons.
*)
module CLRS.Ch16.ActivitySelection.Complexity

//SNIPPET_START: complexity_bounded_linear
/// Exact complexity: cf - c0 == n - 1 comparisons
let complexity_bounded_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1
//SNIPPET_END: complexity_bounded_linear
