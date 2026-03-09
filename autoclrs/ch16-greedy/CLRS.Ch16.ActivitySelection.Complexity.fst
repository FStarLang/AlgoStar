(*
   Activity Selection — Complexity Module

   Defines the complexity bound for the greedy activity selection algorithm.
   CLRS §16.1: O(n) for presorted input — exactly n-1 comparisons.

   The greedy algorithm scans activities 1..n-1, performing one comparison
   per candidate (checking start[m] >= finish[k]). This gives exactly n-1
   comparisons total.
*)
module CLRS.Ch16.ActivitySelection.Complexity
