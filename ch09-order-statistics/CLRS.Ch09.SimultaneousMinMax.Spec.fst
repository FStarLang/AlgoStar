(*
   CLRS Chapter 9.1: Simultaneous Min and Max — Pure Specification

   Result type and complexity bound predicates for simultaneous min/max.
   
   NO admits. NO assumes.
*)
module CLRS.Ch09.SimultaneousMinMax.Spec

noeq
type minmax_result = {
  min_val: int;
  max_val: int;
}

//SNIPPET_START: complexity_bounded_minmax
/// Simple scan: exactly 2(n-1) comparisons
let complexity_bounded_minmax (cf c0 n: nat) : prop =
  n >= 1 /\
  cf >= c0 /\
  cf - c0 == op_Multiply 2 (n - 1)
//SNIPPET_END: complexity_bounded_minmax

//SNIPPET_START: complexity_bounded_minmax_pairs
/// Pair-processing: at most ⌊3n/2⌋ comparisons (expressed without division)
let complexity_bounded_minmax_pairs (cf c0 n: nat) : prop =
  n >= 1 /\
  cf >= c0 /\
  op_Multiply 2 (cf - c0) <= op_Multiply 3 n
//SNIPPET_END: complexity_bounded_minmax_pairs
