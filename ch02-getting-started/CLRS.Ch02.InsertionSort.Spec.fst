(*
   Insertion Sort - Pure specification definitions

   Provides:
   - complexity_bounded: predicate bounding comparison count by n*(n-1)/2
*)
module CLRS.Ch02.InsertionSort.Spec

open CLRS.Common.SortSpec

module Seq = FStar.Seq

/// Complexity bound predicate: comparison count is at most n*(n-1)/2
//SNIPPET_START: complexity_bounded
let complexity_bounded (cf c0: nat) (n: nat) : prop =
  cf >= c0 /\
  cf - c0 <= op_Multiply n (n - 1) / 2
//SNIPPET_END: complexity_bounded
