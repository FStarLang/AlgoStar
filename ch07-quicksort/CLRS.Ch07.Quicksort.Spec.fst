(*
   CLRS Chapter 7: Quicksort — Pure Specification

   Defines the predicates for quicksort's pre/postconditions:
   - Ghost seq_min / seq_max for computing bounds
   - Quadratic complexity bound predicate
   - Pure pre/postcondition predicates for the recursive algorithm

   NO admits. NO assumes.
*)
module CLRS.Ch07.Quicksort.Spec

open CLRS.Ch07.Partition.Spec
open CLRS.Common.SortSpec
module A = Pulse.Lib.Array
module Seq = FStar.Seq

(** Ghost functions to compute bounds **)

let rec seq_min (s: Seq.seq int) : GTot int (decreases (Seq.length s)) =
  if Seq.length s = 0 then 0
  else if Seq.length s = 1 then Seq.index s 0
  else let h = Seq.index s 0 in
       let t = seq_min (Seq.tail s) in
       if h < t then h else t

let rec seq_max (s: Seq.seq int) : GTot int (decreases (Seq.length s)) =
  if Seq.length s = 0 then 0
  else if Seq.length s = 1 then Seq.index s 0
  else let h = Seq.index s 0 in
       let t = seq_max (Seq.tail s) in
       if h > t then h else t

//SNIPPET_START: complexity_bounded_quadratic
let complexity_bounded_quadratic (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= op_Multiply n (n - 1) / 2
//SNIPPET_END: complexity_bounded_quadratic

unfold
let pure_pre_quicksort (a: A.array int) (lo: nat) (hi:(hi:nat{lo <= hi})) (lb rb: int) (s0: Seq.seq int)
  = hi <= A.length a /\
    between_bounds s0 lb rb /\
    Seq.length s0 = hi - lo /\
    lo <= A.length a /\
    lb <= rb

unfold
let pure_post_quicksort (a: A.array int) (lo: nat) (hi:(hi:nat{lo <= hi})) (lb rb: int) (s0 s: Seq.seq int)
  = hi <= A.length a /\
    Seq.length s0 = hi - lo /\
    Seq.length s = hi - lo /\
    sorted s /\
    between_bounds s lb rb /\
    permutation s0 s
