(*
   Merge Sort - Pure specification definitions

   Provides:
   - seq_merge: pure recursive merge of two sorted sequences
   - all_ge: predicate for all elements >= a value
   - ms_cost: comparison cost function bridging to merge_sort_ops
   - merge_complexity_bounded: predicate for merge postcondition
   - sort_complexity_bounded: predicate for sort postcondition
*)
module CLRS.Ch02.MergeSort.Spec

module Seq = FStar.Seq
open CLRS.Common.SortSpec
open CLRS.Ch02.MergeSort.Complexity
open Pulse.Lib.BoundedIntegers

//SNIPPET_START: seq_merge
/// Pure merge of two sorted sequences
let rec seq_merge (s1 s2: Seq.seq int) 
  : Tot (Seq.seq int) (decreases (Seq.length s1 + Seq.length s2))
  = if Seq.length s1 = 0 then s2
    else if Seq.length s2 = 0 then s1
    else let h1 = Seq.head s1 in
         let h2 = Seq.head s2 in
         if h1 <= h2 
         then Seq.cons h1 (seq_merge (Seq.tail s1) s2)
         else Seq.cons h2 (seq_merge s1 (Seq.tail s2))
//SNIPPET_END: seq_merge

/// Predicate: all elements of s are >= v
let all_ge (v: int) (s: Seq.seq int) : prop =
  forall (i: nat). i < Seq.length s ==> v <= Seq.index s i

/// Comparison cost bound: 0 for trivial inputs, merge_sort_ops for n >= 1
let ms_cost (len: int) : nat = if len <= 0 then 0 else merge_sort_ops len

//SNIPPET_START: merge_sort_complexity_defs
/// Complexity bound predicates (avoids BoundedIntegers issues in Pulse ensures)
let merge_complexity_bounded (cf c0: nat) (lo hi: nat) : prop =
  lo <= hi /\ cf >= c0 /\ cf - c0 <= hi - lo

let sort_complexity_bounded (cf c0: nat) (lo hi: nat) : prop =
  lo <= hi /\ cf >= c0 /\ cf - c0 <= ms_cost (hi - lo)
//SNIPPET_END: merge_sort_complexity_defs
