(*
   CLRS Chapter 7: Partition — Pure Specification

   Defines the predicates used to specify the Lomuto partition algorithm:
   - Partition correctness (elements ≤ pivot / > pivot)
   - Bounds predicates (larger_than, smaller_than, between_bounds)
   - Complexity predicate for exact linear cost

   NO admits. NO assumes.
*)
module CLRS.Ch07.Partition.Spec

open CLRS.Common.SortSpec
module Seq = FStar.Seq

let nat_smaller (n: nat) = i:nat{i < n}

let seq_swap (#a: Type) (s: Seq.seq a) (i j: nat_smaller (Seq.length s)) : GTot _ =
  Seq.swap s j i

let larger_than (s: Seq.seq int) (lb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> lb <= Seq.index s k

let smaller_than (s: Seq.seq int) (rb: int)
  = forall (k: int). 0 <= k /\ k < Seq.length s ==> Seq.index s k <= rb

let between_bounds (s: Seq.seq int) (lb rb: int)
  = larger_than s lb /\ smaller_than s rb

//SNIPPET_START: clrs_partition_pred
let clrs_partition_pred (s:Seq.seq int) (lo:nat) (j:nat) (i_plus_1: nat) (pivot: int)
: prop
= forall (k:nat). {:pattern (Seq.index s k)}
   k < Seq.length s ==> (
    let kk = k + lo in
    (lo <= kk /\ kk < i_plus_1 ==> Seq.index s k <= pivot) /\
    (i_plus_1 <= kk /\ kk < j   ==> Seq.index s k > pivot))
//SNIPPET_END: clrs_partition_pred

// Linear bound: cf - c0 = n (exactly n operations)
let complexity_exact_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n
