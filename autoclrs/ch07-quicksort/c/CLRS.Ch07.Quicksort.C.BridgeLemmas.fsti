(*
   Ch07 Quicksort Bridge Lemmas — connecting c2pulse postconditions to F* specs.

   The c2pulse translation works with Seq.seq (option Int32.t) and proves
   properties via adjacent-pair comparisons on Int32.t values.  The F* specs
   (CLRS.Ch07.Partition.Impl, CLRS.Ch07.Quicksort.Impl) express sortedness,
   permutation, and bounds over Seq.seq int using CLRS.Common.SortSpec.

   This module bridges the gap:
     1. extract_ints: lifts option Int32.t sequences to int sequences
     2. adjacent_sorted_implies_sorted: adjacent-pair ⟹ all-pairs (SortSpec.sorted)
     3. swap_extract_permutation: a swap at option level ⟹ SortSpec.permutation
     4. unchanged_extract_eq: pointwise equal options ⟹ equal extracted ints
     5. c_bounds_implies_between_bounds: Int32 bounds ⟹ between_bounds on ints

   NO admits. NO assumes.
*)
module CLRS.Ch07.Quicksort.C.BridgeLemmas

open CLRS.Common.SortSpec
open CLRS.Ch07.Partition.Lemmas
module Seq  = FStar.Seq
module SeqP = FStar.Seq.Properties
module I32  = FStar.Int32

/// Predicate: every element in the prefix [0, len) is Some
let all_some (#a: Type) (s: Seq.seq (option a)) (len: nat) : prop =
  len <= Seq.length s /\
  (forall (i: nat). i < len ==> Some? (Seq.index s i))

/// Extract int values from an initialized option Int32.t sequence
val extract_ints (s: Seq.seq (option I32.t)) (len: nat{all_some s len})
  : Tot (r: Seq.seq int{Seq.length r == len /\
    (forall (i: nat). i < len ==> Seq.index r i == I32.v (Some?.v (Seq.index s i)))})

/// Adjacent-pair sorted (c2pulse formulation) implies SortSpec.sorted
val adjacent_sorted_implies_sorted (s: Seq.seq (option I32.t)) (len: nat)
  : Lemma
    (requires all_some s len /\
      (forall (k: nat). k + 1 < len ==>
        I32.v (Some?.v (Seq.index s k)) <= I32.v (Some?.v (Seq.index s (k + 1)))))
    (ensures sorted (extract_ints s len))

/// A swap at the option Int32.t level implies permutation at the int level
val swap_extract_permutation
  (s: Seq.seq (option I32.t)) (len: nat) (i j: nat)
  : Lemma
    (requires all_some s len /\ i < len /\ j < len)
    (ensures (
      let s' = Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i) in
      all_some s' len /\
      permutation (extract_ints s len) (extract_ints s' len)))

/// Identity: if every element is unchanged, the extracted ints are equal
val unchanged_extract_eq
  (s1 s2: Seq.seq (option I32.t)) (len: nat)
  : Lemma
    (requires all_some s1 len /\ all_some s2 len /\
      (forall (k: nat). k < len ==> Seq.index s1 k == Seq.index s2 k))
    (ensures Seq.equal (extract_ints s1 len) (extract_ints s2 len))

/// Int32 bounds on array elements imply between_bounds on extracted ints
val c_bounds_implies_between_bounds
  (s: Seq.seq (option I32.t)) (len: nat) (lb rb: I32.t)
  : Lemma
    (requires all_some s len /\
      (forall (k: nat). k < len ==>
        I32.v lb <= I32.v (Some?.v (Seq.index s k)) /\
        I32.v (Some?.v (Seq.index s k)) <= I32.v rb))
    (ensures between_bounds (extract_ints s len) (I32.v lb) (I32.v rb))

/// Sorted on a subrange: if a[lo..hi) is adjacent-pair sorted, the extracted
/// slice is SortSpec.sorted
val subrange_sorted_implies_sorted
  (s: Seq.seq (option I32.t)) (lo hi: nat)
  : Lemma
    (requires lo <= hi /\ hi <= Seq.length s /\ all_some s hi /\
      (forall (k: nat). lo <= k /\ k + 1 < hi ==>
        I32.v (Some?.v (Seq.index s k)) <= I32.v (Some?.v (Seq.index s (k + 1)))))
    (ensures sorted (extract_ints (Seq.slice s lo hi) (hi - lo)))
