(*
   InsertionSort Bridge Lemmas — connecting c2pulse postconditions to F* specs.

   The c2pulse translation proves sortedness using adjacent-pair comparisons
   on Int32.t values in Seq.seq (option Int32.t).  The hand-written F* specs
   (CLRS.Ch02.InsertionSort.Impl) express sortedness and permutation over
   Seq.seq int using CLRS.Common.SortSpec.

   This module bridges the gap:
     1. extract_ints: lifts option Int32.t sequences to int sequences
     2. adjacent_sorted_implies_sorted: adjacent-pair ⟹ all-pairs (SortSpec.sorted)
     3. swap_extract_permutation: a swap at option level ⟹ SortSpec.permutation
     4. isort_frame_implies_permutation: frame preservation through swaps
        implies permutation of the overall result

   NO admits.
*)
module CLRS.Ch02.InsertionSort.C.BridgeLemmas

open CLRS.Common.SortSpec
module Seq  = FStar.Seq
module SeqP = FStar.Seq.Properties
module I32  = FStar.Int32

/// Predicate: every element in the prefix is Some
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
