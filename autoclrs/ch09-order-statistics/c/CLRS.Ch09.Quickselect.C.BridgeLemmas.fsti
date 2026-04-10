(*
   Quickselect Bridge Lemmas — connecting c2pulse postconditions
   to the CLRS.Ch09.Quickselect.Impl.fsti spec.

   The c2pulse translation works with Seq.seq (option Int32.t) and proves
   properties via Int32.t comparisons.  The Impl.fsti spec expresses
   permutation, partition_ordered, unchanged_outside, and select_spec over
   Seq.seq int.

   This module bridges the gap:
     1. extract_ints: lifts option Int32.t sequences to int sequences
     2. swap_extract_permutation: a swap at option level implies permutation
        at int level (QSpec.permutation)
     3. unchanged_extract_eq: pointwise equal options give equal extracted ints
     4. no_fabrication_extract: forward surjection at option level
        implies forward surjection at int level
     5. select_correctness_bridge_qs: QSpec.permutation + full ordering
        implies select_spec

   NO admits. NO assumes.
*)
module CLRS.Ch09.Quickselect.C.BridgeLemmas

module Seq  = FStar.Seq
module SeqP = FStar.Seq.Properties
module I32  = FStar.Int32
module QSpec = CLRS.Ch09.Quickselect.Spec
module PSSSpec = CLRS.Ch09.PartialSelectionSort.Spec

/// Predicate: every element in [0, len) is Some
let all_some (#a: Type) (s: Seq.seq (option a)) (len: nat) : prop =
  len <= Seq.length s /\
  (forall (i: nat). i < len ==> Some? (Seq.index s i))

/// Extract int values from an initialized option Int32.t sequence
val extract_ints (s: Seq.seq (option I32.t)) (len: nat{all_some s len})
  : Tot (r: Seq.seq int{Seq.length r == len /\
    (forall (i: nat). i < len ==> Seq.index r i == I32.v (Some?.v (Seq.index s i)))})

/// A swap at the option Int32.t level implies QSpec.permutation at the int level
val swap_extract_permutation
  (s: Seq.seq (option I32.t)) (len: nat) (i j: nat)
  : Lemma
    (requires all_some s len /\ i < len /\ j < len)
    (ensures (
      let s' = Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i) in
      all_some s' len /\
      QSpec.permutation (extract_ints s len) (extract_ints s' len)))

/// Identity: pointwise equal options give equal extracted ints
val unchanged_extract_eq
  (s1 s2: Seq.seq (option I32.t)) (len: nat)
  : Lemma
    (requires all_some s1 len /\ all_some s2 len /\
      (forall (k: nat). k < len ==> Seq.index s1 k == Seq.index s2 k))
    (ensures Seq.equal (extract_ints s1 len) (extract_ints s2 len))

/// Forward surjection at option level implies forward surjection at int level
val no_fabrication_extract
  (s_old s_new: Seq.seq (option I32.t)) (n: nat)
  : Lemma
    (requires all_some s_old n /\ all_some s_new n /\
      (forall (p: nat). p < n ==>
        (exists (m: nat). m < n /\
          I32.v (Some?.v (Seq.index s_new p)) == I32.v (Some?.v (Seq.index s_old m)))))
    (ensures (
      let ints_old = extract_ints s_old n in
      let ints_new = extract_ints s_new n in
      forall (p: nat). p < n ==>
        (exists (m: nat). m < n /\ Seq.index ints_new p == Seq.index ints_old m)))

/// Bridge: QSpec.permutation + full ordering ==> select_spec.
/// Takes unfolded quantifier forms since QSpec definitions are in a
/// #lang-pulse module.
val select_correctness_bridge_qs
  (s0 s_final: Seq.seq int) (k: nat)
  : Lemma
    (requires k < Seq.length s0 /\
              Seq.length s_final == Seq.length s0 /\
              QSpec.permutation s0 s_final /\
              (forall (i: nat). i < k ==>
                Seq.index s_final i <= Seq.index s_final k) /\
              (forall (i: nat). k < i /\ i < Seq.length s_final ==>
                Seq.index s_final k <= Seq.index s_final i))
    (ensures Seq.index s_final k ==
             PSSSpec.select_spec s0 k)
