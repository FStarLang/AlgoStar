(*
   CLRS Chapter 9.2: Quickselect — Pure Specification

   The quickselect specification re-uses the selection specification from
   PartialSelectionSort.Spec: select_spec s k = (pure_sort s)[k].

   This module defines the partition-specific predicates used by the
   quickselect implementation.

   NO admits. NO assumes.
*)
module CLRS.Ch09.Quickselect.Spec

open FStar.Seq
module Seq = FStar.Seq

/// Opaque permutation for SMT performance
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)

let permutation_same_length (s1 s2 : Seq.seq int)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]
  = reveal_opaque (`%permutation) (permutation s1 s2);
    Seq.Properties.perm_len s1 s2

let permutation_refl (s: Seq.seq int)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
  = reveal_opaque (`%permutation) (permutation s s)

let compose_permutations (s1 s2 s3: Seq.seq int)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
  = reveal_opaque (`%permutation) (permutation s1 s2);
    reveal_opaque (`%permutation) (permutation s2 s3);
    reveal_opaque (`%permutation) (permutation s1 s3);
    Seq.perm_len s1 s2;
    Seq.perm_len s1 s3;
    Seq.lemma_trans_perm s1 s2 s3 0 (Seq.length s1)

/// Elements outside [lo, hi) are unchanged
let unchanged_outside (s1 s2: Seq.seq int) (lo hi: nat) : prop =
  Seq.length s1 == Seq.length s2 /\
  lo <= hi /\ hi <= Seq.length s1 /\
  (forall (i: nat). i < Seq.length s1 ==>
    (i < lo \/ hi <= i) ==>
    Seq.index s1 i == Seq.index s2 i)

/// Partition ordering property
let partition_ordered (s: Seq.seq int) (lo p hi: nat) : prop =
  lo <= p /\ p < hi /\ hi <= Seq.length s /\
  (forall (idx: nat). idx < Seq.length s ==>
    (lo <= idx /\ idx < p) ==> Seq.index s idx <= Seq.index s p) /\
  (forall (idx: nat). idx < Seq.length s ==>
    (p < idx /\ idx < hi) ==> Seq.index s idx >= Seq.index s p)

/// Swap is a permutation
let swap_is_permutation (s: Seq.seq int) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s)
          (ensures (let s1 = Seq.upd s i (Seq.index s j) in
                    let s2 = Seq.upd s1 j (Seq.index s i) in
                    permutation s s2))
  = let vi = Seq.index s i in
    let vj = Seq.index s j in
    let s1 = Seq.upd s i vj in
    let s2 = Seq.upd s1 j vi in
    reveal_opaque (`%permutation) (permutation s s2);
    if i = j then (
      Seq.lemma_index_upd1 s i vj;
      Seq.lemma_eq_elim s1 s;
      Seq.lemma_index_upd1 s1 j vi;
      Seq.lemma_eq_elim s2 s1
    ) else (
      let sw = Seq.swap s (if i < j then i else j) (if i < j then j else i) in
      let aux (k: nat{k < Seq.length s})
        : Lemma (Seq.index s2 k == Seq.index sw k) = ()
      in
      FStar.Classical.forall_intro aux;
      Seq.lemma_eq_elim s2 sw;
      if i < j then Seq.Properties.lemma_swap_permutes s i j
      else Seq.Properties.lemma_swap_permutes s j i
    )
