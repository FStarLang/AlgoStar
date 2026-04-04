(*
   Canonical sorting specification definitions for CLRS algorithms.
   
   This module provides the standard definitions of sorted, prefix_sorted,
   and permutation (over int sequences) used across all sorting-related
   chapters: Ch02, Ch06, Ch07, Ch08, Ch09.
   
   NOTE: When using this module from #lang-pulse files that also open
   Pulse.Lib.BoundedIntegers, ensure BoundedIntegers is opened before
   this module so that operator overloads (<=, <, etc.) are consistent.
   
   For algorithms over `seq nat` (e.g., RadixSort), a count-based
   permutation definition is used instead (defined locally in those modules).
*)
module CLRS.Common.SortSpec

module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Classical = FStar.Classical
open Pulse.Lib.BoundedIntegers
// 
//SNIPPET_START: definitions
let sorted (s: Seq.seq int) : prop
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let prefix_sorted (s: Seq.seq int) (k: nat) : prop =
  k <= Seq.length s /\
  (forall (i j: nat). i <= j /\ j < k ==> Seq.index s i <= Seq.index s j)

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)
//SNIPPET_END: definitions

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

let lemma_swap_is_two_upds (s: Seq.seq int) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s /\ i <> j)
          (ensures (let vi = Seq.index s i in
                    let vj = Seq.index s j in
                    let s1 = Seq.upd s i vj in
                    let s2 = Seq.upd s1 j vi in
                    Seq.swap s i j == s2))
  = let vi = Seq.index s i in
    let vj = Seq.index s j in
    let s1 = Seq.upd s i vj in
    let s2 = Seq.upd s1 j vi in
    let sw = Seq.swap s i j in
    let aux (k: nat{k < Seq.length s})
      : Lemma (Seq.index s2 k == Seq.index sw k) = ()
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_elim s2 sw

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
      lemma_swap_is_two_upds s i j;
      if i < j then SeqP.lemma_swap_permutes s i j
      else SeqP.lemma_swap_permutes s j i
    )

let append_permutations (s1 s2 s1' s2': Seq.seq int)
  : Lemma (requires permutation s1 s1' /\ permutation s2 s2')
          (ensures permutation (Seq.append s1 s2) (Seq.append s1' s2'))
  = reveal_opaque (`%permutation) (permutation s1 s1');
    reveal_opaque (`%permutation) (permutation s2 s2');
    reveal_opaque (`%permutation) (permutation (Seq.append s1 s2) (Seq.append s1' s2'));
    SeqP.append_permutations s1 s2 s1' s2'

let singl_sorted (s: Seq.seq int)
  : Lemma (requires Seq.length s <= 1) (ensures sorted s)
  = ()

(* Bridge BoundedIntegers operators in sorted to Prims operators for SMT.
   The new F* encodes typeclass-resolved operators as distinct Z3 symbols
   from Prims built-in operators, preventing quantifier trigger matching.
   Call this lemma before using sorted with explicit Prims operator reasoning. *)
let sorted_as_prims (s: Seq.seq int)
  : Lemma (requires sorted s)
          (ensures forall (i j:nat). Prims.op_LessThanOrEqual i j /\
                                     Prims.op_LessThan j (Seq.length s) ==>
                                     Prims.op_LessThanOrEqual (Seq.index s i) (Seq.index s j))
  = assert_norm (sorted s ==
      (forall (i j: nat). Prims.op_LessThanOrEqual i j /\
                          Prims.op_LessThan j (Seq.length s) ==>
                          Prims.op_LessThanOrEqual (Seq.index s i) (Seq.index s j)))
