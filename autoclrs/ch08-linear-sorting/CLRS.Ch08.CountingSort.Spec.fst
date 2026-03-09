(*
   Pure F* specification for Counting Sort (CLRS §8.2).

   Core predicates defining what it means for counting sort to be correct:
   - sorted / sorted_prefix: ordering predicates on sequences of nat
   - permutation: count-based permutation (opaque to SMT)
   - in_range: all elements bounded by k

   NO admits. NO assumes.
*)

module CLRS.Ch08.CountingSort.Spec

open FStar.Seq
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

// ========== Core Specification Predicates ==========

//SNIPPET_START: counting_sort_spec_defs
let sorted (s: Seq.seq nat)
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let sorted_prefix (s:Seq.seq nat) (n:nat{n <= Seq.length s}) : prop =
  forall (i j: nat). i <= j /\ j < n ==> Seq.index s i <= Seq.index s j

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq nat) : prop = (SeqP.permutation nat s1 s2)

let in_range (s:Seq.seq nat) (k:nat) : prop =
  forall (i:nat). i < Seq.length s ==> Seq.index s i <= k
//SNIPPET_END: counting_sort_spec_defs
