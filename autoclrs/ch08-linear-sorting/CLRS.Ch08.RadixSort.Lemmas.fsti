(*
   RadixSort Lemmas — Interface (CLRS §8.3)

   Public signatures for the key lemma results:
   - CLRS Lemma 8.3 stability proof
   - Inductive radix sort invariant
   - Full correctness (sorted + permutation)

   NO admits. NO assumes.
*)

module CLRS.Ch08.RadixSort.Lemmas

open FStar.Seq
open CLRS.Ch08.RadixSort.Base
module Stab = CLRS.Ch08.RadixSort.Stability

/// CLRS Lemma 8.3: A stable sort on digit d preserves ordering on digits 0..d-1.
val lemma_stable_pass_preserves_ordering
  (s_in s_out: seq nat) (d: nat) (base: nat)
  : Lemma (requires
            base >= 2 /\
            (d = 0 \/ Stab.sorted_up_to_digit s_in (d - 1) base) /\
            Stab.is_stable_sort_on_digit s_in s_out d base)
          (ensures Stab.sorted_up_to_digit s_out d base)

/// Inductive invariant: after d passes, sorted on digits 0..d-1.
val radix_sort_invariant
  (s0: seq nat) (steps: list (seq nat)) (d: nat) (base: nat)
  : Lemma (requires
            base >= 2 /\
            List.Tot.length steps >= d /\
            (forall (step_num: nat). step_num < d ==>
              (let s_in = (if step_num = 0 then s0
                          else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               Stab.is_stable_sort_on_digit s_in s_out step_num base)))
          (ensures d > 0 ==> Stab.sorted_up_to_digit (List.Tot.index steps (d - 1)) (d - 1) base)

/// Full correctness: after bigD passes, output is a sorted permutation.
val radix_sort_fully_sorted
  (s0: seq nat) (steps: list (seq nat)) (bigD: nat) (base: nat)
  : Lemma (requires
            bigD > 0 /\ base >= 2 /\
            (forall (i: nat). i < length s0 ==> index s0 i < pow base bigD) /\
            List.Tot.length steps == bigD /\
            (forall (step_num: nat). step_num < bigD ==>
              (let s_in = (if step_num = 0 then s0
                          else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               Stab.is_stable_sort_on_digit s_in s_out step_num base)))
          (ensures (let s_final = List.Tot.index steps (bigD - 1) in
                    permutation s0 s_final /\ sorted s_final))

/// Simplified corollary with explicit final sequence.
val radix_sort_correct
  (s0 s_final: seq nat) (bigD: nat) (base: nat) (steps: list (seq nat))
  : Lemma (requires
            bigD > 0 /\ base >= 2 /\
            (forall (i: nat). i < length s0 ==> index s0 i < pow base bigD) /\
            List.Tot.length steps == bigD /\
            (forall (step_num: nat). step_num < bigD ==>
              (let s_in = (if step_num = 0 then s0
                          else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               Stab.is_stable_sort_on_digit s_in s_out step_num base)) /\
            s_final == List.Tot.index steps (bigD - 1))
          (ensures permutation s0 s_final /\ sorted s_final)
