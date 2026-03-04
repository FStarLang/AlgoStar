(*
   Bridge between CountingSort (Pulse) and RadixSort (pure spec) definitions.

   CountingSort uses:
   - S.sorted: pairwise on seq nat via forall i j
   - S.permutation: SeqP.permutation nat (count-based, implicit length)
   - S.in_range: all elements <= k

   RadixSort.Base uses:
   - sorted: recursive, head <= next
   - sorted_on_digit: digit comparison
   - permutation: explicit length + count-based (own count function)

   This module proves the equivalences for d=0, base=k+1.

   NO admits. NO assumes.
*)

module CLRS.Ch08.RadixSort.Bridge

open FStar.Seq
open FStar.Mul
open FStar.Classical
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = CLRS.Ch08.CountingSort.Spec
module L = CLRS.Ch08.CountingSort.Lemmas
module B = CLRS.Ch08.RadixSort.Base

(* ========== Count equivalence ========== *)

/// SeqP.count and Base.count agree on seq nat
let rec count_equiv (s: seq nat) (x: nat)
  : Lemma (ensures SeqP.count x s == B.count s x)
          (decreases (length s))
  = if length s = 0 then ()
    else count_equiv (tail s) x

(* ========== Permutation bridge ========== *)

/// SeqP.permutation nat implies Base.permutation
let seqp_perm_implies_base_perm (s1 s2: seq nat)
  : Lemma (requires SeqP.permutation nat s1 s2)
          (ensures B.permutation s1 s2)
  = SeqP.perm_len s1 s2;
    let aux (x: nat) : Lemma (B.count s1 x == B.count s2 x)
      = count_equiv s1 x; count_equiv s2 x
    in
    FStar.Classical.forall_intro aux

/// Base.permutation implies SeqP.permutation nat
let base_perm_implies_seqp_perm (s1 s2: seq nat)
  : Lemma (requires B.permutation s1 s2)
          (ensures SeqP.permutation nat s1 s2)
  = let aux (x: nat) : Lemma (SeqP.count x s1 == SeqP.count x s2)
      = count_equiv s1 x; count_equiv s2 x
    in
    FStar.Classical.forall_intro aux

/// S.permutation (opaque SeqP.permutation) implies Base.permutation
let l_perm_implies_base_perm (s1 s2: seq nat)
  : Lemma (requires S.permutation s1 s2)
          (ensures B.permutation s1 s2)
  = reveal_opaque (`%S.permutation) (S.permutation s1 s2);
    seqp_perm_implies_base_perm s1 s2

(* ========== Sorted bridge ========== *)

/// S.sorted on tail — need to shift indices
#push-options "--z3rlimit 40"
let l_sorted_tail (s: seq nat)
  : Lemma (requires S.sorted s /\ length s > 1)
          (ensures S.sorted (tail s))
  = let t = tail s in
    // Each index of tail s equals shifted index of s
    assert (length t == length s - 1);
    assert (forall (k:nat). k < length t ==> index t k == index s (k + 1));
    // Shifted indices in s are still ordered by S.sorted s
    assert (forall (i j:nat). (i+1) <= (j+1) /\ (j+1) < length s ==> index s (i+1) <= index s (j+1));
    assert (S.sorted t)
#pop-options

/// S.sorted (pairwise) implies B.sorted (recursive)
#push-options "--z3rlimit 20"
let rec l_sorted_implies_base_sorted (s: seq nat)
  : Lemma (requires S.sorted s)
          (ensures B.sorted s)
          (decreases (length s))
  = if length s <= 1 then ()
    else (
      l_sorted_tail s;
      l_sorted_implies_base_sorted (tail s)
    )
#pop-options

/// For d=0 and base > max element, digit k 0 base = k
/// so sorted implies sorted_on_digit at d=0
#push-options "--z3rlimit 20"
let digit_zero (k: nat) (base: nat)
  : Lemma (requires base > 0 /\ k < base)
          (ensures B.digit k 0 base == k)
  = B.pow_positive base 0;
    assert (B.pow base 0 == 1);
    FStar.Math.Lemmas.small_mod k base

let rec l_sorted_implies_sorted_on_digit_0 (s: seq nat) (base: nat)
  : Lemma (requires S.sorted s /\ base > 0 /\
                    (forall (i: nat). i < length s ==> index s i < base))
          (ensures B.sorted_on_digit s 0 base)
          (decreases (length s))
  = if length s <= 1 then ()
    else (
      digit_zero (index s 0) base;
      digit_zero (index s 1) base;
      assert (B.digit (index s 0) 0 base <= B.digit (index s 1) 0 base);
      l_sorted_tail s;
      l_sorted_implies_sorted_on_digit_0 (tail s) base
    )
#pop-options

(* ========== Main connection for d=0 ========== *)

/// CountingSort output satisfies RadixSort.Base predicates for d=0
let counting_sort_is_radix_base_sort
  (s_in s_out: seq nat) (k: nat)
  : Lemma (requires S.sorted s_out /\
                    S.permutation s_in s_out /\
                    length s_in == length s_out /\
                    S.in_range s_in k)
          (ensures B.permutation s_in s_out /\
                   B.sorted_on_digit s_out 0 (k + 1))
  = l_perm_implies_base_perm s_in s_out;
    B.permutation_preserves_bounds s_in s_out (k + 1);
    l_sorted_implies_sorted_on_digit_0 s_out (k + 1)

(* ========== Full is_stable_sort_on_digit for d=0 ========== *)

module Stab = CLRS.Ch08.RadixSort.Stability

/// At d=0 with base=k+1, equal digits means equal values.
/// So the stability condition (distinct elements with equal digits preserve order)
/// is vacuously true: equal digit => equal value => contradiction with distinct.
#push-options "--z3rlimit 40"

/// Helper: digit at d=0 is identity for values < base
let digit_zero_all (s: seq nat) (base: nat)
  : Lemma (requires base > 0 /\ (forall (i:nat). i < length s ==> index s i < base))
          (ensures forall (i:nat). i < length s ==> B.digit (index s i) 0 base == index s i)
  = let aux (i: nat{i < length s}) : Lemma (B.digit (index s i) 0 base == index s i)
      = digit_zero (index s i) base
    in
    forall_intro (fun (i: nat{i < length s}) -> aux i)

let counting_sort_is_stable_on_digit_0
  (s_in s_out: seq nat) (k: nat)
  : Lemma (requires S.sorted s_out /\
                    S.permutation s_in s_out /\
                    length s_in == length s_out /\
                    S.in_range s_in k)
          (ensures Stab.is_stable_sort_on_digit s_in s_out 0 (k + 1))
  = counting_sort_is_radix_base_sort s_in s_out k;
    let base = k + 1 in
    B.permutation_preserves_bounds s_in s_out base;
    digit_zero_all s_out base;
    // With digit(x,0,base)=x in context, equal digits => equal values => contradicts <>
    // So the stability forall is vacuously true
    reveal_opaque (`%Stab.is_stable_sort_on_digit) (Stab.is_stable_sort_on_digit s_in s_out 0 base)
#pop-options
