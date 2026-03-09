(*
   RadixSort Base — Shared definitions for the radix sort proof modules.

   This module extracts common definitions that were previously duplicated
   across RadixSort.Spec, RadixSort.Stability, RadixSort.MultiDigit,
   and RadixSort.FullSort:
     - Power function and helpers (pow, pow_positive, pow_zero, pow_succ, pow_monotonic)
     - Digit extraction (digit, digit_bound)
     - Sorted predicates (sorted, sorted_on_digit)
     - Count-based permutation (count, permutation)
     - Permutation helpers (count_positive_means_appears, element_appears_means_count_positive,
       permutation_transitive, permutation_preserves_bounds)

   NO admits. All proofs are complete.
*)

module CLRS.Ch08.RadixSort.Base

open FStar.Seq
open FStar.Math.Lemmas
open FStar.Mul
open FStar.Classical
module Seq = FStar.Seq

(* ========== Power function ========== *)

let rec pow (base: nat) (exp: nat) : nat =
  if exp = 0 then 1
  else base * pow base (exp - 1)

let rec pow_positive (base: nat) (exp: nat)
  : Lemma (requires base > 0)
          (ensures pow base exp > 0)
          (decreases exp)
  = if exp = 0 then ()
    else pow_positive base (exp - 1)

let pow_zero (base: nat) 
  : Lemma (pow base 0 == 1)
  = ()

let rec pow_succ (base: nat) (d: nat)
  : Lemma (pow base (d + 1) == base * pow base d)
  = if d = 0 then ()
    else pow_succ base (d - 1)

let rec pow_one (exp: nat)
  : Lemma (pow 1 exp == 1)
  = if exp = 0 then () else pow_one (exp - 1)

let rec pow_monotonic (base exp1 exp2: nat)
  : Lemma (requires base >= 2 /\ exp1 <= exp2)
          (ensures pow base exp1 <= pow base exp2)
          (decreases exp2)
  = if exp1 = exp2 then ()
    else if exp1 = 0 then pow_positive base exp2
    else pow_monotonic base exp1 (exp2 - 1)

(* ========== Digit extraction ========== *)

/// Extract the d-th digit of k in the given base.
/// digit k d base = (k / base^d) mod base
let digit (k: nat) (d: nat) (base: nat) : nat =
  if base > 0 then (
    pow_positive base d;
    (k / pow base d) % base
  ) else 0

/// Digit is always less than base
let digit_bound (k d base: nat)
  : Lemma (requires base > 0)
          (ensures digit k d base < base)
  = pow_positive base d;
    lemma_mod_lt (k / pow base d) base

(* ========== Sorted predicates ========== *)

/// A sequence is sorted if each element is <= the next
let rec sorted (s: seq nat) : Tot prop (decreases (length s)) =
  length s <= 1 \/ (index s 0 <= index s 1 /\ sorted (tail s))

/// A sequence is sorted on digit d if comparing only digit d
let rec sorted_on_digit (s: seq nat) (d: nat) (base: nat) : Tot prop (decreases (length s)) =
  base > 0 /\ (
    length s <= 1 \/ 
    (digit (index s 0) d base <= digit (index s 1) d base /\ 
     sorted_on_digit (tail s) d base))

(* ========== Permutation ========== *)

/// Count occurrences of x in sequence
let rec count (s: seq nat) (x: nat) : Tot nat (decreases (length s)) =
  if length s = 0 then 0
  else (if index s 0 = x then 1 else 0) + count (tail s) x

/// s_out is a permutation of s_in (same length and same counts for all values)
let permutation (s_in s_out: seq nat) : prop =
  length s_in == length s_out /\
  (forall (x: nat). count s_in x == count s_out x)

(* ========== Permutation helpers ========== *)

/// If count > 0, the element appears somewhere in the sequence
let rec count_positive_means_appears (s: seq nat) (v: nat)
  : Lemma (requires count s v > 0)
          (ensures (exists (i: nat). i < length s /\ index s i == v))
          (decreases (length s))
  = if length s = 0 then ()
    else if index s 0 = v then ()
    else count_positive_means_appears (tail s) v

/// If an element appears in a sequence, its count is positive
let rec element_appears_means_count_positive (s: seq nat) (i: nat{i < length s})
  : Lemma (ensures count s (index s i) > 0)
          (decreases (length s))
  = if i = 0 then ()
    else element_appears_means_count_positive (tail s) (i - 1)

/// Permutation is transitive
let permutation_transitive (s1 s2 s3: seq nat)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
          (ensures permutation s1 s3)
  = ()

/// Permutation preserves upper bounds on elements
let permutation_preserves_bounds (s_in s_out: seq nat) (bound: nat)
  : Lemma (requires permutation s_in s_out /\
                    (forall (i: nat). i < length s_in ==> index s_in i < bound))
          (ensures (forall (i: nat). i < length s_out ==> index s_out i < bound))
  = let aux (i: nat{i < length s_out}) : Lemma (index s_out i < bound) =
      let v = index s_out i in
      element_appears_means_count_positive s_out i;
      assert (count s_out v > 0);
      assert (count s_in v == count s_out v);
      assert (count s_in v > 0);
      count_positive_means_appears s_in v;
      ()
    in
    Classical.forall_intro aux
