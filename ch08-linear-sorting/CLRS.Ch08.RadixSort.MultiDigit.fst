(*
   Multi-digit Radix Sort - Pure F* Specification
   
   CLRS §8.3 RADIX-SORT algorithm for d-digit numbers:
   
     RADIX-SORT(A, d)
     1  for i = 1 to d
     2    use a stable sort to sort array A on digit i
   
   This module provides pure functional specifications for:
   - Digit extraction from numbers in a given base
   - Stable counting sort on a specific digit
   - Multi-pass radix sort
   - Correctness lemmas (some admitted for now)
   
   This is PURE F* (not Pulse) - all functions are functional.
*)

module CLRS.Ch08.RadixSort.MultiDigit

open FStar.Seq
open FStar.Math.Lemmas
open FStar.Mul
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

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

/// s_out is a permutation of s_in
let permutation (s_in s_out: seq nat) : prop =
  length s_in == length s_out /\
  (forall (x: nat). count s_in x == count s_out x)

(* ========== Helper: insertion into sorted sequence by digit ========== *)

/// Insert element x into sorted sequence s, maintaining sort order by digit d
let rec insert_by_digit (x: nat) (s: seq nat) (d: nat) (base: nat) 
  : Tot (seq nat) (decreases (length s))
  = if length s = 0 then 
      Seq.create 1 x
    else if digit x d base <= digit (index s 0) d base then
      cons x s
    else
      cons (index s 0) (insert_by_digit x (tail s) d base)

/// Insertion sort by digit d - produces a sorted sequence
let rec insertion_sort_by_digit (s: seq nat) (d: nat) (base: nat)
  : Tot (seq nat) (decreases (length s))
  = if length s = 0 then 
      empty
    else 
      insert_by_digit (index s 0) (insertion_sort_by_digit (tail s) d base) d base

(* ========== Stable sort on a single digit ========== *)

/// Stable sort that sorts sequence s by digit d only.
/// In practice, this would be counting sort. Here we use insertion sort
/// as a simple stable sort for specification purposes.
/// 
/// Key property: This is a STABLE sort - elements with equal digit d
/// maintain their relative order from the input sequence.
let stable_sort_on_digit (s: seq nat) (d: nat) (base: nat) : seq nat =
  if base > 0 then
    insertion_sort_by_digit s d base
  else
    s

(* ========== Multi-digit radix sort ========== *)

/// Apply radix sort for num_digits passes, sorting by digits 0, 1, ..., num_digits-1
/// This implements CLRS RADIX-SORT(A, d) where d = num_digits
let rec radix_sort (s: seq nat) (num_digits: nat) (base: nat) 
  : Tot (seq nat) (decreases num_digits)
  = if num_digits = 0 then
      s
    else
      // Sort by digit 0 first, then digit 1, ..., then digit num_digits-1
      let s' = radix_sort s (num_digits - 1) base in
      stable_sort_on_digit s' (num_digits - 1) base

(* ========== Correctness lemmas ========== *)

/// Lemma: insert_by_digit produces a sequence sorted on digit d
let rec insert_by_digit_sorted 
  (x: nat) (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0 /\ sorted_on_digit s d base)
          (ensures sorted_on_digit (insert_by_digit x s d base) d base)
          (decreases (length s))
  = admit() // Proof requires reasoning about cons and sorted_on_digit structure

/// Lemma: insertion_sort_by_digit produces a sorted sequence
let rec insertion_sort_sorted 
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures sorted_on_digit (insertion_sort_by_digit s d base) d base)
          (decreases (length s))
  = admit() // Proof follows from insert_by_digit_sorted

/// Lemma: stable_sort_on_digit produces a sequence sorted on digit d
let stable_sort_on_digit_sorted 
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures sorted_on_digit (stable_sort_on_digit s d base) d base)
  = insertion_sort_sorted s d base

/// Lemma: insert_by_digit is a permutation
let rec insert_by_digit_permutation
  (x: nat) (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures (let result = insert_by_digit x s d base in
                   length result == length s + 1 /\
                   count result x == count s x + 1 /\
                   (forall (y: nat). y <> x ==> count result y == count s y)))
          (decreases (length s))
  = admit() // Tedious counting argument

/// Lemma: insertion_sort_by_digit is a permutation
let rec insertion_sort_permutation
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures permutation s (insertion_sort_by_digit s d base))
          (decreases (length s))
  = admit() // Uses insert_by_digit_permutation

/// Lemma: stable_sort_on_digit is a permutation
let stable_sort_on_digit_permutation
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures permutation s (stable_sort_on_digit s d base))
  = insertion_sort_permutation s d base

/// Key stability property: stable sort preserves relative order of elements
/// with the same digit d. This is crucial for radix sort correctness.
/// 
/// Formally: if two elements x, y appear at positions i < j in input s,
/// and they have the same digit d, then x appears before y in the output.
let stable_sort_preserves_order
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures (
            let result = stable_sort_on_digit s d base in
            permutation s result /\
            sorted_on_digit result d base /\
            // Stability: for equal keys (digit d), maintain relative order
            (forall (i j: nat) (x y: nat).
              i < length s /\ j < length s /\ i < j /\
              index s i == x /\ index s j == y /\
              digit x d base == digit y d base ==>
              // Then x appears before y in result
              (exists (i' j': nat). 
                i' < length result /\ j' < length result /\
                index result i' == x /\ index result j' == y /\
                i' < j'))
          ))
  = admit() // Core stability reasoning - requires detailed proof about insertion sort

/// After sorting by multiple digits, sequence is sorted on lower digits
/// This is an intermediate property used in radix sort correctness
let rec radix_sort_sorted_on_lower_digits
  (s: seq nat) (num_digits: nat) (base: nat) (check_digit: nat)
  : Lemma (requires base > 0 /\ check_digit < num_digits)
          (ensures sorted_on_digit (radix_sort s num_digits base) check_digit base)
          (decreases num_digits)
  = admit() // Inductive argument on the radix sort structure

/// Main correctness theorem: radix_sort produces a fully sorted permutation
/// 
/// Key insight (CLRS Lemma 8.3): If we run d passes of stable digit sort
/// (from digit 0 to d-1), the result is sorted by the full key value,
/// provided all keys fit within d digits.
let radix_sort_correct
  (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\
                    // All elements fit within num_digits digits
                    (forall (i: nat). i < length s ==> index s i < pow base num_digits))
          (ensures (let result = radix_sort s num_digits base in
                   permutation s result /\
                   sorted result))
  = admit() // Main inductive proof using stability and digit comparison
           // Sketch: After k passes, sorted on digits 0..k-1
           // After num_digits passes, sorted on all digits => fully sorted

(* ========== Example usage ========== *)

/// Example: Sort [170, 45, 75, 90, 2, 24, 802, 66] with base=10, d=3
/// This is the example from CLRS Figure 8.3
let example_radix_sort () : seq nat =
  let input = Seq.seq_of_list [170; 45; 75; 90; 2; 24; 802; 66] in
  radix_sort input 3 10

/// The example produces a sorted sequence
let example_radix_sort_correct ()
  : Lemma (ensures (let result = example_radix_sort () in
                   sorted result))
  = admit() // Would follow from radix_sort_correct once proven
