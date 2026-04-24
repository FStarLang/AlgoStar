(*
   GCD Complexity Analysis — Interface

   Transparent definitions for step counting and num_bits, plus
   signatures for the O(log b) bound lemmas on Euclid's algorithm.

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Complexity

open CLRS.Ch31.GCD.Spec

//SNIPPET_START: gcd_steps
// Count the number of Euclidean steps (transparent for unfolding)
let rec gcd_steps (a b: nat) : Tot nat (decreases b) =
  if b = 0 then 0
  else 1 + gcd_steps b (a % b)

// Number of bits needed to represent n (transparent for unfolding)
let rec num_bits (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0
  else 1 + num_bits (n / 2)
//SNIPPET_END: gcd_steps

//SNIPPET_START: gcd_complexity_bounded
// Complexity bound predicate (transparent)
let gcd_complexity_bounded (cf c0: nat) (a_init b_init: nat) : prop =
  cf >= c0 /\
  cf - c0 == gcd_steps a_init b_init /\
  (b_init > 0 ==> cf - c0 <= op_Star 2 (num_bits b_init) + 1)
//SNIPPET_END: gcd_complexity_bounded

// num_bits is monotone
val lemma_num_bits_monotone (a b: nat)
  : Lemma (requires a <= b)
          (ensures num_bits a <= num_bits b)

// Halving reduces bits by exactly 1 (for n > 0)
val lemma_num_bits_half (n: nat)
  : Lemma (requires n > 0)
          (ensures num_bits (n / 2) == num_bits n - 1)

// Main theorem: Euclid's algorithm takes at most 2*log2(b) + 1 steps
val lemma_gcd_steps_log (a b: nat)
  : Lemma (requires b > 0)
          (ensures gcd_steps a b <= op_Star 2 (num_bits b) + 1)

// O(log min(a,b)) bound
val gcd_steps_log_min (a b: nat)
  : Lemma (requires a > 0 /\ b > 0)
          (ensures gcd_steps a b <= op_Star 2 (num_bits (if a <= b then a else b)) + 2)
