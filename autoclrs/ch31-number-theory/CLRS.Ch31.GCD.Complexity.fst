(*
   GCD Complexity Analysis — Implementation

   Proves O(log b) bound on Euclid's algorithm using a direct mod-halving
   argument (a % b ≤ a/2), capturing the same O(log b) bound as CLRS
   Theorem 31.11 (Lamé's theorem).

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Complexity

open FStar.Mul
open FStar.Math.Lemmas
open CLRS.Ch31.GCD.Spec

// num_bits is monotone
let rec lemma_num_bits_monotone (a b: nat)
  : Lemma (requires a <= b)
          (ensures num_bits a <= num_bits b)
          (decreases b)
  = if a = 0 then ()
    else if b = 0 then ()
    else lemma_num_bits_monotone (a / 2) (b / 2)

// Halving reduces bits by exactly 1 (for n > 0)
let lemma_num_bits_half (n: nat)
  : Lemma (requires n > 0)
          (ensures num_bits (n / 2) == num_bits n - 1)
  = ()

// Key lemma: a % b ≤ a / 2 when a ≥ b > 0
#push-options "--z3rlimit 20"
let lemma_mod_le_half (a b: nat)
  : Lemma (requires a >= b /\ b > 0)
          (ensures a % b <= a / 2)
  = ()
#pop-options

// Arithmetic helper: if x <= y - 1 then 2x + 3 <= 2y + 1
let lemma_arithmetic_helper (x y: nat)
  : Lemma (requires x <= y - 1 /\ y > 0)
          (ensures (2 + (op_Multiply 2 x) + 1) <= (op_Multiply 2 y + 1))
  = ()

// Transitivity helper: combine IH with arithmetic
let lemma_gcd_steps_bound_step (a b r r2: nat)
  : Lemma (requires b > 0 /\ r2 < b /\
                    gcd_steps a b == 2 + gcd_steps r r2 /\
                    gcd_steps r r2 <= op_Multiply 2 (num_bits r2) + 1 /\
                    num_bits r2 <= num_bits b - 1)
          (ensures gcd_steps a b <= op_Multiply 2 (num_bits b) + 1)
  = lemma_arithmetic_helper (num_bits r2) (num_bits b)

//SNIPPET_START: lemma_gcd_steps_log
// Main theorem: Euclid's algorithm takes at most 2*log2(b) + 1 steps (Lamé's theorem)
#push-options "--z3rlimit 150 --fuel 3 --ifuel 2"
let rec lemma_gcd_steps_log (a b: nat)
  : Lemma (requires b > 0)
          (ensures gcd_steps a b <= op_Multiply 2 (num_bits b) + 1)
          (decreases b)
//SNIPPET_END: lemma_gcd_steps_log
  = let r = a % b in
    if r = 0 then ()
    else (
      let r2 = b % r in
      if r2 = 0 then ()
      else (
        lemma_mod_le_half b r;
        lemma_num_bits_monotone r2 (b / 2);
        lemma_num_bits_half b;
        lemma_gcd_steps_log r r2;
        lemma_gcd_steps_bound_step a b r r2
      )
    )
#pop-options

// O(log min(a,b)) bound: combines the O(log b) bound with commutativity
let gcd_steps_log_min (a b: nat)
  : Lemma (requires a > 0 /\ b > 0)
          (ensures gcd_steps a b <= op_Multiply 2 (num_bits (if a <= b then a else b)) + 2)
  = if a >= b then
      lemma_gcd_steps_log a b
    else (
      FStar.Math.Lemmas.small_mod a b;
      lemma_gcd_steps_log b a
    )
