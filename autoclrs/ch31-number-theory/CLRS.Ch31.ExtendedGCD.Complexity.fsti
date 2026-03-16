(*
   Extended GCD Complexity — Interface

   The extended Euclidean algorithm has the same recursion structure as
   gcd_spec (both recurse on (b, a % b)), so its step count is gcd_steps
   and the O(log b) bound from Lamé's theorem applies directly.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD.Complexity

open FStar.Mul
open CLRS.Ch31.GCD.Complexity

// Complexity bound for extended_gcd: same as gcd_spec
let extended_gcd_complexity_bounded (a_init b_init: nat) : prop =
  b_init > 0 ==> gcd_steps a_init b_init <= op_Multiply 2 (num_bits b_init) + 1

val extended_gcd_complexity (a b: nat)
  : Lemma (requires b > 0)
          (ensures extended_gcd_complexity_bounded a b)
