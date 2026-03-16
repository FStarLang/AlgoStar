(*
   Extended GCD Complexity — Implementation

   Delegates to lemma_gcd_steps_log since extended_gcd has the same
   recursion structure as gcd_spec.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD.Complexity

open FStar.Mul
open CLRS.Ch31.GCD.Complexity

let extended_gcd_complexity (a b: nat)
  : Lemma (requires b > 0)
          (ensures extended_gcd_complexity_bounded a b)
  = lemma_gcd_steps_log a b
