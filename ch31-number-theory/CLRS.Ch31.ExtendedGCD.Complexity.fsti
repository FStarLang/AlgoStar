(*
   Extended Euclidean Algorithm — Complexity Interface

   Signatures for the complexity bound of the extended GCD algorithm.
   Reuses gcd_steps/num_bits from CLRS.Ch31.GCD.Complexity.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD.Complexity

open FStar.Mul
open CLRS.Ch31.GCD.Complexity

val extended_gcd_complexity_bounded (a b: nat) : prop

val extended_gcd_complexity (a b: nat)
  : Lemma (ensures extended_gcd_complexity_bounded a b)
