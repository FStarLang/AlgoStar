(*
   Extended Euclidean Algorithm — Complexity Interface

   Transparent complexity bound predicate and lemma signature.
   Reuses gcd_steps/num_bits from CLRS.Ch31.GCD.Complexity.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD.Complexity

open FStar.Mul
open CLRS.Ch31.GCD.Complexity

// Transparent so clients can see what the bound actually says
let extended_gcd_complexity_bounded (a b: nat) : prop =
  b > 0 ==> gcd_steps a b <= op_Multiply 2 (num_bits b) + 1

val extended_gcd_complexity (a b: nat)
  : Lemma (ensures extended_gcd_complexity_bounded a b)
