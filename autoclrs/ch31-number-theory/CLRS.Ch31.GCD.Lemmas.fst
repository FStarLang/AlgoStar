(*
   GCD Lemmas — Implementation

   Proves the "greatest" property of gcd_spec by delegating to
   the Extended GCD correctness theorem (Bézout's identity).

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Lemmas

open FStar.Math.Euclid
open CLRS.Ch31.GCD.Spec
open CLRS.Ch31.ExtendedGCD.Spec
open CLRS.Ch31.ExtendedGCD.Lemmas

/// Proof: extended_gcd_correctness gives us Bézout's identity
/// a*x + b*y = d where d = gcd_spec a b, from which it follows
/// that any common divisor c of a and b also divides d.
let gcd_spec_is_greatest (a b: nat) (c: pos)
  : Lemma (requires divides c a /\ divides c b)
          (ensures divides c (gcd_spec a b))
  = extended_gcd_correctness a b
