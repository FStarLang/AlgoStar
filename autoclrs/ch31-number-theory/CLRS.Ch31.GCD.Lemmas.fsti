(*
   GCD Lemmas — Interface

   Proves that gcd_spec computes the GREATEST common divisor,
   not just a common divisor. Uses Bézout's identity from the
   Extended GCD module.

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Lemmas

open FStar.Math.Euclid
open CLRS.Ch31.GCD.Spec

/// gcd_spec a b is the greatest common divisor:
/// any positive common divisor of a and b divides gcd_spec a b
val gcd_spec_is_greatest (a b: nat) (c: pos)
  : Lemma (requires divides c a /\ divides c b)
          (ensures divides c (gcd_spec a b))
