(*
   Extended Euclidean Algorithm — Lemmas Interface

   Signatures for correctness proofs of the extended GCD algorithm:
   Bézout's identity, divisibility, and greatest-divisor property.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD.Lemmas

open FStar.Mul
open FStar.Math.Euclid
open CLRS.Ch31.GCD.Spec
open CLRS.Ch31.ExtendedGCD.Spec

// The returned d equals gcd(a, b)
val extended_gcd_computes_gcd (a b: nat)
  : Lemma (ensures (let (| d, _, _ |) = extended_gcd a b in d == gcd a b))

// d divides both a and b
val extended_gcd_divides_both (a b: nat)
  : Lemma (ensures (let (| d, _, _ |) = extended_gcd a b in 
                    divides d a /\ divides d b))

// Main theorem: Bézout's identity (a*x + b*y = d)
val bezout_identity (a b: nat)
  : Lemma (ensures (let (| d, x, y |) = extended_gcd a b in
                    a * x + b * y == d))

// d is the greatest common divisor: any common divisor of a and b divides d
val extended_gcd_is_greatest (a b: nat) (c: pos)
  : Lemma (requires divides c a /\ divides c b)
          (ensures (let (| d, _, _ |) = extended_gcd a b in divides c d))

// Package all properties into one theorem
val extended_gcd_correctness (a b: nat)
  : Lemma (ensures (
      let (| d, x, y |) = extended_gcd a b in
      d == gcd a b /\
      a * x + b * y == d /\
      divides d a /\ divides d b /\
      (forall (c: pos). divides c a /\ divides c b ==> divides c d)
    ))

/// Coefficient bounds (CLRS Theorem 31.8):
/// When a > 0 and b > 0, the Bézout coefficients satisfy
/// |x| ≤ b/gcd(a,b) and |y| ≤ a/gcd(a,b).
val extended_gcd_coeff_bounds (a b: nat)
  : Lemma (requires a > 0 /\ b > 0)
          (ensures (let (| d, x, y |) = extended_gcd a b in
                    d > 0 /\
                    abs x <= b / d /\
                    abs y <= a / d))
