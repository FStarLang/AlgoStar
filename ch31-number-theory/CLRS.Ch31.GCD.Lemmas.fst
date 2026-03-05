(*
   GCD Lemmas — Implementation

   Proves divisibility properties of gcd_spec.

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Lemmas

open FStar.Mul
open FStar.Math.Euclid
open FStar.Math.Lemmas
open CLRS.Ch31.GCD.Spec

// gcd_spec computes the actual greatest common divisor
let rec gcd_spec_divides (a b: nat)
  : Lemma (ensures divides (gcd_spec a b) a /\ divides (gcd_spec a b) b)
          (decreases b)
  = if b = 0 then (
      divides_reflexive a;
      divides_0 a
    )
    else (
      gcd_spec_divides b (a % b);
      let d = gcd_spec a b in
      let q = a / b in
      let r = a % b in
      euclidean_division_definition a b;
      divides_mult_right q b d;
      divides_plus (op_Multiply q b) r d
    )
