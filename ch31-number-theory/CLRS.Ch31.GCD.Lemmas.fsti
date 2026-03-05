(*
   GCD Lemmas — Interface

   Signatures for divisibility properties of gcd_spec.

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Lemmas

open FStar.Mul
open FStar.Math.Euclid
open CLRS.Ch31.GCD.Spec

// gcd_spec computes the actual greatest common divisor: it divides both inputs
val gcd_spec_divides (a b: nat)
  : Lemma (ensures divides (gcd_spec a b) a /\ divides (gcd_spec a b) b)
