(*
   GCD Pure Specification

   Defines the pure recursive GCD (Euclid's algorithm, CLRS p. 935, Alg 31.2)
   and proves commutativity and divisibility properties.

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Spec

open FStar.Math.Euclid
open FStar.Math.Lemmas

//SNIPPET_START: gcd_spec
// The pure recursive GCD specification
let rec gcd_spec (a b: nat) : Tot nat (decreases b) =
  if b = 0 then a else gcd_spec b (a % b)
//SNIPPET_END: gcd_spec

// Basic property: GCD is commutative
let rec gcd_spec_comm (a b: nat)
  : Lemma (ensures gcd_spec a b == gcd_spec b a)
          (decreases (a + b))
  = if a = 0 then ()
    else if b = 0 then ()
    else if a >= b then (
      gcd_spec_comm b (a % b);
      assert (gcd_spec a b == gcd_spec b (a % b));
      assert (gcd_spec b a == gcd_spec a (b % a))
    )
    else (
      gcd_spec_comm a (b % a);
      assert (gcd_spec b a == gcd_spec a (b % a));
      assert (gcd_spec a b == gcd_spec b (a % b))
    )

// gcd_spec computes the actual greatest common divisor: it divides both inputs
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
      divides_plus (op_Star q b) r d
    )
