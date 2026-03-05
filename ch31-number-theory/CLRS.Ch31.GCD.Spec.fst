(*
   GCD Pure Specification

   Defines the pure recursive GCD (Euclid's algorithm, CLRS p. 935, Alg 31.2)
   and basic commutativity property.

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Spec

open FStar.Mul

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
