(*
   Extended Euclidean Algorithm — Lemmas Implementation

   Proves correctness of the extended GCD algorithm:
   Bézout's identity, divisibility, greatest-divisor, and combined theorem.
   Includes example computations.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD.Lemmas

open FStar.Math.Lemmas
open FStar.Mul
open FStar.Math.Euclid
open CLRS.Ch31.GCD.Spec
open CLRS.Ch31.ExtendedGCD.Spec

// Lemma: The returned d equals gcd(a, b)
let rec extended_gcd_computes_gcd (a b: nat)
  : Lemma (ensures (let (| d, _, _ |) = extended_gcd a b in d == gcd a b))
          (decreases b)
  = if b = 0 then ()
    else extended_gcd_computes_gcd b (a % b)

// Lemma: d divides both a and b
let rec extended_gcd_divides_both (a b: nat)
  : Lemma (ensures (let (| d, _, _ |) = extended_gcd a b in 
                    divides d a /\ divides d b))
          (decreases b)
  = if b = 0 then (
      divides_reflexive a;
      divides_0 a
    )
    else (
      let (| d, x, y |) = extended_gcd b (a % b) in
      extended_gcd_divides_both b (a % b);
      let q = a / b in
      let r = a % b in
      assert (b > 0);
      euclidean_division_definition a b;
      divides_mult_right q b d;
      divides_plus (q * b) r d;
      ()
    )

//SNIPPET_START: bezout_identity
// Main theorem: Bézout's identity
let rec bezout_identity (a b: nat)
  : Lemma (ensures (let (| d, x, y |) = extended_gcd a b in
                    a * x + b * y == d))
          (decreases b)
//SNIPPET_END: bezout_identity
  = if b = 0 then ()
    else (
      let (| d', x', y' |) = extended_gcd b (a % b) in
      bezout_identity b (a % b);
      let q = a / b in
      let r = a % b in
      euclidean_division_definition a b;
      assert (a == q * b + r);
      assert (a * y' + b * (x' - q * y') == 
              a * y' + b * x' - b * q * y');
      assert (a * y' + b * x' - b * q * y' == 
              a * y' + b * x' - q * b * y');
      assert (b * x' + a * y' - q * b * y' == 
              b * x' + (a - q * b) * y');
      assert (a - q * b == r);
      assert (b * x' + r * y' == d')
    )

// Theorem: d is the greatest common divisor
let extended_gcd_is_greatest (a b: nat) (c: pos)
  : Lemma (requires divides c a /\ divides c b)
          (ensures (let (| d, _, _ |) = extended_gcd a b in divides c d))
  = let (| d, x, y |) = extended_gcd a b in
    bezout_identity a b;
    divides_mult_right x a c;
    divides_mult_right y b c;
    divides_plus (a * x) (b * y) c;
    ()

//SNIPPET_START: extended_gcd_correctness
// Package all properties into one theorem
let extended_gcd_correctness (a b: nat)
  : Lemma (ensures (
      let (| d, x, y |) = extended_gcd a b in
      d == gcd a b /\
      a * x + b * y == d /\
      divides d a /\ divides d b /\
      (forall (c: pos). divides c a /\ divides c b ==> divides c d)
    ))
//SNIPPET_END: extended_gcd_correctness
  = extended_gcd_computes_gcd a b;
    bezout_identity a b;
    extended_gcd_divides_both a b;
    let aux (c: pos) : Lemma (requires divides c a /\ divides c b)
                             (ensures (let (| d, _, _ |) = extended_gcd a b in divides c d))
      = extended_gcd_is_greatest a b c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

// ========== Example Computations ==========

let test_extended_gcd_30_21 ()
  : Lemma (ensures (
      let (| d, x, y |) = extended_gcd 30 21 in
      d == 3 /\ 30 * x + 21 * y == 3
    ))
  = extended_gcd_correctness 30 21

let test_extended_gcd_99_78 ()
  : Lemma (ensures (
      let (| d, x, y |) = extended_gcd 99 78 in
      d == 3 /\ 99 * x + 78 * y == 3
    ))
  = extended_gcd_correctness 99 78
