(*
   Extended Euclidean Algorithm - Verified implementation in F*
   
   Implements CLRS Chapter 31's EXTENDED-EUCLID algorithm:
   Given a and b, computes (d, x, y) such that:
   - d = gcd(a, b)
   - a*x + b*y = d  (Bézout's identity)
   - d divides both a and b
   
   Uses FStar.Math.Euclid for divides relation and properties.
   Complexity: O(log b), same as the basic GCD algorithm (uses gcd_steps from CLRS.Ch31.GCD).
   
   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD

open FStar.Math.Lemmas
open FStar.Mul
open FStar.Math.Euclid
open CLRS.Ch31.GCD

// ========== GCD Definition ==========
// Uses gcd_spec from CLRS.Ch31.GCD to avoid duplication
let gcd = gcd_spec

// ========== Extended GCD Algorithm ==========

//SNIPPET_START: extended_gcd
// The algorithm returns (d, x, y) as a tuple
type extended_gcd_result = (_: nat & _: int & int)

let rec extended_gcd (a b: nat) 
  : Tot extended_gcd_result (decreases b)
  = if b = 0 then
      (| a, 1, 0 |)
    else
      let (| d', x', y' |) = extended_gcd b (a % b) in
      let q = a / b in
      let d = d' in
      let x = y' in
      let y = x' - q * y' in
      (| d, x, y |)
//SNIPPET_END: extended_gcd

// ========== Correctness Proofs ==========

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
      // We know d divides b and (a % b)
      // Need to show d divides a
      // a = (a/b)*b + (a%b) by Euclidean division
      let q = a / b in
      let r = a % b in
      assert (b > 0);
      euclidean_division_definition a b;
      // d divides b and r, so d divides (q*b + r) = a
      divides_mult_right q b d;    // d divides q*b
      divides_plus (q * b) r d;    // d divides (q*b + r)
      ()
    )

//SNIPPET_START: bezout_identity
// Main theorem: Bézout's identity
// This is the key result: a*x + b*y = d where d = gcd(a,b)
let rec bezout_identity (a b: nat)
  : Lemma (ensures (let (| d, x, y |) = extended_gcd a b in
                    a * x + b * y == d))
          (decreases b)
//SNIPPET_END: bezout_identity
  = if b = 0 then ()
    else (
      let (| d', x', y' |) = extended_gcd b (a % b) in
      bezout_identity b (a % b);
      // We know: b * x' + (a % b) * y' == d'
      // The algorithm returns: d = d', x = y', y = x' - (a/b) * y'
      // Need to show: a * y' + b * (x' - (a/b) * y') == d'
      let q = a / b in
      let r = a % b in
      euclidean_division_definition a b;
      assert (a == q * b + r);
      // From IH: b * x' + r * y' == d'
      // Substituting r = a - q*b:
      // b * x' + (a - q*b) * y' == d'
      // b * x' + a * y' - q*b*y' == d'
      // a * y' + b * (x' - q*y') == d'
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
// Any common divisor of a and b divides d
let extended_gcd_is_greatest (a b: nat) (c: pos)
  : Lemma (requires divides c a /\ divides c b)
          (ensures (let (| d, _, _ |) = extended_gcd a b in divides c d))
  = let (| d, x, y |) = extended_gcd a b in
    bezout_identity a b;
    // We have a*x + b*y = d
    // c divides a and b, so c divides any linear combination
    divides_mult_right x a c;    // c divides a*x
    divides_mult_right y b c;    // c divides b*y
    divides_plus (a * x) (b * y) c;  // c divides (a*x + b*y) = d
    ()

// ========== Complete Specification ==========

//SNIPPET_START: extended_gcd_correctness
// Package all properties into one theorem
let extended_gcd_correctness (a b: nat)
  : Lemma (ensures (
      let (| d, x, y |) = extended_gcd a b in
      // Property 1: d is the GCD
      d == gcd a b /\
      // Property 2: Bézout's identity holds
      a * x + b * y == d /\
      // Property 3: d divides both a and b
      divides d a /\ divides d b /\
      // Property 4: d is the greatest (any common divisor divides d)
      (forall (c: pos). divides c a /\ divides c b ==> divides c d)
    ))
//SNIPPET_END: extended_gcd_correctness
  = extended_gcd_computes_gcd a b;
    bezout_identity a b;
    extended_gcd_divides_both a b;
    // For property 4, introduce a lemma helper
    let aux (c: pos) : Lemma (requires divides c a /\ divides c b)
                             (ensures (let (| d, _, _ |) = extended_gcd a b in divides c d))
      = extended_gcd_is_greatest a b c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

// ========== Complexity Analysis ==========

// extended_gcd has the same recursion structure as gcd_spec:
//   both recurse on (b, a%b) with base case b=0.
// Therefore gcd_steps counts the recursive calls of extended_gcd,
// and the O(log b) bound from lemma_gcd_steps_log applies directly.

//SNIPPET_START: extended_gcd_complexity
let extended_gcd_complexity_bounded (a b: nat) : prop =
  b > 0 ==> gcd_steps a b <= op_Multiply 2 (num_bits b) + 1

let extended_gcd_complexity (a b: nat)
  : Lemma (ensures extended_gcd_complexity_bounded a b)
  = if b > 0 then lemma_gcd_steps_log a b
//SNIPPET_END: extended_gcd_complexity

// ========== Example Computations ==========

// Example: extended_gcd(30, 21) should give d=3 with 30*(-2) + 21*3 = 3
let test_extended_gcd_30_21 ()
  : Lemma (ensures (
      let (| d, x, y |) = extended_gcd 30 21 in
      d == 3 /\ 30 * x + 21 * y == 3
    ))
  = extended_gcd_correctness 30 21

// Example: extended_gcd(99, 78) should give d=3
let test_extended_gcd_99_78 ()
  : Lemma (ensures (
      let (| d, x, y |) = extended_gcd 99 78 in
      d == 3 /\ 99 * x + 78 * y == 3
    ))
  = extended_gcd_correctness 99 78
