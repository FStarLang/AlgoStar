(*
   Extended Euclidean Algorithm — Pure Specification

   Defines the EXTENDED-EUCLID algorithm (CLRS p. 937, Alg 31.3):
   Given a and b, computes (d, x, y) such that d = gcd(a, b) and a*x + b*y = d.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD.Spec

open CLRS.Ch31.GCD.Spec

// Uses gcd_spec from CLRS.Ch31.GCD.Spec to avoid duplication
let gcd = gcd_spec

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
