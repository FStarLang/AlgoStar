(*
   Extended Euclidean Algorithm — Complexity Implementation

   extended_gcd has the same recursion structure as gcd_spec:
   both recurse on (b, a%b) with base case b=0.
   Therefore gcd_steps counts the recursive calls of extended_gcd,
   and the O(log b) bound from lemma_gcd_steps_log applies directly.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD.Complexity

open FStar.Mul
open CLRS.Ch31.GCD.Complexity

//SNIPPET_START: extended_gcd_complexity
let extended_gcd_complexity (a b: nat)
  : Lemma (ensures extended_gcd_complexity_bounded a b)
  = if b > 0 then lemma_gcd_steps_log a b
//SNIPPET_END: extended_gcd_complexity
