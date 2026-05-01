(*
   CLRS Chapter 31: Extended GCD — Spec Validation Test

   Tests that the extended_gcd_impl API's postcondition is satisfiable
   and sufficiently precise to determine the output for a concrete input:
     extended_gcd(35, 15) = (5, 1, -2)

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ extended_gcd 35 15 = (5, 1, -2) normalized
        ✓ SZ.v result == 5 from postcondition
        ✓ 35*1 + 15*(-2) == 5 (Bézout's identity)
     2. RUNTIME (computational, survives extraction to C):
        ✓ sz_eq comparison returns bool checked at runtime
        ✓ Returns bool — caller can verify at runtime

   NO admits. NO assumes.
*)
module CLRS.Ch31.ExtendedGCD.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.SizeT
open FStar.Math.Euclid
open CLRS.Ch31.ExtendedGCD.Impl
open CLRS.Ch31.ExtendedGCD.Spec
open CLRS.Ch31.ExtendedGCD.Lemmas
open CLRS.Ch31.GCD.Complexity

module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

(* SZ.t equality check — computational, survives extraction to C *)
inline_for_extraction
let sz_eq (a b: SZ.t) : (r:bool{r <==> SZ.v a = SZ.v b}) =
  not (a <^ b || b <^ a)

/// Prove the expected output by normalizing the pure spec
let egcd_expected ()
  : Lemma (extended_gcd 35 15 == (| 5, 1, -2 |))
  = assert_norm (extended_gcd 35 15 == (| 5, 1, -2 |))

/// Extract the d component
let egcd_d ()
  : Lemma (let (| d, _, _ |) = extended_gcd 35 15 in d == 5)
  = egcd_expected ()

```pulse
(* Test: extended_gcd(35, 15) = (5, 1, -2) — check d = 5 at runtime *)
fn test_extended_gcd ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // Allocate ghost tick counter
  let ctr = GR.alloc #nat 0;

  // Call extended_gcd_impl — precondition: 35 > 0 ∨ 15 > 0 (trivially true)
  let result = extended_gcd_impl 35sz 15sz ctr;

  // Postcondition gives: SZ.v result == d where (d, x, y) = extended_gcd 35 15
  // Normalize spec to determine d == 5
  egcd_d ();
  assert (pure (SZ.v result == 5));

  // Bézout's identity from postcondition: 35*1 + 15*(-2) == 5
  egcd_expected ();
  assert (pure (let (| _, x, y |) = extended_gcd 35 15 in 35 * x + 15 * y == 5));

  // Result positivity
  assert (pure (SZ.v result > 0));

  // Divisibility
  assert (pure (divides (SZ.v result) 35));
  assert (pure (divides (SZ.v result) 15));

  // Runtime check (survives extraction to C)
  let pass = sz_eq result 5sz;

  // Cleanup ghost counter
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  pass
}
```
