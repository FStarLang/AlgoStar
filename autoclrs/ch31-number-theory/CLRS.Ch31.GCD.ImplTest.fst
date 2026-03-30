(*
   CLRS Chapter 31: GCD — Spec Validation Test

   Adapted from the test methodology in:
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch31-number-theory/

   Tests that the gcd_impl API's postcondition is satisfiable and
   sufficiently precise to determine the output for a concrete input:
     gcd(12, 8) = 4

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        ✓ gcd_spec 12 8 == 4 normalized
        ✓ SZ.v result == 4 from postcondition
        ✓ result divides both inputs
     2. RUNTIME (computational, survives extraction to C):
        ✓ sz_eq comparison returns bool checked at runtime
        ✓ Returns bool — caller can verify at runtime

   NO admits. NO assumes.
*)
module CLRS.Ch31.GCD.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.SizeT
open FStar.Mul
open FStar.Math.Euclid
open CLRS.Ch31.GCD.Impl
open CLRS.Ch31.GCD.Spec
open CLRS.Ch31.GCD.Complexity

module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

(* SZ.t equality check — computational, survives extraction to C *)
inline_for_extraction
let sz_eq (a b: SZ.t) : (r:bool{r <==> SZ.v a = SZ.v b}) =
  not (a <^ b || b <^ a)

/// Prove the expected output by normalizing the pure spec
let gcd_expected ()
  : Lemma (gcd_spec 12 8 == 4)
  = assert_norm (gcd_spec 12 8 == 4)

/// Prove exact step count by normalization (tests complexity spec precision)
let gcd_steps_expected ()
  : Lemma (gcd_steps 12 8 == 2)
  = assert_norm (gcd_steps 12 8 == 2)

```pulse
(* Test: gcd(12, 8) = 4 *)
fn test_gcd ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // Allocate ghost tick counter
  let ctr = GR.alloc #nat 0;

  // Call gcd_impl — precondition: 12 > 0 ∨ 8 > 0 (trivially true)
  let result = gcd_impl 12sz 8sz ctr;

  // Postcondition gives: SZ.v result == gcd_spec 12 8
  // Normalize spec to determine: gcd_spec 12 8 == 4
  gcd_expected ();
  assert (pure (SZ.v result == 4));

  // Result positivity — directly from strengthened postcondition
  assert (pure (SZ.v result > 0));

  // Divisibility — directly from strengthened postcondition
  assert (pure (divides (SZ.v result) 12));
  assert (pure (divides (SZ.v result) 8));

  // Runtime check (survives extraction to C)
  let pass = sz_eq result 4sz;

  // Cleanup ghost counter
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  pass
}
```
