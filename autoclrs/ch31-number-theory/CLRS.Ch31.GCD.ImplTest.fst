(*
   CLRS Chapter 31: GCD — Spec Validation Test

   Adapted from the test methodology in:
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch31-number-theory/

   Tests that the gcd_impl API's postcondition is satisfiable and
   sufficiently precise to determine the output for a concrete input:
     gcd(12, 8) = 4

   What is proven:
   1. The precondition (a > 0 ∨ b > 0) is satisfiable for (12, 8).
   2. The postcondition uniquely determines the result: gcd_spec 12 8 == 4,
      and we can prove SZ.v result == 4 using only the postcondition.
   3. The result is positive (SZ.v result > 0) — directly from postcondition.
   4. The result divides both inputs — directly from postcondition.
   5. The complexity spec gcd_steps 12 8 == 2 can be computed by normalization.
   6. No admits, no assumes.
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

#push-options "--z3rlimit 30 --fuel 8 --ifuel 4"

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
  returns _: unit
  ensures emp
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

  // Cleanup ghost counter
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
}
```

#pop-options
