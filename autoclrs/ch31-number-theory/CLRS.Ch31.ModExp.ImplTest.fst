(*
   CLRS Chapter 31: Modular Exponentiation (R-to-L) — Spec Validation Test

   Adapted from the test methodology in:
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch31-number-theory/

   Tests that the mod_exp_impl API's postcondition is satisfiable and
   sufficiently precise to determine the output for a concrete input:
     2^10 mod 1000 = 24

   What is proven:
   1. The precondition (ghost counter) is trivially satisfiable.
   2. The postcondition uniquely determines the result:
      mod_exp_spec 2 10 1000 == 24, and we can prove result == 24.
   3. The bounds postcondition (0 ≤ result < m) is verified: 0 ≤ 24 < 1000.
   4. No admits, no assumes.
*)
module CLRS.Ch31.ModExp.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.Mul
open CLRS.Ch31.ModExp.Impl
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.ModExp.Complexity

module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 30 --fuel 16 --ifuel 4"

/// Prove the expected output by normalizing the pure spec
let modexp_expected ()
  : Lemma (mod_exp_spec 2 10 1000 == 24)
  = assert_norm (mod_exp_spec 2 10 1000 == 24)

```pulse
(* Test: 2^10 mod 1000 = 24 *)
fn test_mod_exp ()
  requires emp
  returns _: unit
  ensures emp
{
  // Allocate ghost tick counter
  let ctr = GR.alloc #nat 0;

  // Call mod_exp_impl — no special precondition beyond ghost counter
  let result = mod_exp_impl 2 10 1000 ctr;

  // Postcondition gives: result == mod_exp_spec 2 10 1000
  // Normalize spec: mod_exp_spec 2 10 1000 == pow 2 10 % 1000 == 1024 % 1000 == 24
  modexp_expected ();
  assert (pure (result == 24));

  // Bounds from postcondition: 0 ≤ result < 1000
  assert (pure (result >= 0));
  assert (pure (result < 1000));

  // Cleanup ghost counter
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
}
```

#pop-options
