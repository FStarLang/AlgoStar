(*
   CLRS Chapter 31: Modular Exponentiation (L-to-R) — Spec Validation Test

   Adapted from the test methodology in:
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch31-number-theory/

   Tests that the mod_exp_lr_impl API's postcondition is satisfiable and
   sufficiently precise to determine the output for a concrete input:
     3^5 mod 7 = 5

   What is proven:
   1. The precondition (ghost counter) is trivially satisfiable.
   2. The postcondition uniquely determines the result:
      mod_exp_spec 3 5 7 == 5, and we can prove result == 5.
   3. The bounds postcondition (0 ≤ result < m) is verified: 0 ≤ 5 < 7.
   4. No admits, no assumes.
*)
module CLRS.Ch31.ModExpLR.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.Mul
open CLRS.Ch31.ModExpLR.Impl
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.GCD.Complexity
open CLRS.Ch31.ModExpLR.Complexity

module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 30 --fuel 16 --ifuel 4"

/// Prove the expected output by normalizing the pure spec
let modexplr_expected ()
  : Lemma (mod_exp_spec 3 5 7 == 5)
  = assert_norm (mod_exp_spec 3 5 7 == 5)

```pulse
(* Test: 3^5 mod 7 = 5 *)
fn test_mod_exp_lr ()
  requires emp
  returns _: unit
  ensures emp
{
  // Allocate ghost tick counter
  let ctr = GR.alloc #nat 0;

  // Call mod_exp_lr_impl — no special precondition beyond ghost counter
  let result = mod_exp_lr_impl 3 5 7 ctr;

  // Postcondition gives: result == mod_exp_spec 3 5 7
  // Normalize spec: mod_exp_spec 3 5 7 == pow 3 5 % 7 == 243 % 7 == 5
  modexplr_expected ();
  assert (pure (result == 5));

  // Bounds from postcondition: 0 ≤ result < 7
  assert (pure (result >= 0));
  assert (pure (result < 7));

  // Cleanup ghost counter
  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
}
```

#pop-options
